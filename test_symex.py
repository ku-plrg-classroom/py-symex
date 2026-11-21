import unittest

import z3

from syntax import parse
from cfg import build
from interp import run
from symex import (SymState, NotSupported, start, to_z3, transfer,
                   reach_node, returns, paths, reach, target_of)


RUNNING = open("examples/running.py").read()
MAGIC = open("examples/magic.py").read()
LOOP = open("examples/loop.py").read()


def graph(src):
    return build(parse(src))


def edge(g, text):
    """The edge whose command prints as `text`."""
    for e in g.edges:
        if str(e) == text:
            return e
    raise KeyError(text)


def along(g, *texts):
    """The state after taking the edges `texts` in order, from the entry."""
    st = start(g)
    for t in texts:
        st = transfer(st, edge(g, t))
    return st


def same(a, b):
    """The z3 terms a and b are equal for every input."""
    s = z3.Solver()
    s.add(a != b)
    return s.check() == z3.unsat


def holds(pc, cond):
    """The path condition pc says exactly cond."""
    return same(z3.And(*pc) if pc else z3.BoolVal(True), cond)


x, y = z3.Int("x"), z3.Int("y")


def expr(text):
    """The MiniPy expression `text`, parsed."""
    return parse(f"def g(x, y):\n    return {text}\n").ret


# the state at point 6 of the running example: x -> x, y -> y, r -> 1,
# z -> x + y (the symbols for the inputs are named after the parameters)
ST6 = SymState(6, (("x", x), ("y", y), ("r", z3.IntVal(1)), ("z", x + y)),
               (10 < x + y, x < 3))


class TestToZ3(unittest.TestCase):
    def term(self, text):
        return to_z3(expr(text), ST6)

    def test_integer_literal(self):
        self.assertTrue(same(self.term("42"), z3.IntVal(42)))

    def test_boolean_literals(self):
        self.assertTrue(same(self.term("True"), z3.BoolVal(True)))
        self.assertTrue(same(self.term("False"), z3.BoolVal(False)))

    def test_a_parameter_is_its_symbol(self):
        self.assertTrue(same(self.term("x"), x))

    def test_a_variable_holds_a_term(self):
        self.assertTrue(same(self.term("z"), x + y))

    def test_a_variable_holds_a_constant(self):
        self.assertTrue(same(self.term("r"), z3.IntVal(1)))

    def test_addition(self):
        self.assertTrue(same(self.term("x + 1"), x + 1))
        self.assertTrue(same(self.term("z + r"), x + y + 1))

    def test_multiplication(self):
        self.assertTrue(same(self.term("z * y"), (x + y) * y))
        self.assertTrue(same(self.term("r * 2"), z3.IntVal(2)))

    def test_unary_minus(self):
        self.assertTrue(same(self.term("-x"), -x))
        self.assertTrue(same(self.term("x + -y"), x - y))

    def test_nested_arithmetic(self):
        self.assertTrue(same(self.term("(x + 1) * (y + -2)"), (x + 1) * (y - 2)))

    def test_order_comparisons(self):
        self.assertTrue(same(self.term("x < 3"), x < 3))
        self.assertTrue(same(self.term("10 <= z"), 10 <= x + y))

    def test_equality_comparisons(self):
        self.assertTrue(same(self.term("x == y"), x == y))
        self.assertTrue(same(self.term("x != 0"), x != 0))

    def test_not(self):
        self.assertTrue(same(self.term("not x < 3"), z3.Not(x < 3)))

    def test_and_or(self):
        self.assertTrue(same(self.term("x < 3 and 0 < y"), z3.And(x < 3, 0 < y)))
        self.assertTrue(same(self.term("x == 0 or y == 0"), z3.Or(x == 0, y == 0)))

    def test_strings_and_lists_are_not_supported(self):
        for text in ('"abc"', 'x + "abc"', "[1, 2]", "[x, y][0]"):
            with self.subTest(expr=text):
                with self.assertRaises(NotSupported):
                    self.term(text)

    def test_an_undefined_variable_is_an_error(self):
        with self.assertRaises(NameError):
            self.term("w")
        with self.assertRaises(NameError):
            self.term("x + w")


class TestTransfer(unittest.TestCase):
    def test_assignment_holds_a_term(self):
        g = graph(RUNNING)
        st = transfer(start(g), edge(g, "r = 0"))
        self.assertEqual(st.node, edge(g, "r = 0").dst)
        self.assertTrue(same(st.get("r"), z3.IntVal(0)))
        self.assertEqual(st.pc, ())

    def test_assignment_uses_the_current_terms(self):
        g = graph(RUNNING)
        st = along(g, "r = 0", "z = x + y")
        self.assertTrue(same(st.get("z"), x + y))
        self.assertTrue(same(st.get("x"), x))

    def test_assignment_reads_the_old_value(self):
        g = graph("def f(x):\n    x = x + 1\n    x = x * 2\n    return x\n")
        st = along(g, "x = x + 1", "x = x * 2")
        self.assertTrue(same(st.get("x"), (x + 1) * 2))

    def test_assume_adds_to_the_path_condition(self):
        g = graph(RUNNING)
        st = along(g, "r = 0", "z = x + y", "assume(10 < z)")
        self.assertEqual(st.node, edge(g, "assume(10 < z)").dst)
        self.assertTrue(holds(st.pc, 10 < x + y))
        self.assertTrue(same(st.get("z"), x + y))

    def test_assumes_accumulate(self):
        g = graph(RUNNING)
        st = along(g, "r = 0", "z = x + y", "assume(10 < z)", "assume(x < 3)")
        self.assertTrue(holds(st.pc, z3.And(10 < x + y, x < 3)))

    def test_negated_condition(self):
        g = graph(RUNNING)
        st = along(g, "r = 0", "z = x + y", "assume(not 10 < z)")
        self.assertEqual(st.node, g.exit)
        self.assertTrue(holds(st.pc, z3.Not(10 < x + y)))

    def test_infeasible_assume_is_none(self):
        g = graph(RUNNING)
        st = along(g, "r = 0", "z = x + y", "assume(10 < z)",
                   "assume(x < 3)", "r = 1")
        self.assertIsNone(transfer(st, edge(g, "assume(y < 8)")))
        self.assertIsNotNone(transfer(st, edge(g, "assume(not y < 8)")))

    def test_pass_only_moves(self):
        g = graph("def f(x):\n    if x < 0:\n        pass\n    return x\n")
        st = along(g, "assume(x < 0)")
        after = transfer(st, edge(g, "pass"))
        self.assertEqual(after.node, g.exit)
        self.assertEqual(after.env, st.env)
        self.assertEqual(after.pc, st.pc)

    def test_a_literal_condition(self):
        g = graph("def f(x):\n    r = 0\n    if True:\n        r = 1\n    return r\n")
        st = along(g, "r = 0")
        self.assertIsNotNone(transfer(st, edge(g, "assume(True)")))
        self.assertIsNone(transfer(st, edge(g, "assume(not True)")))

    def test_assume_reads_the_current_terms(self):
        g = graph("def f(x):\n    x = x + 1\n    if x < 1:\n        x = 0\n    return x\n")
        st = along(g, "x = x + 1", "assume(x < 1)")
        self.assertTrue(holds(st.pc, x + 1 < 1))

    def test_a_boolean_variable(self):
        g = graph("def f(x):\n    b = x < 3\n    if b:\n        x = 0\n    return x\n")
        st = along(g, "b = x < 3")
        self.assertTrue(same(st.get("b"), x < 3))
        self.assertTrue(holds(transfer(st, edge(g, "assume(b)")).pc, x < 3))

    def test_the_old_state_is_unchanged(self):
        g = graph(RUNNING)
        st = along(g, "r = 0", "z = x + y")
        before = (st.node, st.env, st.pc)
        transfer(st, edge(g, "assume(10 < z)"))
        self.assertEqual((st.node, st.env, st.pc), before)


class TestReach(unittest.TestCase):
    def check_runs_to(self, src, text, expected):
        """reach finds an input, and running the program on it returns
        `expected`, which only the line `text` can make it return."""
        m = reach(src, text)
        self.assertIsNotNone(m)
        prog = parse(src)
        self.assertEqual(run(prog, [m[p] for p in prog.params]), expected)

    def test_nested_conditions(self):
        self.check_runs_to(RUNNING, "r = 1", 1)

    def test_infeasible_line(self):
        self.assertIsNone(reach(RUNNING, "r = 2"))

    def test_magic_value(self):
        self.assertEqual(reach(MAGIC, "r = 1"), {"x": 714})

    def test_else_branch(self):
        src = ("def f(x, y):\n    r = 0\n    if x < y:\n        r = 1\n"
               "    else:\n        if x == y + 5:\n            r = 2\n"
               "    return r\n")
        self.check_runs_to(src, "r = 2", 2)

    def test_two_equations(self):
        src = ("def f(x, y):\n    r = 0\n    if x * y == 12 and x + y == 7:\n"
               "        if x < y:\n            r = 1\n    return r\n")
        self.assertEqual(reach(src, "r = 1"), {"x": 3, "y": 4})

    def test_not_and_or(self):
        src = ("def f(x):\n    r = 0\n    if not (x < 5) and (x == 6 or x == 9):\n"
               "        if 7 < x:\n            r = 1\n    return r\n")
        self.assertEqual(reach(src, "r = 1"), {"x": 9})

    def test_unreachable_line(self):
        src = "def f(x):\n    r = 0\n    if x < x:\n        r = 1\n    return r\n"
        self.assertIsNone(reach(src, "r = 1"))

    def test_loop_is_unrolled(self):
        src = ("def f(n):\n    i = 0\n    s = 0\n    r = 0\n"
               "    while i < n:\n        s = s + i\n        i = i + 1\n"
               "    if s == 6:\n        r = 1\n    return r\n")
        self.assertEqual(reach(src, "r = 1"), {"n": 4})

    def test_the_then_branch(self):
        src = ("def f(x, y):\n    r = 0\n    if x < y:\n        r = 1\n"
               "    else:\n        r = 2\n    return r\n")
        self.check_runs_to(src, "r = 1", 1)

    def test_through_a_boolean_variable(self):
        src = ("def f(x, y):\n    r = 0\n    b = x < y\n"
               "    if b and y == 2 * x:\n        if 4 < y:\n            r = 1\n"
               "    return r\n")
        self.check_runs_to(src, "r = 1", 1)

    def test_a_constant_makes_a_line_unreachable(self):
        src = ("def f(x):\n    r = 0\n    x = 5\n    if x < 3:\n"
               "        r = 1\n    return r\n")
        self.assertIsNone(reach(src, "r = 1"))

    def test_reach_node_on_a_point(self):
        g = graph(RUNNING)
        m = reach_node(g, target_of(g, "r = 1"))
        self.assertLess(m["x"], 3)
        self.assertLess(10, m["x"] + m["y"])

    def test_the_entry_is_reached_by_anything(self):
        g = graph(MAGIC)
        self.assertIsNotNone(reach_node(g, g.entry))


class TestReturns(unittest.TestCase):
    def check_returns(self, src, value):
        prog = parse(src)
        m = returns(build(prog), value)
        self.assertIsNotNone(m)
        self.assertEqual(run(prog, [m[p] for p in prog.params]), value)

    def test_solving_for_the_output(self):
        g = graph("def f(x):\n    y = x * 2\n    return y + 1\n")
        self.assertEqual(returns(g, 15), {"x": 7})

    def test_each_value_of_the_running_example(self):
        self.check_returns(RUNNING, 0)
        self.check_returns(RUNNING, 1)

    def test_an_impossible_value(self):
        self.assertIsNone(returns(graph(RUNNING), 2))

    def test_not_only_the_first_path(self):
        src = "def f(x):\n    if x < 0:\n        x = 0\n    return x\n"
        self.check_returns(src, 5)
        self.assertIsNone(returns(graph(src), -5))

    def test_a_loop(self):
        self.assertEqual(returns(graph(LOOP), 5), {"n": 5})

    def test_a_negative_answer(self):
        g = graph("def f(x):\n    return x * -3\n")
        self.assertEqual(returns(g, 12), {"x": -4})


class TestSearch(unittest.TestCase):
    def test_infeasible_paths_are_pruned(self):
        self.assertEqual(len(paths(graph(RUNNING))), 3)

    def test_path_explosion(self):
        """n independent branches give 2^n paths."""
        for n in (1, 2, 3, 4):
            src = "def f(" + ", ".join(f"a{i}" for i in range(n)) + "):\n"
            for i in range(n):
                src += f"    if a{i} < 1:\n        a{i} = 1\n"
            src += "    return a0\n"
            with self.subTest(branches=n):
                self.assertEqual(len(paths(graph(src))), 2 ** n)

    def test_correlated_branches(self):
        """The second if repeats the first: two paths, not four."""
        src = ("def f(x):\n    r = 0\n    if x < 0:\n        r = 1\n"
               "    if x < 0:\n        r = r + 1\n    return r\n")
        self.assertEqual(len(paths(graph(src))), 2)

    def test_a_loop_is_cut_at_the_depth_bound(self):
        g = graph(LOOP)
        self.assertEqual([len(paths(g, d)) for d in (5, 10, 20)], [3, 6, 11])


if __name__ == "__main__":
    unittest.main()
