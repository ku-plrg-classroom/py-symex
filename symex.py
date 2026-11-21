"""Symbolic execution: walk the CFG with symbols, collect a path condition,
and ask Z3 for an input that follows it.

Integers and booleans only. Lists and strings would need Z3's array and
string theories, and the path condition is what matters here: they raise
NotSupported.
"""

from __future__ import annotations

from dataclasses import dataclass

import z3

from cfg import CFG, Edge, Assume, NodeId, build
from syntax import *


class NotSupported(Exception):
    """An expression the solver is not given here: strings and lists."""


@dataclass(frozen=True)
class SymState:
    node: NodeId
    env: tuple                      # ((name, z3 expr), ...) -- hashable
    pc: tuple                       # conjuncts of the path condition

    def get(self, x: str):
        for k, v in self.env:
            if k == x:
                return v
        return None

    def set(self, x: str, v):
        return SymState(self.node, tuple((k, w) for k, w in self.env if k != x)
                        + ((x, v),), self.pc)

    def at(self, n: NodeId):
        return SymState(n, self.env, self.pc)

    def assume(self, c):
        return SymState(self.node, self.env, self.pc + (c,))


def start(g: CFG) -> SymState:
    """One fresh symbol per parameter: the input is unknown."""
    return SymState(g.entry, tuple((p, z3.Int(p)) for p in g.params), ())


def to_z3(e: Expr, s: SymState):
    """The z3 term for the expression e in the state s.

    - an integer literal: `z3.IntVal(n)`; a boolean literal: `z3.BoolVal(b)`
    - a variable: the term s holds for it; if s holds none, the program
      reads a variable before assigning it: raise NameError
    - `+ * < <= == !=` and unary `-`: the same operator on the z3 terms
      of the operands (Python's operators work on z3 terms)
    - `and`, `or`, `not`: `z3.And`, `z3.Or`, `z3.Not`
    - anything else (strings, lists, indexing): raise NotSupported
    """
    raise NotImplementedError("TODO: to_z3")


def sat(pc: tuple) -> z3.ModelRef | None:
    """A model of the path condition, or None when no input follows it."""
    s = z3.Solver()
    s.add(*pc)
    return s.model() if s.check() == z3.sat else None


def model_of(g: CFG, m: z3.ModelRef) -> dict[str, int]:
    return {p: m.eval(z3.Int(p), model_completion=True).as_long()
            for p in g.params}


def transfer(st: SymState, e: Edge) -> SymState | None:
    """The symbolic state after taking edge e, or None if that is infeasible.

    The result is always at point e.dst. By the command of e:

    - `assume(cond)`: add the z3 term for cond to the path condition. If no
      input satisfies the new path condition (ask `sat`), return None.
    - `x = rhs`: x now holds the z3 term for rhs.
    - anything else (`pass`): nothing changes but the point.

    `to_z3` turns an expression into a z3 term in a state, and the methods
    of SymState build the new state. A SymState is never changed in place.
    """
    raise NotImplementedError("TODO: transfer")


def walk(g: CFG, max_depth: int = 60):
    """Every feasible symbolic state, depth-first."""
    stack = [(start(g), 0)]
    while stack:
        st, d = stack.pop()
        yield st, d
        if d >= max_depth:
            continue
        for e in reversed(g.succ[st.node]):
            nxt = transfer(st, e)
            if nxt is not None:
                stack.append((nxt, d + 1))


def reach_node(g: CFG, target: NodeId,
               max_depth: int = 60) -> dict[str, int] | None:
    """An input that reaches `target`.

    Take the first state that `walk(g, max_depth)` yields at point `target`
    and solve its path condition; `model_of` turns the model into an input,
    a dict from each parameter to an int. None if no state reaches `target`.
    """
    raise NotImplementedError("TODO: reach_node")


def returns(g: CFG, value: int, max_depth: int = 60) -> dict[str, int] | None:
    """An input that makes the program return `value`.

    Look at the states that `walk(g, max_depth)` yields at the exit, in
    order. For each, the returned expression `g.ret` must equal `value`, on
    top of its path condition. Return the input for the first state where
    that is satisfiable, or None if there is none.
    """
    raise NotImplementedError("TODO: returns")


def paths(g: CFG, max_depth: int = 30) -> list[tuple]:
    """Every feasible path condition, up to a depth bound."""
    return [st.pc for st, d in walk(g, max_depth)
            if st.node == g.exit or d >= max_depth]


# --------------------------------------------------------------- convenience

def target_of(g: CFG, text: str) -> NodeId:
    """The program point where the command that prints as `text` runs."""
    hits = [e.src for e in g.edges if text in str(e)]
    if not hits:
        raise KeyError(f"no command matching {text!r}")
    return hits[0]


def reach(src: str, text: str) -> dict[str, int] | None:
    """An input to the program in `src` that reaches the statement `text`."""
    g = build(parse(src))
    return reach_node(g, target_of(g, text))
