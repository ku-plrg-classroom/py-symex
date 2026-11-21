# MiniPy Symbolic Executor

A symbolic executor for **MiniPy**, a subset of Python: one `def`, integers,
booleans, strings, lists, `if`, `while`, and a final `return`. Programs are
parsed, turned into a control flow graph, and walked with **symbols** in place
of the inputs. Each path collects a **path condition**, and the Z3 solver
turns it into a concrete input that takes that path.

The symbolic state and the depth-first search are written for you. The
translation to Z3, the step along one edge, and the two questions asked of
the search are left for you to write. The tests tell you when you are done.

## Layout

| File | What it is | Edit? |
|---|---|---|
| `symex.py` | the symbolic executor, with holes | **yes, only this one** |
| `test_symex.py` | the tests | no |
| `syntax.py` | the MiniPy parser and AST | no |
| `cfg.py` | control flow graphs | no |
| `interp.py` | the concrete interpreter; the tests run your inputs on it | no |
| `examples/` | small MiniPy programs to try | no |

## The holes

Every function in `symex.py` that raises `NotImplementedError` is yours. Read
the rest of the file first: `SymState` and its methods, `start`, `sat`,
`model_of`, and `walk` are finished, and you will use them all.

1. **`to_z3(e, s)`**: the Z3 term for a MiniPy expression in a symbolic
   state. The same cases as the interpreter's `eval_expr`, but it builds a
   term instead of a value.
2. **`transfer(st, e)`**: the symbolic state after edge `e`, or `None` if no
   input can take it. An `assume` adds to the path condition and asks the
   solver; an assignment stores a Z3 term; anything else only moves.
3. **`reach_node(g, target)`**: an input that reaches the point `target`.
4. **`returns(g, value)`**: an input that makes the program return `value`.

The docstring of each function says exactly what it must return. Define any
helper you like.

## Running it

```python
from cfg import build
from syntax import parse
from symex import reach, reach_node, returns, target_of

src = open("examples/running.py").read()
print(reach(src, "r = 1"))           # an input that reaches r = 1, e.g. {'x': 2, 'y': 9}
print(reach(src, "r = 2"))           # None: no input reaches r = 2

g = build(parse(src))
print(returns(g, 0))                 # an input for which f returns 0
print(returns(g, 2))                 # None: f never returns 2
print(reach(open("examples/magic.py").read(), "r = 1"))       # {'x': 714}
```

`reach(src, text)` finds the point where the command printed as `text` runs
(`target_of`) and calls your `reach_node` there. Any input that satisfies the
path condition is correct: the tests do not compare it with a fixed answer.
They **run the program** on your input and check what it does.

## Running the tests

```
python3 -m unittest test_symex
```

Run one class at a time while you work, in this order:

```
python3 -m unittest test_symex.TestToZ3
python3 -m unittest test_symex.TestTransfer
```

`transfer` needs `to_z3`, and `TestReach`, `TestReturns`, and `TestSearch`
need both: the search calls `transfer` for every edge.

## Requirements

Python 3.12 or later, and the Z3 solver:

```
pip install z3-solver
```
