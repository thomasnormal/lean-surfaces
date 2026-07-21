# Tutorials — proving Python programs correct, from zero

A progressive series. Each part builds on the previous one, each ships with an
executable companion in [`Examples/python/`](../../Examples/python/) that
`lake build` checks — every code block you are meant to type exists in the
tree and is verified on every build.

| # | Tutorial | You leave having… | Companion |
|---|---|---|---|
| 1 | [Your first run](01-first-run.md) | pushed your own 3-line Python file through the whole pipeline: extract, build, run, diff-test | [`tut_01.py`](../../Examples/python/tut_01.py) |
| 2 | [Your first spec](02-first-spec.md) | proved a theorem about a Python function with the `==>` arrow and `py_prove`, and understood what it *means* | [`tut_02.py`](../../Examples/python/tut_02.py) |
| 3 | [Branching and preconditions](03-branching-and-preconditions.md) | handled `if`, stated preconditions as hypotheses, and learned to read a goal state | [`tut_03.py`](../../Examples/python/tut_03.py) |
| 4 | [Loops](04-loops.md) | **the centerpiece** — found a loop invariant yourself and proved a `while` loop with `py_begin`/`py_loop` | [`tut_04.py`](../../Examples/python/tut_04.py) |
| 5 | [Exceptions and partial correctness](05-exceptions-and-partial.md) | specified a raise with `==>!`, used the strengthened partial arrow `~~>`, and know why the weak form is banned | [`tut_05.py`](../../Examples/python/tut_05.py) |
| 6 | [When proofs fail](06-when-proofs-fail.md) | seen the real error message for every common failure mode, with diagnosis and fix | [`tut_06.py`](../../Examples/python/tut_06.py) |

## Prerequisites

- A checkout of this repository. The Lean toolchain is pinned in
  `lean-toolchain` (`leanprover/lean4:v4.33.0-rc1`); if you have
  [elan](https://github.com/leanprover/elan) the first `lake build` fetches it.
  There are no package dependencies — core Lean only.
- Python ≥ 3.9 (standard library only) for the extractor and the differential
  harness.
- Basic Lean 4 tactic literacy helps from tutorial 2 on (`intro`, `exact`,
  `omega`); tutorial 1 needs none.

Run every command from the repository root.

## Where this series sits

Tutorials are learning-oriented: they walk, they do not enumerate. For
lookup-oriented tables (arrows, tactics, types, CLI) see
[../reference.md](../reference.md); for task-oriented recipes see
[../howto/](../howto/); for the design rationale see
[../explanation.md](../explanation.md), [../DESIGN.md](../DESIGN.md)
(normative interpreter contract) and [../spec-surface.md](../spec-surface.md)
(normative spec-surface design). This series covers the **Python lane** only;
the SystemVerilog lane (`LeanModels/Sv/`, `Examples/sv/`) is in progress and
has its own documents (`../sv-*.md`).
