/-
**The module INITIALIZER, discharged down to one statement** — and with it
`GenMovesEqRef` from a hypothesis about ONE line of the shipped file instead
of two about the whole starting world.

`genmoves_drain.lean` ends at `gen_moves_eq_ref_of_dirs`: the flagship, from
two ground facts about `initWorld sunfish` (that it binds `directions` to
`.ref 63`, and that slot 63 holds `dirsObj`). Both are TRUE — the compiled
evaluator answers them in well under a second — and both were out of the
kernel's reach, because `initWorld` RUNS the module and `rfl` asks for the
whole run in one reduction (measured there: OOM at ~7 min / 16 GB).

This file does not make that reduction cheaper. It makes it SMALLER, by
running the initializer the way the initializer is written — one top-level
statement at a time, through `LeanModels/Python/ModuleInit.lean`'s calculus —
and paying the kernel only for the statements it can afford:

| top-level statements | what they are | kernel |
|---|---|---|
| 0–6 | imports, `version`, `piece`, `pst` (the raw tables) | **0.11 s, proved** (`run_prefix`) |
| 7–8 | the `pst` PIPELINE: the padding loop and `K_MID`/`K_END` | **the wall** (docs/backlog.md §L12) |
| 9–23 | the constants, `directions`, the MATE window, `opt_ranges`, `hist`, the `__main__` guard | **0.72 s, proved** (`dirs_ref` / `dirs_obj` run through them) |

So the initializer's twenty-four statements are twenty-two proved and two
hypothesised, and the two are named exactly: `PstPipelineRuns`, the padding
loop plus the endgame table, from the pinned state before them to the pinned
state after. Everything downstream of that — the address arithmetic that puts
`directions` at slot 63, the live-view resolution, `resolvedG`, the poisoning
of `opt_ranges`, the `NameError` at the `__main__` guard — is kernel-proved
here, not assumed.

**Why the two are a wall, measured rather than asserted** (docs/backlog.md
§L12 carries the table). Statement 7 is `for k, table in pst.items():`, whose
body's middle line is `pst[k] = sum((padrow(table[i*8:i*8+8]) for i in
range(8)), ())`. From a fully pinned input state that ONE Python statement,
by `rfl`, ran 154 s to a 4 000 000-heartbeat timeout and 420 s / 8.5 GB to an
OOM kill without finishing. Statement 8 (`K_MID, K_END = pst["K"],
tuple(<genexp over range(120)>)`) ran 627 s to an OOM kill. Chopping the top
level finer does not help: the wall is INSIDE a single statement, which is
why the pinned-literal route stops here and the remaining work is the
sub-statement calculus (`initItemsLoop_step` / `initBodyStmts_cons` are
landed for it, and the `sum`-over-a-generator round is the next chop).

**The hypothesis is not a wish.** `#guard`s at the bottom run
`PstPipelineRuns` and both projections through the compiled evaluator, so if
the shipped program changes and the pinned states go stale, this file fails
loudly rather than proving something about a world sunfish no longer has.
-/
import LeanModels.Python.ModuleInit
import Examples.python.sunfish.genmoves_drain

namespace Examples.python.sunfish.init_chain

open LeanModels LeanModels.Python
open Examples.python.sunfish.pins
open Examples.python.sunfish.genmoves_scan
open Examples.python.sunfish.genmoves_theorem
open Examples.python.sunfish.genmoves_drain

/-! ### The top level, projected

Never retyped: the three pieces are `take`/`drop` of the shipped module's own
statement array, so a changed program moves them together and the pins below
stop matching. -/

/-- The seven statements before the `pst` pipeline. -/
def prefix7 : List Stmt := sunfish.topLevel.toList.take 7

/-- The prefix as the pipeline's `done` view. -/
def done7 : Array Stmt := prefix7.toArray

/-- The `pst` PIPELINE: the padding loop (line 84) and the `K_MID`/`K_END`
line (line 96). The two statements this file does not run. -/
def pstPipeline : List Stmt := [sunfish.topLevel[7]!, sunfish.topLevel[8]!]

/-- The `done` view after the pipeline. -/
def donePst : Array Stmt := (sunfish.topLevel.toList.take 9).toArray

/-- Everything after the pipeline: the constants, `directions`, the MATE
window, the out-of-tier right-hand sides, and the `__main__` guard. -/
def tail9 : List Stmt := sunfish.topLevel.toList.drop 9

/-! ### The two pinned states

`h7`/`acc7` is the live state after the SEVEN statements before the
`pst` pipeline; `h9`/`acc9` the state after it. Both are printed from
the compiled evaluator and re-entered here, and neither is trusted: the
first is proved by `run_prefix` below, and the second is exactly what
the one hypothesis names. -/

def h7 : Heap :=
  #[LeanModels.Python.Obj.dict
    #[(LeanModels.Python.RVal.str "P", LeanModels.Python.RVal.int 100),
      (LeanModels.Python.RVal.str "N", LeanModels.Python.RVal.int 280),
      (LeanModels.Python.RVal.str "B", LeanModels.Python.RVal.int 320),
      (LeanModels.Python.RVal.str "R", LeanModels.Python.RVal.int 479),
      (LeanModels.Python.RVal.str "Q", LeanModels.Python.RVal.int 929),
      (LeanModels.Python.RVal.str "K", LeanModels.Python.RVal.int 60000)]
    0,
  LeanModels.Python.Obj.dict
    #[(LeanModels.Python.RVal.str "P",
       LeanModels.Python.RVal.tuple
         #[LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 78,
           LeanModels.Python.RVal.int 83, LeanModels.Python.RVal.int 86, LeanModels.Python.RVal.int 73,
           LeanModels.Python.RVal.int 102, LeanModels.Python.RVal.int 82, LeanModels.Python.RVal.int 85,
           LeanModels.Python.RVal.int 90, LeanModels.Python.RVal.int 7, LeanModels.Python.RVal.int 29,
           LeanModels.Python.RVal.int 21, LeanModels.Python.RVal.int 44, LeanModels.Python.RVal.int 40,
           LeanModels.Python.RVal.int 31, LeanModels.Python.RVal.int 44, LeanModels.Python.RVal.int 7,
           LeanModels.Python.RVal.int (-17), LeanModels.Python.RVal.int 16, LeanModels.Python.RVal.int (-2),
           LeanModels.Python.RVal.int 15, LeanModels.Python.RVal.int 14, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 15, LeanModels.Python.RVal.int (-13), LeanModels.Python.RVal.int (-26),
           LeanModels.Python.RVal.int 3, LeanModels.Python.RVal.int 10, LeanModels.Python.RVal.int 9,
           LeanModels.Python.RVal.int 6, LeanModels.Python.RVal.int 1, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int (-23), LeanModels.Python.RVal.int (-22), LeanModels.Python.RVal.int 9,
           LeanModels.Python.RVal.int 5, LeanModels.Python.RVal.int (-11), LeanModels.Python.RVal.int (-10),
           LeanModels.Python.RVal.int (-2), LeanModels.Python.RVal.int 3, LeanModels.Python.RVal.int (-19),
           LeanModels.Python.RVal.int (-31), LeanModels.Python.RVal.int 8, LeanModels.Python.RVal.int (-7),
           LeanModels.Python.RVal.int (-37), LeanModels.Python.RVal.int (-36), LeanModels.Python.RVal.int (-14),
           LeanModels.Python.RVal.int 3, LeanModels.Python.RVal.int (-31), LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0]),
      (LeanModels.Python.RVal.str "N",
       LeanModels.Python.RVal.tuple
         #[LeanModels.Python.RVal.int (-66), LeanModels.Python.RVal.int (-53), LeanModels.Python.RVal.int (-75),
           LeanModels.Python.RVal.int (-75), LeanModels.Python.RVal.int (-10), LeanModels.Python.RVal.int (-55),
           LeanModels.Python.RVal.int (-58), LeanModels.Python.RVal.int (-70), LeanModels.Python.RVal.int (-3),
           LeanModels.Python.RVal.int (-6), LeanModels.Python.RVal.int 100, LeanModels.Python.RVal.int (-36),
           LeanModels.Python.RVal.int 4, LeanModels.Python.RVal.int 62, LeanModels.Python.RVal.int (-4),
           LeanModels.Python.RVal.int (-14), LeanModels.Python.RVal.int 10, LeanModels.Python.RVal.int 67,
           LeanModels.Python.RVal.int 1, LeanModels.Python.RVal.int 74, LeanModels.Python.RVal.int 73,
           LeanModels.Python.RVal.int 27, LeanModels.Python.RVal.int 62, LeanModels.Python.RVal.int (-2),
           LeanModels.Python.RVal.int 24, LeanModels.Python.RVal.int 24, LeanModels.Python.RVal.int 45,
           LeanModels.Python.RVal.int 37, LeanModels.Python.RVal.int 33, LeanModels.Python.RVal.int 41,
           LeanModels.Python.RVal.int 25, LeanModels.Python.RVal.int 17, LeanModels.Python.RVal.int (-1),
           LeanModels.Python.RVal.int 5, LeanModels.Python.RVal.int 31, LeanModels.Python.RVal.int 21,
           LeanModels.Python.RVal.int 22, LeanModels.Python.RVal.int 35, LeanModels.Python.RVal.int 2,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int (-18), LeanModels.Python.RVal.int 10,
           LeanModels.Python.RVal.int 13, LeanModels.Python.RVal.int 22, LeanModels.Python.RVal.int 18,
           LeanModels.Python.RVal.int 15, LeanModels.Python.RVal.int 11, LeanModels.Python.RVal.int (-14),
           LeanModels.Python.RVal.int (-23), LeanModels.Python.RVal.int (-15), LeanModels.Python.RVal.int 2,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 2, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int (-23), LeanModels.Python.RVal.int (-20), LeanModels.Python.RVal.int (-74),
           LeanModels.Python.RVal.int (-23), LeanModels.Python.RVal.int (-26), LeanModels.Python.RVal.int (-24),
           LeanModels.Python.RVal.int (-19), LeanModels.Python.RVal.int (-35), LeanModels.Python.RVal.int (-22),
           LeanModels.Python.RVal.int (-69)]),
      (LeanModels.Python.RVal.str "B",
       LeanModels.Python.RVal.tuple
         #[LeanModels.Python.RVal.int (-59), LeanModels.Python.RVal.int (-78), LeanModels.Python.RVal.int (-82),
           LeanModels.Python.RVal.int (-76), LeanModels.Python.RVal.int (-23), LeanModels.Python.RVal.int (-107),
           LeanModels.Python.RVal.int (-37), LeanModels.Python.RVal.int (-50), LeanModels.Python.RVal.int (-11),
           LeanModels.Python.RVal.int 20, LeanModels.Python.RVal.int 35, LeanModels.Python.RVal.int (-42),
           LeanModels.Python.RVal.int (-39), LeanModels.Python.RVal.int 31, LeanModels.Python.RVal.int 2,
           LeanModels.Python.RVal.int (-22), LeanModels.Python.RVal.int (-9), LeanModels.Python.RVal.int 39,
           LeanModels.Python.RVal.int (-32), LeanModels.Python.RVal.int 41, LeanModels.Python.RVal.int 52,
           LeanModels.Python.RVal.int (-10), LeanModels.Python.RVal.int 28, LeanModels.Python.RVal.int (-14),
           LeanModels.Python.RVal.int 25, LeanModels.Python.RVal.int 17, LeanModels.Python.RVal.int 20,
           LeanModels.Python.RVal.int 34, LeanModels.Python.RVal.int 26, LeanModels.Python.RVal.int 25,
           LeanModels.Python.RVal.int 15, LeanModels.Python.RVal.int 10, LeanModels.Python.RVal.int 13,
           LeanModels.Python.RVal.int 10, LeanModels.Python.RVal.int 17, LeanModels.Python.RVal.int 23,
           LeanModels.Python.RVal.int 17, LeanModels.Python.RVal.int 16, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 7, LeanModels.Python.RVal.int 14, LeanModels.Python.RVal.int 25,
           LeanModels.Python.RVal.int 24, LeanModels.Python.RVal.int 15, LeanModels.Python.RVal.int 8,
           LeanModels.Python.RVal.int 25, LeanModels.Python.RVal.int 20, LeanModels.Python.RVal.int 15,
           LeanModels.Python.RVal.int 19, LeanModels.Python.RVal.int 20, LeanModels.Python.RVal.int 11,
           LeanModels.Python.RVal.int 6, LeanModels.Python.RVal.int 7, LeanModels.Python.RVal.int 6,
           LeanModels.Python.RVal.int 20, LeanModels.Python.RVal.int 16, LeanModels.Python.RVal.int (-7),
           LeanModels.Python.RVal.int 2, LeanModels.Python.RVal.int (-15), LeanModels.Python.RVal.int (-12),
           LeanModels.Python.RVal.int (-14), LeanModels.Python.RVal.int (-15), LeanModels.Python.RVal.int (-10),
           LeanModels.Python.RVal.int (-10)]),
      (LeanModels.Python.RVal.str "R",
       LeanModels.Python.RVal.tuple
         #[LeanModels.Python.RVal.int 35, LeanModels.Python.RVal.int 29, LeanModels.Python.RVal.int 33,
           LeanModels.Python.RVal.int 4, LeanModels.Python.RVal.int 37, LeanModels.Python.RVal.int 33,
           LeanModels.Python.RVal.int 56, LeanModels.Python.RVal.int 50, LeanModels.Python.RVal.int 55,
           LeanModels.Python.RVal.int 29, LeanModels.Python.RVal.int 56, LeanModels.Python.RVal.int 67,
           LeanModels.Python.RVal.int 55, LeanModels.Python.RVal.int 62, LeanModels.Python.RVal.int 34,
           LeanModels.Python.RVal.int 60, LeanModels.Python.RVal.int 19, LeanModels.Python.RVal.int 35,
           LeanModels.Python.RVal.int 28, LeanModels.Python.RVal.int 33, LeanModels.Python.RVal.int 45,
           LeanModels.Python.RVal.int 27, LeanModels.Python.RVal.int 25, LeanModels.Python.RVal.int 15,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 5, LeanModels.Python.RVal.int 16,
           LeanModels.Python.RVal.int 13, LeanModels.Python.RVal.int 18, LeanModels.Python.RVal.int (-4),
           LeanModels.Python.RVal.int (-9), LeanModels.Python.RVal.int (-6), LeanModels.Python.RVal.int (-28),
           LeanModels.Python.RVal.int (-35), LeanModels.Python.RVal.int (-16), LeanModels.Python.RVal.int (-21),
           LeanModels.Python.RVal.int (-13), LeanModels.Python.RVal.int (-29), LeanModels.Python.RVal.int (-46),
           LeanModels.Python.RVal.int (-30), LeanModels.Python.RVal.int (-42), LeanModels.Python.RVal.int (-28),
           LeanModels.Python.RVal.int (-42), LeanModels.Python.RVal.int (-25), LeanModels.Python.RVal.int (-25),
           LeanModels.Python.RVal.int (-35), LeanModels.Python.RVal.int (-26), LeanModels.Python.RVal.int (-46),
           LeanModels.Python.RVal.int (-53), LeanModels.Python.RVal.int (-38), LeanModels.Python.RVal.int (-31),
           LeanModels.Python.RVal.int (-26), LeanModels.Python.RVal.int (-29), LeanModels.Python.RVal.int (-43),
           LeanModels.Python.RVal.int (-44), LeanModels.Python.RVal.int (-53), LeanModels.Python.RVal.int (-30),
           LeanModels.Python.RVal.int (-24), LeanModels.Python.RVal.int (-18), LeanModels.Python.RVal.int 5,
           LeanModels.Python.RVal.int (-2), LeanModels.Python.RVal.int (-18), LeanModels.Python.RVal.int (-31),
           LeanModels.Python.RVal.int (-32)]),
      (LeanModels.Python.RVal.str "Q",
       LeanModels.Python.RVal.tuple
         #[LeanModels.Python.RVal.int 6, LeanModels.Python.RVal.int 1, LeanModels.Python.RVal.int (-8),
           LeanModels.Python.RVal.int (-104), LeanModels.Python.RVal.int 69, LeanModels.Python.RVal.int 24,
           LeanModels.Python.RVal.int 88, LeanModels.Python.RVal.int 26, LeanModels.Python.RVal.int 14,
           LeanModels.Python.RVal.int 32, LeanModels.Python.RVal.int 60, LeanModels.Python.RVal.int (-10),
           LeanModels.Python.RVal.int 20, LeanModels.Python.RVal.int 76, LeanModels.Python.RVal.int 57,
           LeanModels.Python.RVal.int 24, LeanModels.Python.RVal.int (-2), LeanModels.Python.RVal.int 43,
           LeanModels.Python.RVal.int 32, LeanModels.Python.RVal.int 60, LeanModels.Python.RVal.int 72,
           LeanModels.Python.RVal.int 63, LeanModels.Python.RVal.int 43, LeanModels.Python.RVal.int 2,
           LeanModels.Python.RVal.int 1, LeanModels.Python.RVal.int (-16), LeanModels.Python.RVal.int 22,
           LeanModels.Python.RVal.int 17, LeanModels.Python.RVal.int 25, LeanModels.Python.RVal.int 20,
           LeanModels.Python.RVal.int (-13), LeanModels.Python.RVal.int (-6), LeanModels.Python.RVal.int (-14),
           LeanModels.Python.RVal.int (-15), LeanModels.Python.RVal.int (-2), LeanModels.Python.RVal.int (-5),
           LeanModels.Python.RVal.int (-1), LeanModels.Python.RVal.int (-10), LeanModels.Python.RVal.int (-20),
           LeanModels.Python.RVal.int (-22), LeanModels.Python.RVal.int (-30), LeanModels.Python.RVal.int (-6),
           LeanModels.Python.RVal.int (-13), LeanModels.Python.RVal.int (-11), LeanModels.Python.RVal.int (-16),
           LeanModels.Python.RVal.int (-11), LeanModels.Python.RVal.int (-16), LeanModels.Python.RVal.int (-27),
           LeanModels.Python.RVal.int (-36), LeanModels.Python.RVal.int (-18), LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int (-19), LeanModels.Python.RVal.int (-15), LeanModels.Python.RVal.int (-15),
           LeanModels.Python.RVal.int (-21), LeanModels.Python.RVal.int (-38), LeanModels.Python.RVal.int (-39),
           LeanModels.Python.RVal.int (-30), LeanModels.Python.RVal.int (-31), LeanModels.Python.RVal.int (-13),
           LeanModels.Python.RVal.int (-31), LeanModels.Python.RVal.int (-36), LeanModels.Python.RVal.int (-34),
           LeanModels.Python.RVal.int (-42)]),
      (LeanModels.Python.RVal.str "K",
       LeanModels.Python.RVal.tuple
         #[LeanModels.Python.RVal.int 4, LeanModels.Python.RVal.int 54, LeanModels.Python.RVal.int 47,
           LeanModels.Python.RVal.int (-99), LeanModels.Python.RVal.int (-99), LeanModels.Python.RVal.int 60,
           LeanModels.Python.RVal.int 83, LeanModels.Python.RVal.int (-62), LeanModels.Python.RVal.int (-32),
           LeanModels.Python.RVal.int 10, LeanModels.Python.RVal.int 55, LeanModels.Python.RVal.int 56,
           LeanModels.Python.RVal.int 56, LeanModels.Python.RVal.int 55, LeanModels.Python.RVal.int 10,
           LeanModels.Python.RVal.int 3, LeanModels.Python.RVal.int (-62), LeanModels.Python.RVal.int 12,
           LeanModels.Python.RVal.int (-57), LeanModels.Python.RVal.int 44, LeanModels.Python.RVal.int (-67),
           LeanModels.Python.RVal.int 28, LeanModels.Python.RVal.int 37, LeanModels.Python.RVal.int (-31),
           LeanModels.Python.RVal.int (-55), LeanModels.Python.RVal.int 50, LeanModels.Python.RVal.int 11,
           LeanModels.Python.RVal.int (-4), LeanModels.Python.RVal.int (-19), LeanModels.Python.RVal.int 13,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int (-49), LeanModels.Python.RVal.int (-55),
           LeanModels.Python.RVal.int (-43), LeanModels.Python.RVal.int (-52), LeanModels.Python.RVal.int (-28),
           LeanModels.Python.RVal.int (-51), LeanModels.Python.RVal.int (-47), LeanModels.Python.RVal.int (-8),
           LeanModels.Python.RVal.int (-50), LeanModels.Python.RVal.int (-47), LeanModels.Python.RVal.int (-42),
           LeanModels.Python.RVal.int (-43), LeanModels.Python.RVal.int (-79), LeanModels.Python.RVal.int (-64),
           LeanModels.Python.RVal.int (-32), LeanModels.Python.RVal.int (-29), LeanModels.Python.RVal.int (-32),
           LeanModels.Python.RVal.int (-4), LeanModels.Python.RVal.int 3, LeanModels.Python.RVal.int (-14),
           LeanModels.Python.RVal.int (-50), LeanModels.Python.RVal.int (-57), LeanModels.Python.RVal.int (-18),
           LeanModels.Python.RVal.int 13, LeanModels.Python.RVal.int 4, LeanModels.Python.RVal.int 17,
           LeanModels.Python.RVal.int 30, LeanModels.Python.RVal.int (-3), LeanModels.Python.RVal.int (-14),
           LeanModels.Python.RVal.int 6, LeanModels.Python.RVal.int (-1), LeanModels.Python.RVal.int 40,
           LeanModels.Python.RVal.int 18])]
    0]

def acc7 : GlobalsAcc :=
  [("pst", some (LeanModels.Python.RVal.ref 1)),
 ("piece", some (LeanModels.Python.RVal.ref 0)),
 ("version", some (LeanModels.Python.RVal.str "sunfish 2026")),
 ("time", none)]

def h9 : Heap :=
  #[LeanModels.Python.Obj.dict
    #[(LeanModels.Python.RVal.str "P", LeanModels.Python.RVal.int 100),
      (LeanModels.Python.RVal.str "N", LeanModels.Python.RVal.int 280),
      (LeanModels.Python.RVal.str "B", LeanModels.Python.RVal.int 320),
      (LeanModels.Python.RVal.str "R", LeanModels.Python.RVal.int 479),
      (LeanModels.Python.RVal.str "Q", LeanModels.Python.RVal.int 929),
      (LeanModels.Python.RVal.str "K", LeanModels.Python.RVal.int 60000)]
    0,
  LeanModels.Python.Obj.dict
    #[(LeanModels.Python.RVal.str "P",
       LeanModels.Python.RVal.tuple
         #[LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 100, LeanModels.Python.RVal.int 100, LeanModels.Python.RVal.int 100,
           LeanModels.Python.RVal.int 100, LeanModels.Python.RVal.int 100, LeanModels.Python.RVal.int 100,
           LeanModels.Python.RVal.int 100, LeanModels.Python.RVal.int 100, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 178, LeanModels.Python.RVal.int 183,
           LeanModels.Python.RVal.int 186, LeanModels.Python.RVal.int 173, LeanModels.Python.RVal.int 202,
           LeanModels.Python.RVal.int 182, LeanModels.Python.RVal.int 185, LeanModels.Python.RVal.int 190,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 107,
           LeanModels.Python.RVal.int 129, LeanModels.Python.RVal.int 121, LeanModels.Python.RVal.int 144,
           LeanModels.Python.RVal.int 140, LeanModels.Python.RVal.int 131, LeanModels.Python.RVal.int 144,
           LeanModels.Python.RVal.int 107, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 83, LeanModels.Python.RVal.int 116, LeanModels.Python.RVal.int 98,
           LeanModels.Python.RVal.int 115, LeanModels.Python.RVal.int 114, LeanModels.Python.RVal.int 100,
           LeanModels.Python.RVal.int 115, LeanModels.Python.RVal.int 87, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 74, LeanModels.Python.RVal.int 103,
           LeanModels.Python.RVal.int 110, LeanModels.Python.RVal.int 109, LeanModels.Python.RVal.int 106,
           LeanModels.Python.RVal.int 101, LeanModels.Python.RVal.int 100, LeanModels.Python.RVal.int 77,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 78,
           LeanModels.Python.RVal.int 109, LeanModels.Python.RVal.int 105, LeanModels.Python.RVal.int 89,
           LeanModels.Python.RVal.int 90, LeanModels.Python.RVal.int 98, LeanModels.Python.RVal.int 103,
           LeanModels.Python.RVal.int 81, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 69, LeanModels.Python.RVal.int 108, LeanModels.Python.RVal.int 93,
           LeanModels.Python.RVal.int 63, LeanModels.Python.RVal.int 64, LeanModels.Python.RVal.int 86,
           LeanModels.Python.RVal.int 103, LeanModels.Python.RVal.int 69, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 100, LeanModels.Python.RVal.int 100,
           LeanModels.Python.RVal.int 100, LeanModels.Python.RVal.int 100, LeanModels.Python.RVal.int 100,
           LeanModels.Python.RVal.int 100, LeanModels.Python.RVal.int 100, LeanModels.Python.RVal.int 100,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0]),
      (LeanModels.Python.RVal.str "N",
       LeanModels.Python.RVal.tuple
         #[LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 214, LeanModels.Python.RVal.int 227, LeanModels.Python.RVal.int 205,
           LeanModels.Python.RVal.int 205, LeanModels.Python.RVal.int 270, LeanModels.Python.RVal.int 225,
           LeanModels.Python.RVal.int 222, LeanModels.Python.RVal.int 210, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 277, LeanModels.Python.RVal.int 274,
           LeanModels.Python.RVal.int 380, LeanModels.Python.RVal.int 244, LeanModels.Python.RVal.int 284,
           LeanModels.Python.RVal.int 342, LeanModels.Python.RVal.int 276, LeanModels.Python.RVal.int 266,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 290,
           LeanModels.Python.RVal.int 347, LeanModels.Python.RVal.int 281, LeanModels.Python.RVal.int 354,
           LeanModels.Python.RVal.int 353, LeanModels.Python.RVal.int 307, LeanModels.Python.RVal.int 342,
           LeanModels.Python.RVal.int 278, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 304, LeanModels.Python.RVal.int 304, LeanModels.Python.RVal.int 325,
           LeanModels.Python.RVal.int 317, LeanModels.Python.RVal.int 313, LeanModels.Python.RVal.int 321,
           LeanModels.Python.RVal.int 305, LeanModels.Python.RVal.int 297, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 279, LeanModels.Python.RVal.int 285,
           LeanModels.Python.RVal.int 311, LeanModels.Python.RVal.int 301, LeanModels.Python.RVal.int 302,
           LeanModels.Python.RVal.int 315, LeanModels.Python.RVal.int 282, LeanModels.Python.RVal.int 280,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 262,
           LeanModels.Python.RVal.int 290, LeanModels.Python.RVal.int 293, LeanModels.Python.RVal.int 302,
           LeanModels.Python.RVal.int 298, LeanModels.Python.RVal.int 295, LeanModels.Python.RVal.int 291,
           LeanModels.Python.RVal.int 266, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 257, LeanModels.Python.RVal.int 265, LeanModels.Python.RVal.int 282,
           LeanModels.Python.RVal.int 280, LeanModels.Python.RVal.int 282, LeanModels.Python.RVal.int 280,
           LeanModels.Python.RVal.int 257, LeanModels.Python.RVal.int 260, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 206, LeanModels.Python.RVal.int 257,
           LeanModels.Python.RVal.int 254, LeanModels.Python.RVal.int 256, LeanModels.Python.RVal.int 261,
           LeanModels.Python.RVal.int 245, LeanModels.Python.RVal.int 258, LeanModels.Python.RVal.int 211,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0]),
      (LeanModels.Python.RVal.str "B",
       LeanModels.Python.RVal.tuple
         #[LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 261, LeanModels.Python.RVal.int 242, LeanModels.Python.RVal.int 238,
           LeanModels.Python.RVal.int 244, LeanModels.Python.RVal.int 297, LeanModels.Python.RVal.int 213,
           LeanModels.Python.RVal.int 283, LeanModels.Python.RVal.int 270, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 309, LeanModels.Python.RVal.int 340,
           LeanModels.Python.RVal.int 355, LeanModels.Python.RVal.int 278, LeanModels.Python.RVal.int 281,
           LeanModels.Python.RVal.int 351, LeanModels.Python.RVal.int 322, LeanModels.Python.RVal.int 298,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 311,
           LeanModels.Python.RVal.int 359, LeanModels.Python.RVal.int 288, LeanModels.Python.RVal.int 361,
           LeanModels.Python.RVal.int 372, LeanModels.Python.RVal.int 310, LeanModels.Python.RVal.int 348,
           LeanModels.Python.RVal.int 306, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 345, LeanModels.Python.RVal.int 337, LeanModels.Python.RVal.int 340,
           LeanModels.Python.RVal.int 354, LeanModels.Python.RVal.int 346, LeanModels.Python.RVal.int 345,
           LeanModels.Python.RVal.int 335, LeanModels.Python.RVal.int 330, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 333, LeanModels.Python.RVal.int 330,
           LeanModels.Python.RVal.int 337, LeanModels.Python.RVal.int 343, LeanModels.Python.RVal.int 337,
           LeanModels.Python.RVal.int 336, LeanModels.Python.RVal.int 320, LeanModels.Python.RVal.int 327,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 334,
           LeanModels.Python.RVal.int 345, LeanModels.Python.RVal.int 344, LeanModels.Python.RVal.int 335,
           LeanModels.Python.RVal.int 328, LeanModels.Python.RVal.int 345, LeanModels.Python.RVal.int 340,
           LeanModels.Python.RVal.int 335, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 339, LeanModels.Python.RVal.int 340, LeanModels.Python.RVal.int 331,
           LeanModels.Python.RVal.int 326, LeanModels.Python.RVal.int 327, LeanModels.Python.RVal.int 326,
           LeanModels.Python.RVal.int 340, LeanModels.Python.RVal.int 336, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 313, LeanModels.Python.RVal.int 322,
           LeanModels.Python.RVal.int 305, LeanModels.Python.RVal.int 308, LeanModels.Python.RVal.int 306,
           LeanModels.Python.RVal.int 305, LeanModels.Python.RVal.int 310, LeanModels.Python.RVal.int 310,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0]),
      (LeanModels.Python.RVal.str "R",
       LeanModels.Python.RVal.tuple
         #[LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 514, LeanModels.Python.RVal.int 508, LeanModels.Python.RVal.int 512,
           LeanModels.Python.RVal.int 483, LeanModels.Python.RVal.int 516, LeanModels.Python.RVal.int 512,
           LeanModels.Python.RVal.int 535, LeanModels.Python.RVal.int 529, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 534, LeanModels.Python.RVal.int 508,
           LeanModels.Python.RVal.int 535, LeanModels.Python.RVal.int 546, LeanModels.Python.RVal.int 534,
           LeanModels.Python.RVal.int 541, LeanModels.Python.RVal.int 513, LeanModels.Python.RVal.int 539,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 498,
           LeanModels.Python.RVal.int 514, LeanModels.Python.RVal.int 507, LeanModels.Python.RVal.int 512,
           LeanModels.Python.RVal.int 524, LeanModels.Python.RVal.int 506, LeanModels.Python.RVal.int 504,
           LeanModels.Python.RVal.int 494, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 479, LeanModels.Python.RVal.int 484, LeanModels.Python.RVal.int 495,
           LeanModels.Python.RVal.int 492, LeanModels.Python.RVal.int 497, LeanModels.Python.RVal.int 475,
           LeanModels.Python.RVal.int 470, LeanModels.Python.RVal.int 473, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 451, LeanModels.Python.RVal.int 444,
           LeanModels.Python.RVal.int 463, LeanModels.Python.RVal.int 458, LeanModels.Python.RVal.int 466,
           LeanModels.Python.RVal.int 450, LeanModels.Python.RVal.int 433, LeanModels.Python.RVal.int 449,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 437,
           LeanModels.Python.RVal.int 451, LeanModels.Python.RVal.int 437, LeanModels.Python.RVal.int 454,
           LeanModels.Python.RVal.int 454, LeanModels.Python.RVal.int 444, LeanModels.Python.RVal.int 453,
           LeanModels.Python.RVal.int 433, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 426, LeanModels.Python.RVal.int 441, LeanModels.Python.RVal.int 448,
           LeanModels.Python.RVal.int 453, LeanModels.Python.RVal.int 450, LeanModels.Python.RVal.int 436,
           LeanModels.Python.RVal.int 435, LeanModels.Python.RVal.int 426, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 449, LeanModels.Python.RVal.int 455,
           LeanModels.Python.RVal.int 461, LeanModels.Python.RVal.int 484, LeanModels.Python.RVal.int 477,
           LeanModels.Python.RVal.int 461, LeanModels.Python.RVal.int 448, LeanModels.Python.RVal.int 447,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0]),
      (LeanModels.Python.RVal.str "Q",
       LeanModels.Python.RVal.tuple
         #[LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 935, LeanModels.Python.RVal.int 930, LeanModels.Python.RVal.int 921,
           LeanModels.Python.RVal.int 825, LeanModels.Python.RVal.int 998, LeanModels.Python.RVal.int 953,
           LeanModels.Python.RVal.int 1017, LeanModels.Python.RVal.int 955, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 943, LeanModels.Python.RVal.int 961,
           LeanModels.Python.RVal.int 989, LeanModels.Python.RVal.int 919, LeanModels.Python.RVal.int 949,
           LeanModels.Python.RVal.int 1005, LeanModels.Python.RVal.int 986, LeanModels.Python.RVal.int 953,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 927,
           LeanModels.Python.RVal.int 972, LeanModels.Python.RVal.int 961, LeanModels.Python.RVal.int 989,
           LeanModels.Python.RVal.int 1001, LeanModels.Python.RVal.int 992, LeanModels.Python.RVal.int 972,
           LeanModels.Python.RVal.int 931, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 930, LeanModels.Python.RVal.int 913, LeanModels.Python.RVal.int 951,
           LeanModels.Python.RVal.int 946, LeanModels.Python.RVal.int 954, LeanModels.Python.RVal.int 949,
           LeanModels.Python.RVal.int 916, LeanModels.Python.RVal.int 923, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 915, LeanModels.Python.RVal.int 914,
           LeanModels.Python.RVal.int 927, LeanModels.Python.RVal.int 924, LeanModels.Python.RVal.int 928,
           LeanModels.Python.RVal.int 919, LeanModels.Python.RVal.int 909, LeanModels.Python.RVal.int 907,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 899,
           LeanModels.Python.RVal.int 923, LeanModels.Python.RVal.int 916, LeanModels.Python.RVal.int 918,
           LeanModels.Python.RVal.int 913, LeanModels.Python.RVal.int 918, LeanModels.Python.RVal.int 913,
           LeanModels.Python.RVal.int 902, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 893, LeanModels.Python.RVal.int 911, LeanModels.Python.RVal.int 929,
           LeanModels.Python.RVal.int 910, LeanModels.Python.RVal.int 914, LeanModels.Python.RVal.int 914,
           LeanModels.Python.RVal.int 908, LeanModels.Python.RVal.int 891, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 890, LeanModels.Python.RVal.int 899,
           LeanModels.Python.RVal.int 898, LeanModels.Python.RVal.int 916, LeanModels.Python.RVal.int 898,
           LeanModels.Python.RVal.int 893, LeanModels.Python.RVal.int 895, LeanModels.Python.RVal.int 887,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0]),
      (LeanModels.Python.RVal.str "K",
       LeanModels.Python.RVal.tuple
         #[LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 60004, LeanModels.Python.RVal.int 60054, LeanModels.Python.RVal.int 60047,
           LeanModels.Python.RVal.int 59901, LeanModels.Python.RVal.int 59901, LeanModels.Python.RVal.int 60060,
           LeanModels.Python.RVal.int 60083, LeanModels.Python.RVal.int 59938, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 59968, LeanModels.Python.RVal.int 60010,
           LeanModels.Python.RVal.int 60055, LeanModels.Python.RVal.int 60056, LeanModels.Python.RVal.int 60056,
           LeanModels.Python.RVal.int 60055, LeanModels.Python.RVal.int 60010, LeanModels.Python.RVal.int 60003,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 59938,
           LeanModels.Python.RVal.int 60012, LeanModels.Python.RVal.int 59943, LeanModels.Python.RVal.int 60044,
           LeanModels.Python.RVal.int 59933, LeanModels.Python.RVal.int 60028, LeanModels.Python.RVal.int 60037,
           LeanModels.Python.RVal.int 59969, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 59945, LeanModels.Python.RVal.int 60050, LeanModels.Python.RVal.int 60011,
           LeanModels.Python.RVal.int 59996, LeanModels.Python.RVal.int 59981, LeanModels.Python.RVal.int 60013,
           LeanModels.Python.RVal.int 60000, LeanModels.Python.RVal.int 59951, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 59945, LeanModels.Python.RVal.int 59957,
           LeanModels.Python.RVal.int 59948, LeanModels.Python.RVal.int 59972, LeanModels.Python.RVal.int 59949,
           LeanModels.Python.RVal.int 59953, LeanModels.Python.RVal.int 59992, LeanModels.Python.RVal.int 59950,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 59953,
           LeanModels.Python.RVal.int 59958, LeanModels.Python.RVal.int 59957, LeanModels.Python.RVal.int 59921,
           LeanModels.Python.RVal.int 59936, LeanModels.Python.RVal.int 59968, LeanModels.Python.RVal.int 59971,
           LeanModels.Python.RVal.int 59968, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 59996, LeanModels.Python.RVal.int 60003, LeanModels.Python.RVal.int 59986,
           LeanModels.Python.RVal.int 59950, LeanModels.Python.RVal.int 59943, LeanModels.Python.RVal.int 59982,
           LeanModels.Python.RVal.int 60013, LeanModels.Python.RVal.int 60004, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 60017, LeanModels.Python.RVal.int 60030,
           LeanModels.Python.RVal.int 59997, LeanModels.Python.RVal.int 59986, LeanModels.Python.RVal.int 60006,
           LeanModels.Python.RVal.int 59999, LeanModels.Python.RVal.int 60040, LeanModels.Python.RVal.int 60018,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
           LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0])]
    0,
  LeanModels.Python.Obj.closure
    "padrow"
    #[{ arg := "row", span := { lineno := 85, colOffset := 20, endLineno := 85, endColOffset := 23 }, default := none }]
    true
    true
    false
    false
    #[LeanModels.Python.Stmt.ret
        (some (LeanModels.Python.Expr.binOp
           (LeanModels.Python.Expr.binOp
             (LeanModels.Python.Expr.tuple
               #[LeanModels.Python.Expr.constant
                   (LeanModels.Python.Const.int 0)
                   { lineno := 85, colOffset := 26, endLineno := 85, endColOffset := 27 }]
               { lineno := 85, colOffset := 25, endLineno := 85, endColOffset := 29 })
             (LeanModels.Python.BinOp.add)
             (LeanModels.Python.Expr.call
               (LeanModels.Python.Expr.name
                 "tuple"
                 { lineno := 85, colOffset := 32, endLineno := 85, endColOffset := 37 })
               #[LeanModels.Python.Expr.call
                   (LeanModels.Python.Expr.name
                     "<genexpr@5>"
                     { lineno := 85, colOffset := 37, endLineno := 85, endColOffset := 64 })
                   #[LeanModels.Python.Expr.name
                       "row"
                       { lineno := 85, colOffset := 60, endLineno := 85, endColOffset := 63 }]
                   #[]
                   none
                   { lineno := 85, colOffset := 37, endLineno := 85, endColOffset := 64 }]
               #[]
               none
               { lineno := 85, colOffset := 32, endLineno := 85, endColOffset := 64 })
             { lineno := 85, colOffset := 25, endLineno := 85, endColOffset := 64 })
           (LeanModels.Python.BinOp.add)
           (LeanModels.Python.Expr.tuple
             #[LeanModels.Python.Expr.constant
                 (LeanModels.Python.Const.int 0)
                 { lineno := 85, colOffset := 68, endLineno := 85, endColOffset := 69 }]
             { lineno := 85, colOffset := 67, endLineno := 85, endColOffset := 71 })
           { lineno := 85, colOffset := 25, endLineno := 85, endColOffset := 71 }))
        { lineno := 85, colOffset := 25, endLineno := 85, endColOffset := 71 }]
    [],
  LeanModels.Python.Obj.generator
    "<genexpr@6>"
    [(".0", LeanModels.Python.RVal.rangeV 0 8 1), ("i", LeanModels.Python.RVal.int 7)]
    []
    (LeanModels.Python.GenStatus.closed),
  LeanModels.Python.Obj.generator
    "<genexpr@5>"
    [(".0",
      LeanModels.Python.RVal.tuple
        #[LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
          LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
          LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0]),
     ("x", LeanModels.Python.RVal.int 0)]
    []
    (LeanModels.Python.GenStatus.closed),
  LeanModels.Python.Obj.generator
    "<genexpr@5>"
    [(".0",
      LeanModels.Python.RVal.tuple
        #[LeanModels.Python.RVal.int 78, LeanModels.Python.RVal.int 83, LeanModels.Python.RVal.int 86,
          LeanModels.Python.RVal.int 73, LeanModels.Python.RVal.int 102, LeanModels.Python.RVal.int 82,
          LeanModels.Python.RVal.int 85, LeanModels.Python.RVal.int 90]),
     ("x", LeanModels.Python.RVal.int 90)]
    []
    (LeanModels.Python.GenStatus.closed),
  LeanModels.Python.Obj.generator
    "<genexpr@5>"
    [(".0",
      LeanModels.Python.RVal.tuple
        #[LeanModels.Python.RVal.int 7, LeanModels.Python.RVal.int 29, LeanModels.Python.RVal.int 21,
          LeanModels.Python.RVal.int 44, LeanModels.Python.RVal.int 40, LeanModels.Python.RVal.int 31,
          LeanModels.Python.RVal.int 44, LeanModels.Python.RVal.int 7]),
     ("x", LeanModels.Python.RVal.int 7)]
    []
    (LeanModels.Python.GenStatus.closed),
  LeanModels.Python.Obj.generator
    "<genexpr@5>"
    [(".0",
      LeanModels.Python.RVal.tuple
        #[LeanModels.Python.RVal.int (-17), LeanModels.Python.RVal.int 16, LeanModels.Python.RVal.int (-2),
          LeanModels.Python.RVal.int 15, LeanModels.Python.RVal.int 14, LeanModels.Python.RVal.int 0,
          LeanModels.Python.RVal.int 15, LeanModels.Python.RVal.int (-13)]),
     ("x", LeanModels.Python.RVal.int (-13))]
    []
    (LeanModels.Python.GenStatus.closed),
  LeanModels.Python.Obj.generator
    "<genexpr@5>"
    [(".0",
      LeanModels.Python.RVal.tuple
        #[LeanModels.Python.RVal.int (-26), LeanModels.Python.RVal.int 3, LeanModels.Python.RVal.int 10,
          LeanModels.Python.RVal.int 9, LeanModels.Python.RVal.int 6, LeanModels.Python.RVal.int 1,
          LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int (-23)]),
     ("x", LeanModels.Python.RVal.int (-23))]
    []
    (LeanModels.Python.GenStatus.closed),
  LeanModels.Python.Obj.generator
    "<genexpr@5>"
    [(".0",
      LeanModels.Python.RVal.tuple
        #[LeanModels.Python.RVal.int (-22), LeanModels.Python.RVal.int 9, LeanModels.Python.RVal.int 5,
          LeanModels.Python.RVal.int (-11), LeanModels.Python.RVal.int (-10), LeanModels.Python.RVal.int (-2),
          LeanModels.Python.RVal.int 3, LeanModels.Python.RVal.int (-19)]),
     ("x", LeanModels.Python.RVal.int (-19))]
    []
    (LeanModels.Python.GenStatus.closed),
  LeanModels.Python.Obj.generator
    "<genexpr@5>"
    [(".0",
      LeanModels.Python.RVal.tuple
        #[LeanModels.Python.RVal.int (-31), LeanModels.Python.RVal.int 8, LeanModels.Python.RVal.int (-7),
          LeanModels.Python.RVal.int (-37), LeanModels.Python.RVal.int (-36), LeanModels.Python.RVal.int (-14),
          LeanModels.Python.RVal.int 3, LeanModels.Python.RVal.int (-31)]),
     ("x", LeanModels.Python.RVal.int (-31))]
    []
    (LeanModels.Python.GenStatus.closed),
  LeanModels.Python.Obj.generator
    "<genexpr@5>"
    [(".0",
      LeanModels.Python.RVal.tuple
        #[LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
          LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
          LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0]),
     ("x", LeanModels.Python.RVal.int 0)]
    []
    (LeanModels.Python.GenStatus.closed),
  LeanModels.Python.Obj.closure
    "padrow"
    #[{ arg := "row", span := { lineno := 85, colOffset := 20, endLineno := 85, endColOffset := 23 }, default := none }]
    true
    true
    false
    false
    #[LeanModels.Python.Stmt.ret
        (some (LeanModels.Python.Expr.binOp
           (LeanModels.Python.Expr.binOp
             (LeanModels.Python.Expr.tuple
               #[LeanModels.Python.Expr.constant
                   (LeanModels.Python.Const.int 0)
                   { lineno := 85, colOffset := 26, endLineno := 85, endColOffset := 27 }]
               { lineno := 85, colOffset := 25, endLineno := 85, endColOffset := 29 })
             (LeanModels.Python.BinOp.add)
             (LeanModels.Python.Expr.call
               (LeanModels.Python.Expr.name
                 "tuple"
                 { lineno := 85, colOffset := 32, endLineno := 85, endColOffset := 37 })
               #[LeanModels.Python.Expr.call
                   (LeanModels.Python.Expr.name
                     "<genexpr@5>"
                     { lineno := 85, colOffset := 37, endLineno := 85, endColOffset := 64 })
                   #[LeanModels.Python.Expr.name
                       "row"
                       { lineno := 85, colOffset := 60, endLineno := 85, endColOffset := 63 }]
                   #[]
                   none
                   { lineno := 85, colOffset := 37, endLineno := 85, endColOffset := 64 }]
               #[]
               none
               { lineno := 85, colOffset := 32, endLineno := 85, endColOffset := 64 })
             { lineno := 85, colOffset := 25, endLineno := 85, endColOffset := 64 })
           (LeanModels.Python.BinOp.add)
           (LeanModels.Python.Expr.tuple
             #[LeanModels.Python.Expr.constant
                 (LeanModels.Python.Const.int 0)
                 { lineno := 85, colOffset := 68, endLineno := 85, endColOffset := 69 }]
             { lineno := 85, colOffset := 67, endLineno := 85, endColOffset := 71 })
           { lineno := 85, colOffset := 25, endLineno := 85, endColOffset := 71 }))
        { lineno := 85, colOffset := 25, endLineno := 85, endColOffset := 71 }]
    [],
  LeanModels.Python.Obj.generator
    "<genexpr@6>"
    [(".0", LeanModels.Python.RVal.rangeV 0 8 1), ("i", LeanModels.Python.RVal.int 7)]
    []
    (LeanModels.Python.GenStatus.closed),
  LeanModels.Python.Obj.generator
    "<genexpr@5>"
    [(".0",
      LeanModels.Python.RVal.tuple
        #[LeanModels.Python.RVal.int (-66), LeanModels.Python.RVal.int (-53), LeanModels.Python.RVal.int (-75),
          LeanModels.Python.RVal.int (-75), LeanModels.Python.RVal.int (-10), LeanModels.Python.RVal.int (-55),
          LeanModels.Python.RVal.int (-58), LeanModels.Python.RVal.int (-70)]),
     ("x", LeanModels.Python.RVal.int (-70))]
    []
    (LeanModels.Python.GenStatus.closed),
  LeanModels.Python.Obj.generator
    "<genexpr@5>"
    [(".0",
      LeanModels.Python.RVal.tuple
        #[LeanModels.Python.RVal.int (-3), LeanModels.Python.RVal.int (-6), LeanModels.Python.RVal.int 100,
          LeanModels.Python.RVal.int (-36), LeanModels.Python.RVal.int 4, LeanModels.Python.RVal.int 62,
          LeanModels.Python.RVal.int (-4), LeanModels.Python.RVal.int (-14)]),
     ("x", LeanModels.Python.RVal.int (-14))]
    []
    (LeanModels.Python.GenStatus.closed),
  LeanModels.Python.Obj.generator
    "<genexpr@5>"
    [(".0",
      LeanModels.Python.RVal.tuple
        #[LeanModels.Python.RVal.int 10, LeanModels.Python.RVal.int 67, LeanModels.Python.RVal.int 1,
          LeanModels.Python.RVal.int 74, LeanModels.Python.RVal.int 73, LeanModels.Python.RVal.int 27,
          LeanModels.Python.RVal.int 62, LeanModels.Python.RVal.int (-2)]),
     ("x", LeanModels.Python.RVal.int (-2))]
    []
    (LeanModels.Python.GenStatus.closed),
  LeanModels.Python.Obj.generator
    "<genexpr@5>"
    [(".0",
      LeanModels.Python.RVal.tuple
        #[LeanModels.Python.RVal.int 24, LeanModels.Python.RVal.int 24, LeanModels.Python.RVal.int 45,
          LeanModels.Python.RVal.int 37, LeanModels.Python.RVal.int 33, LeanModels.Python.RVal.int 41,
          LeanModels.Python.RVal.int 25, LeanModels.Python.RVal.int 17]),
     ("x", LeanModels.Python.RVal.int 17)]
    []
    (LeanModels.Python.GenStatus.closed),
  LeanModels.Python.Obj.generator
    "<genexpr@5>"
    [(".0",
      LeanModels.Python.RVal.tuple
        #[LeanModels.Python.RVal.int (-1), LeanModels.Python.RVal.int 5, LeanModels.Python.RVal.int 31,
          LeanModels.Python.RVal.int 21, LeanModels.Python.RVal.int 22, LeanModels.Python.RVal.int 35,
          LeanModels.Python.RVal.int 2, LeanModels.Python.RVal.int 0]),
     ("x", LeanModels.Python.RVal.int 0)]
    []
    (LeanModels.Python.GenStatus.closed),
  LeanModels.Python.Obj.generator
    "<genexpr@5>"
    [(".0",
      LeanModels.Python.RVal.tuple
        #[LeanModels.Python.RVal.int (-18), LeanModels.Python.RVal.int 10, LeanModels.Python.RVal.int 13,
          LeanModels.Python.RVal.int 22, LeanModels.Python.RVal.int 18, LeanModels.Python.RVal.int 15,
          LeanModels.Python.RVal.int 11, LeanModels.Python.RVal.int (-14)]),
     ("x", LeanModels.Python.RVal.int (-14))]
    []
    (LeanModels.Python.GenStatus.closed),
  LeanModels.Python.Obj.generator
    "<genexpr@5>"
    [(".0",
      LeanModels.Python.RVal.tuple
        #[LeanModels.Python.RVal.int (-23), LeanModels.Python.RVal.int (-15), LeanModels.Python.RVal.int 2,
          LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 2, LeanModels.Python.RVal.int 0,
          LeanModels.Python.RVal.int (-23), LeanModels.Python.RVal.int (-20)]),
     ("x", LeanModels.Python.RVal.int (-20))]
    []
    (LeanModels.Python.GenStatus.closed),
  LeanModels.Python.Obj.generator
    "<genexpr@5>"
    [(".0",
      LeanModels.Python.RVal.tuple
        #[LeanModels.Python.RVal.int (-74), LeanModels.Python.RVal.int (-23), LeanModels.Python.RVal.int (-26),
          LeanModels.Python.RVal.int (-24), LeanModels.Python.RVal.int (-19), LeanModels.Python.RVal.int (-35),
          LeanModels.Python.RVal.int (-22), LeanModels.Python.RVal.int (-69)]),
     ("x", LeanModels.Python.RVal.int (-69))]
    []
    (LeanModels.Python.GenStatus.closed),
  LeanModels.Python.Obj.closure
    "padrow"
    #[{ arg := "row", span := { lineno := 85, colOffset := 20, endLineno := 85, endColOffset := 23 }, default := none }]
    true
    true
    false
    false
    #[LeanModels.Python.Stmt.ret
        (some (LeanModels.Python.Expr.binOp
           (LeanModels.Python.Expr.binOp
             (LeanModels.Python.Expr.tuple
               #[LeanModels.Python.Expr.constant
                   (LeanModels.Python.Const.int 0)
                   { lineno := 85, colOffset := 26, endLineno := 85, endColOffset := 27 }]
               { lineno := 85, colOffset := 25, endLineno := 85, endColOffset := 29 })
             (LeanModels.Python.BinOp.add)
             (LeanModels.Python.Expr.call
               (LeanModels.Python.Expr.name
                 "tuple"
                 { lineno := 85, colOffset := 32, endLineno := 85, endColOffset := 37 })
               #[LeanModels.Python.Expr.call
                   (LeanModels.Python.Expr.name
                     "<genexpr@5>"
                     { lineno := 85, colOffset := 37, endLineno := 85, endColOffset := 64 })
                   #[LeanModels.Python.Expr.name
                       "row"
                       { lineno := 85, colOffset := 60, endLineno := 85, endColOffset := 63 }]
                   #[]
                   none
                   { lineno := 85, colOffset := 37, endLineno := 85, endColOffset := 64 }]
               #[]
               none
               { lineno := 85, colOffset := 32, endLineno := 85, endColOffset := 64 })
             { lineno := 85, colOffset := 25, endLineno := 85, endColOffset := 64 })
           (LeanModels.Python.BinOp.add)
           (LeanModels.Python.Expr.tuple
             #[LeanModels.Python.Expr.constant
                 (LeanModels.Python.Const.int 0)
                 { lineno := 85, colOffset := 68, endLineno := 85, endColOffset := 69 }]
             { lineno := 85, colOffset := 67, endLineno := 85, endColOffset := 71 })
           { lineno := 85, colOffset := 25, endLineno := 85, endColOffset := 71 }))
        { lineno := 85, colOffset := 25, endLineno := 85, endColOffset := 71 }]
    [],
  LeanModels.Python.Obj.generator
    "<genexpr@6>"
    [(".0", LeanModels.Python.RVal.rangeV 0 8 1), ("i", LeanModels.Python.RVal.int 7)]
    []
    (LeanModels.Python.GenStatus.closed),
  LeanModels.Python.Obj.generator
    "<genexpr@5>"
    [(".0",
      LeanModels.Python.RVal.tuple
        #[LeanModels.Python.RVal.int (-59), LeanModels.Python.RVal.int (-78), LeanModels.Python.RVal.int (-82),
          LeanModels.Python.RVal.int (-76), LeanModels.Python.RVal.int (-23), LeanModels.Python.RVal.int (-107),
          LeanModels.Python.RVal.int (-37), LeanModels.Python.RVal.int (-50)]),
     ("x", LeanModels.Python.RVal.int (-50))]
    []
    (LeanModels.Python.GenStatus.closed),
  LeanModels.Python.Obj.generator
    "<genexpr@5>"
    [(".0",
      LeanModels.Python.RVal.tuple
        #[LeanModels.Python.RVal.int (-11), LeanModels.Python.RVal.int 20, LeanModels.Python.RVal.int 35,
          LeanModels.Python.RVal.int (-42), LeanModels.Python.RVal.int (-39), LeanModels.Python.RVal.int 31,
          LeanModels.Python.RVal.int 2, LeanModels.Python.RVal.int (-22)]),
     ("x", LeanModels.Python.RVal.int (-22))]
    []
    (LeanModels.Python.GenStatus.closed),
  LeanModels.Python.Obj.generator
    "<genexpr@5>"
    [(".0",
      LeanModels.Python.RVal.tuple
        #[LeanModels.Python.RVal.int (-9), LeanModels.Python.RVal.int 39, LeanModels.Python.RVal.int (-32),
          LeanModels.Python.RVal.int 41, LeanModels.Python.RVal.int 52, LeanModels.Python.RVal.int (-10),
          LeanModels.Python.RVal.int 28, LeanModels.Python.RVal.int (-14)]),
     ("x", LeanModels.Python.RVal.int (-14))]
    []
    (LeanModels.Python.GenStatus.closed),
  LeanModels.Python.Obj.generator
    "<genexpr@5>"
    [(".0",
      LeanModels.Python.RVal.tuple
        #[LeanModels.Python.RVal.int 25, LeanModels.Python.RVal.int 17, LeanModels.Python.RVal.int 20,
          LeanModels.Python.RVal.int 34, LeanModels.Python.RVal.int 26, LeanModels.Python.RVal.int 25,
          LeanModels.Python.RVal.int 15, LeanModels.Python.RVal.int 10]),
     ("x", LeanModels.Python.RVal.int 10)]
    []
    (LeanModels.Python.GenStatus.closed),
  LeanModels.Python.Obj.generator
    "<genexpr@5>"
    [(".0",
      LeanModels.Python.RVal.tuple
        #[LeanModels.Python.RVal.int 13, LeanModels.Python.RVal.int 10, LeanModels.Python.RVal.int 17,
          LeanModels.Python.RVal.int 23, LeanModels.Python.RVal.int 17, LeanModels.Python.RVal.int 16,
          LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 7]),
     ("x", LeanModels.Python.RVal.int 7)]
    []
    (LeanModels.Python.GenStatus.closed),
  LeanModels.Python.Obj.generator
    "<genexpr@5>"
    [(".0",
      LeanModels.Python.RVal.tuple
        #[LeanModels.Python.RVal.int 14, LeanModels.Python.RVal.int 25, LeanModels.Python.RVal.int 24,
          LeanModels.Python.RVal.int 15, LeanModels.Python.RVal.int 8, LeanModels.Python.RVal.int 25,
          LeanModels.Python.RVal.int 20, LeanModels.Python.RVal.int 15]),
     ("x", LeanModels.Python.RVal.int 15)]
    []
    (LeanModels.Python.GenStatus.closed),
  LeanModels.Python.Obj.generator
    "<genexpr@5>"
    [(".0",
      LeanModels.Python.RVal.tuple
        #[LeanModels.Python.RVal.int 19, LeanModels.Python.RVal.int 20, LeanModels.Python.RVal.int 11,
          LeanModels.Python.RVal.int 6, LeanModels.Python.RVal.int 7, LeanModels.Python.RVal.int 6,
          LeanModels.Python.RVal.int 20, LeanModels.Python.RVal.int 16]),
     ("x", LeanModels.Python.RVal.int 16)]
    []
    (LeanModels.Python.GenStatus.closed),
  LeanModels.Python.Obj.generator
    "<genexpr@5>"
    [(".0",
      LeanModels.Python.RVal.tuple
        #[LeanModels.Python.RVal.int (-7), LeanModels.Python.RVal.int 2, LeanModels.Python.RVal.int (-15),
          LeanModels.Python.RVal.int (-12), LeanModels.Python.RVal.int (-14), LeanModels.Python.RVal.int (-15),
          LeanModels.Python.RVal.int (-10), LeanModels.Python.RVal.int (-10)]),
     ("x", LeanModels.Python.RVal.int (-10))]
    []
    (LeanModels.Python.GenStatus.closed),
  LeanModels.Python.Obj.closure
    "padrow"
    #[{ arg := "row", span := { lineno := 85, colOffset := 20, endLineno := 85, endColOffset := 23 }, default := none }]
    true
    true
    false
    false
    #[LeanModels.Python.Stmt.ret
        (some (LeanModels.Python.Expr.binOp
           (LeanModels.Python.Expr.binOp
             (LeanModels.Python.Expr.tuple
               #[LeanModels.Python.Expr.constant
                   (LeanModels.Python.Const.int 0)
                   { lineno := 85, colOffset := 26, endLineno := 85, endColOffset := 27 }]
               { lineno := 85, colOffset := 25, endLineno := 85, endColOffset := 29 })
             (LeanModels.Python.BinOp.add)
             (LeanModels.Python.Expr.call
               (LeanModels.Python.Expr.name
                 "tuple"
                 { lineno := 85, colOffset := 32, endLineno := 85, endColOffset := 37 })
               #[LeanModels.Python.Expr.call
                   (LeanModels.Python.Expr.name
                     "<genexpr@5>"
                     { lineno := 85, colOffset := 37, endLineno := 85, endColOffset := 64 })
                   #[LeanModels.Python.Expr.name
                       "row"
                       { lineno := 85, colOffset := 60, endLineno := 85, endColOffset := 63 }]
                   #[]
                   none
                   { lineno := 85, colOffset := 37, endLineno := 85, endColOffset := 64 }]
               #[]
               none
               { lineno := 85, colOffset := 32, endLineno := 85, endColOffset := 64 })
             { lineno := 85, colOffset := 25, endLineno := 85, endColOffset := 64 })
           (LeanModels.Python.BinOp.add)
           (LeanModels.Python.Expr.tuple
             #[LeanModels.Python.Expr.constant
                 (LeanModels.Python.Const.int 0)
                 { lineno := 85, colOffset := 68, endLineno := 85, endColOffset := 69 }]
             { lineno := 85, colOffset := 67, endLineno := 85, endColOffset := 71 })
           { lineno := 85, colOffset := 25, endLineno := 85, endColOffset := 71 }))
        { lineno := 85, colOffset := 25, endLineno := 85, endColOffset := 71 }]
    [],
  LeanModels.Python.Obj.generator
    "<genexpr@6>"
    [(".0", LeanModels.Python.RVal.rangeV 0 8 1), ("i", LeanModels.Python.RVal.int 7)]
    []
    (LeanModels.Python.GenStatus.closed),
  LeanModels.Python.Obj.generator
    "<genexpr@5>"
    [(".0",
      LeanModels.Python.RVal.tuple
        #[LeanModels.Python.RVal.int 35, LeanModels.Python.RVal.int 29, LeanModels.Python.RVal.int 33,
          LeanModels.Python.RVal.int 4, LeanModels.Python.RVal.int 37, LeanModels.Python.RVal.int 33,
          LeanModels.Python.RVal.int 56, LeanModels.Python.RVal.int 50]),
     ("x", LeanModels.Python.RVal.int 50)]
    []
    (LeanModels.Python.GenStatus.closed),
  LeanModels.Python.Obj.generator
    "<genexpr@5>"
    [(".0",
      LeanModels.Python.RVal.tuple
        #[LeanModels.Python.RVal.int 55, LeanModels.Python.RVal.int 29, LeanModels.Python.RVal.int 56,
          LeanModels.Python.RVal.int 67, LeanModels.Python.RVal.int 55, LeanModels.Python.RVal.int 62,
          LeanModels.Python.RVal.int 34, LeanModels.Python.RVal.int 60]),
     ("x", LeanModels.Python.RVal.int 60)]
    []
    (LeanModels.Python.GenStatus.closed),
  LeanModels.Python.Obj.generator
    "<genexpr@5>"
    [(".0",
      LeanModels.Python.RVal.tuple
        #[LeanModels.Python.RVal.int 19, LeanModels.Python.RVal.int 35, LeanModels.Python.RVal.int 28,
          LeanModels.Python.RVal.int 33, LeanModels.Python.RVal.int 45, LeanModels.Python.RVal.int 27,
          LeanModels.Python.RVal.int 25, LeanModels.Python.RVal.int 15]),
     ("x", LeanModels.Python.RVal.int 15)]
    []
    (LeanModels.Python.GenStatus.closed),
  LeanModels.Python.Obj.generator
    "<genexpr@5>"
    [(".0",
      LeanModels.Python.RVal.tuple
        #[LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 5, LeanModels.Python.RVal.int 16,
          LeanModels.Python.RVal.int 13, LeanModels.Python.RVal.int 18, LeanModels.Python.RVal.int (-4),
          LeanModels.Python.RVal.int (-9), LeanModels.Python.RVal.int (-6)]),
     ("x", LeanModels.Python.RVal.int (-6))]
    []
    (LeanModels.Python.GenStatus.closed),
  LeanModels.Python.Obj.generator
    "<genexpr@5>"
    [(".0",
      LeanModels.Python.RVal.tuple
        #[LeanModels.Python.RVal.int (-28), LeanModels.Python.RVal.int (-35), LeanModels.Python.RVal.int (-16),
          LeanModels.Python.RVal.int (-21), LeanModels.Python.RVal.int (-13), LeanModels.Python.RVal.int (-29),
          LeanModels.Python.RVal.int (-46), LeanModels.Python.RVal.int (-30)]),
     ("x", LeanModels.Python.RVal.int (-30))]
    []
    (LeanModels.Python.GenStatus.closed),
  LeanModels.Python.Obj.generator
    "<genexpr@5>"
    [(".0",
      LeanModels.Python.RVal.tuple
        #[LeanModels.Python.RVal.int (-42), LeanModels.Python.RVal.int (-28), LeanModels.Python.RVal.int (-42),
          LeanModels.Python.RVal.int (-25), LeanModels.Python.RVal.int (-25), LeanModels.Python.RVal.int (-35),
          LeanModels.Python.RVal.int (-26), LeanModels.Python.RVal.int (-46)]),
     ("x", LeanModels.Python.RVal.int (-46))]
    []
    (LeanModels.Python.GenStatus.closed),
  LeanModels.Python.Obj.generator
    "<genexpr@5>"
    [(".0",
      LeanModels.Python.RVal.tuple
        #[LeanModels.Python.RVal.int (-53), LeanModels.Python.RVal.int (-38), LeanModels.Python.RVal.int (-31),
          LeanModels.Python.RVal.int (-26), LeanModels.Python.RVal.int (-29), LeanModels.Python.RVal.int (-43),
          LeanModels.Python.RVal.int (-44), LeanModels.Python.RVal.int (-53)]),
     ("x", LeanModels.Python.RVal.int (-53))]
    []
    (LeanModels.Python.GenStatus.closed),
  LeanModels.Python.Obj.generator
    "<genexpr@5>"
    [(".0",
      LeanModels.Python.RVal.tuple
        #[LeanModels.Python.RVal.int (-30), LeanModels.Python.RVal.int (-24), LeanModels.Python.RVal.int (-18),
          LeanModels.Python.RVal.int 5, LeanModels.Python.RVal.int (-2), LeanModels.Python.RVal.int (-18),
          LeanModels.Python.RVal.int (-31), LeanModels.Python.RVal.int (-32)]),
     ("x", LeanModels.Python.RVal.int (-32))]
    []
    (LeanModels.Python.GenStatus.closed),
  LeanModels.Python.Obj.closure
    "padrow"
    #[{ arg := "row", span := { lineno := 85, colOffset := 20, endLineno := 85, endColOffset := 23 }, default := none }]
    true
    true
    false
    false
    #[LeanModels.Python.Stmt.ret
        (some (LeanModels.Python.Expr.binOp
           (LeanModels.Python.Expr.binOp
             (LeanModels.Python.Expr.tuple
               #[LeanModels.Python.Expr.constant
                   (LeanModels.Python.Const.int 0)
                   { lineno := 85, colOffset := 26, endLineno := 85, endColOffset := 27 }]
               { lineno := 85, colOffset := 25, endLineno := 85, endColOffset := 29 })
             (LeanModels.Python.BinOp.add)
             (LeanModels.Python.Expr.call
               (LeanModels.Python.Expr.name
                 "tuple"
                 { lineno := 85, colOffset := 32, endLineno := 85, endColOffset := 37 })
               #[LeanModels.Python.Expr.call
                   (LeanModels.Python.Expr.name
                     "<genexpr@5>"
                     { lineno := 85, colOffset := 37, endLineno := 85, endColOffset := 64 })
                   #[LeanModels.Python.Expr.name
                       "row"
                       { lineno := 85, colOffset := 60, endLineno := 85, endColOffset := 63 }]
                   #[]
                   none
                   { lineno := 85, colOffset := 37, endLineno := 85, endColOffset := 64 }]
               #[]
               none
               { lineno := 85, colOffset := 32, endLineno := 85, endColOffset := 64 })
             { lineno := 85, colOffset := 25, endLineno := 85, endColOffset := 64 })
           (LeanModels.Python.BinOp.add)
           (LeanModels.Python.Expr.tuple
             #[LeanModels.Python.Expr.constant
                 (LeanModels.Python.Const.int 0)
                 { lineno := 85, colOffset := 68, endLineno := 85, endColOffset := 69 }]
             { lineno := 85, colOffset := 67, endLineno := 85, endColOffset := 71 })
           { lineno := 85, colOffset := 25, endLineno := 85, endColOffset := 71 }))
        { lineno := 85, colOffset := 25, endLineno := 85, endColOffset := 71 }]
    [],
  LeanModels.Python.Obj.generator
    "<genexpr@6>"
    [(".0", LeanModels.Python.RVal.rangeV 0 8 1), ("i", LeanModels.Python.RVal.int 7)]
    []
    (LeanModels.Python.GenStatus.closed),
  LeanModels.Python.Obj.generator
    "<genexpr@5>"
    [(".0",
      LeanModels.Python.RVal.tuple
        #[LeanModels.Python.RVal.int 6, LeanModels.Python.RVal.int 1, LeanModels.Python.RVal.int (-8),
          LeanModels.Python.RVal.int (-104), LeanModels.Python.RVal.int 69, LeanModels.Python.RVal.int 24,
          LeanModels.Python.RVal.int 88, LeanModels.Python.RVal.int 26]),
     ("x", LeanModels.Python.RVal.int 26)]
    []
    (LeanModels.Python.GenStatus.closed),
  LeanModels.Python.Obj.generator
    "<genexpr@5>"
    [(".0",
      LeanModels.Python.RVal.tuple
        #[LeanModels.Python.RVal.int 14, LeanModels.Python.RVal.int 32, LeanModels.Python.RVal.int 60,
          LeanModels.Python.RVal.int (-10), LeanModels.Python.RVal.int 20, LeanModels.Python.RVal.int 76,
          LeanModels.Python.RVal.int 57, LeanModels.Python.RVal.int 24]),
     ("x", LeanModels.Python.RVal.int 24)]
    []
    (LeanModels.Python.GenStatus.closed),
  LeanModels.Python.Obj.generator
    "<genexpr@5>"
    [(".0",
      LeanModels.Python.RVal.tuple
        #[LeanModels.Python.RVal.int (-2), LeanModels.Python.RVal.int 43, LeanModels.Python.RVal.int 32,
          LeanModels.Python.RVal.int 60, LeanModels.Python.RVal.int 72, LeanModels.Python.RVal.int 63,
          LeanModels.Python.RVal.int 43, LeanModels.Python.RVal.int 2]),
     ("x", LeanModels.Python.RVal.int 2)]
    []
    (LeanModels.Python.GenStatus.closed),
  LeanModels.Python.Obj.generator
    "<genexpr@5>"
    [(".0",
      LeanModels.Python.RVal.tuple
        #[LeanModels.Python.RVal.int 1, LeanModels.Python.RVal.int (-16), LeanModels.Python.RVal.int 22,
          LeanModels.Python.RVal.int 17, LeanModels.Python.RVal.int 25, LeanModels.Python.RVal.int 20,
          LeanModels.Python.RVal.int (-13), LeanModels.Python.RVal.int (-6)]),
     ("x", LeanModels.Python.RVal.int (-6))]
    []
    (LeanModels.Python.GenStatus.closed),
  LeanModels.Python.Obj.generator
    "<genexpr@5>"
    [(".0",
      LeanModels.Python.RVal.tuple
        #[LeanModels.Python.RVal.int (-14), LeanModels.Python.RVal.int (-15), LeanModels.Python.RVal.int (-2),
          LeanModels.Python.RVal.int (-5), LeanModels.Python.RVal.int (-1), LeanModels.Python.RVal.int (-10),
          LeanModels.Python.RVal.int (-20), LeanModels.Python.RVal.int (-22)]),
     ("x", LeanModels.Python.RVal.int (-22))]
    []
    (LeanModels.Python.GenStatus.closed),
  LeanModels.Python.Obj.generator
    "<genexpr@5>"
    [(".0",
      LeanModels.Python.RVal.tuple
        #[LeanModels.Python.RVal.int (-30), LeanModels.Python.RVal.int (-6), LeanModels.Python.RVal.int (-13),
          LeanModels.Python.RVal.int (-11), LeanModels.Python.RVal.int (-16), LeanModels.Python.RVal.int (-11),
          LeanModels.Python.RVal.int (-16), LeanModels.Python.RVal.int (-27)]),
     ("x", LeanModels.Python.RVal.int (-27))]
    []
    (LeanModels.Python.GenStatus.closed),
  LeanModels.Python.Obj.generator
    "<genexpr@5>"
    [(".0",
      LeanModels.Python.RVal.tuple
        #[LeanModels.Python.RVal.int (-36), LeanModels.Python.RVal.int (-18), LeanModels.Python.RVal.int 0,
          LeanModels.Python.RVal.int (-19), LeanModels.Python.RVal.int (-15), LeanModels.Python.RVal.int (-15),
          LeanModels.Python.RVal.int (-21), LeanModels.Python.RVal.int (-38)]),
     ("x", LeanModels.Python.RVal.int (-38))]
    []
    (LeanModels.Python.GenStatus.closed),
  LeanModels.Python.Obj.generator
    "<genexpr@5>"
    [(".0",
      LeanModels.Python.RVal.tuple
        #[LeanModels.Python.RVal.int (-39), LeanModels.Python.RVal.int (-30), LeanModels.Python.RVal.int (-31),
          LeanModels.Python.RVal.int (-13), LeanModels.Python.RVal.int (-31), LeanModels.Python.RVal.int (-36),
          LeanModels.Python.RVal.int (-34), LeanModels.Python.RVal.int (-42)]),
     ("x", LeanModels.Python.RVal.int (-42))]
    []
    (LeanModels.Python.GenStatus.closed),
  LeanModels.Python.Obj.closure
    "padrow"
    #[{ arg := "row", span := { lineno := 85, colOffset := 20, endLineno := 85, endColOffset := 23 }, default := none }]
    true
    true
    false
    false
    #[LeanModels.Python.Stmt.ret
        (some (LeanModels.Python.Expr.binOp
           (LeanModels.Python.Expr.binOp
             (LeanModels.Python.Expr.tuple
               #[LeanModels.Python.Expr.constant
                   (LeanModels.Python.Const.int 0)
                   { lineno := 85, colOffset := 26, endLineno := 85, endColOffset := 27 }]
               { lineno := 85, colOffset := 25, endLineno := 85, endColOffset := 29 })
             (LeanModels.Python.BinOp.add)
             (LeanModels.Python.Expr.call
               (LeanModels.Python.Expr.name
                 "tuple"
                 { lineno := 85, colOffset := 32, endLineno := 85, endColOffset := 37 })
               #[LeanModels.Python.Expr.call
                   (LeanModels.Python.Expr.name
                     "<genexpr@5>"
                     { lineno := 85, colOffset := 37, endLineno := 85, endColOffset := 64 })
                   #[LeanModels.Python.Expr.name
                       "row"
                       { lineno := 85, colOffset := 60, endLineno := 85, endColOffset := 63 }]
                   #[]
                   none
                   { lineno := 85, colOffset := 37, endLineno := 85, endColOffset := 64 }]
               #[]
               none
               { lineno := 85, colOffset := 32, endLineno := 85, endColOffset := 64 })
             { lineno := 85, colOffset := 25, endLineno := 85, endColOffset := 64 })
           (LeanModels.Python.BinOp.add)
           (LeanModels.Python.Expr.tuple
             #[LeanModels.Python.Expr.constant
                 (LeanModels.Python.Const.int 0)
                 { lineno := 85, colOffset := 68, endLineno := 85, endColOffset := 69 }]
             { lineno := 85, colOffset := 67, endLineno := 85, endColOffset := 71 })
           { lineno := 85, colOffset := 25, endLineno := 85, endColOffset := 71 }))
        { lineno := 85, colOffset := 25, endLineno := 85, endColOffset := 71 }]
    [],
  LeanModels.Python.Obj.generator
    "<genexpr@6>"
    [(".0", LeanModels.Python.RVal.rangeV 0 8 1), ("i", LeanModels.Python.RVal.int 7)]
    []
    (LeanModels.Python.GenStatus.closed),
  LeanModels.Python.Obj.generator
    "<genexpr@5>"
    [(".0",
      LeanModels.Python.RVal.tuple
        #[LeanModels.Python.RVal.int 4, LeanModels.Python.RVal.int 54, LeanModels.Python.RVal.int 47,
          LeanModels.Python.RVal.int (-99), LeanModels.Python.RVal.int (-99), LeanModels.Python.RVal.int 60,
          LeanModels.Python.RVal.int 83, LeanModels.Python.RVal.int (-62)]),
     ("x", LeanModels.Python.RVal.int (-62))]
    []
    (LeanModels.Python.GenStatus.closed),
  LeanModels.Python.Obj.generator
    "<genexpr@5>"
    [(".0",
      LeanModels.Python.RVal.tuple
        #[LeanModels.Python.RVal.int (-32), LeanModels.Python.RVal.int 10, LeanModels.Python.RVal.int 55,
          LeanModels.Python.RVal.int 56, LeanModels.Python.RVal.int 56, LeanModels.Python.RVal.int 55,
          LeanModels.Python.RVal.int 10, LeanModels.Python.RVal.int 3]),
     ("x", LeanModels.Python.RVal.int 3)]
    []
    (LeanModels.Python.GenStatus.closed),
  LeanModels.Python.Obj.generator
    "<genexpr@5>"
    [(".0",
      LeanModels.Python.RVal.tuple
        #[LeanModels.Python.RVal.int (-62), LeanModels.Python.RVal.int 12, LeanModels.Python.RVal.int (-57),
          LeanModels.Python.RVal.int 44, LeanModels.Python.RVal.int (-67), LeanModels.Python.RVal.int 28,
          LeanModels.Python.RVal.int 37, LeanModels.Python.RVal.int (-31)]),
     ("x", LeanModels.Python.RVal.int (-31))]
    []
    (LeanModels.Python.GenStatus.closed),
  LeanModels.Python.Obj.generator
    "<genexpr@5>"
    [(".0",
      LeanModels.Python.RVal.tuple
        #[LeanModels.Python.RVal.int (-55), LeanModels.Python.RVal.int 50, LeanModels.Python.RVal.int 11,
          LeanModels.Python.RVal.int (-4), LeanModels.Python.RVal.int (-19), LeanModels.Python.RVal.int 13,
          LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int (-49)]),
     ("x", LeanModels.Python.RVal.int (-49))]
    []
    (LeanModels.Python.GenStatus.closed),
  LeanModels.Python.Obj.generator
    "<genexpr@5>"
    [(".0",
      LeanModels.Python.RVal.tuple
        #[LeanModels.Python.RVal.int (-55), LeanModels.Python.RVal.int (-43), LeanModels.Python.RVal.int (-52),
          LeanModels.Python.RVal.int (-28), LeanModels.Python.RVal.int (-51), LeanModels.Python.RVal.int (-47),
          LeanModels.Python.RVal.int (-8), LeanModels.Python.RVal.int (-50)]),
     ("x", LeanModels.Python.RVal.int (-50))]
    []
    (LeanModels.Python.GenStatus.closed),
  LeanModels.Python.Obj.generator
    "<genexpr@5>"
    [(".0",
      LeanModels.Python.RVal.tuple
        #[LeanModels.Python.RVal.int (-47), LeanModels.Python.RVal.int (-42), LeanModels.Python.RVal.int (-43),
          LeanModels.Python.RVal.int (-79), LeanModels.Python.RVal.int (-64), LeanModels.Python.RVal.int (-32),
          LeanModels.Python.RVal.int (-29), LeanModels.Python.RVal.int (-32)]),
     ("x", LeanModels.Python.RVal.int (-32))]
    []
    (LeanModels.Python.GenStatus.closed),
  LeanModels.Python.Obj.generator
    "<genexpr@5>"
    [(".0",
      LeanModels.Python.RVal.tuple
        #[LeanModels.Python.RVal.int (-4), LeanModels.Python.RVal.int 3, LeanModels.Python.RVal.int (-14),
          LeanModels.Python.RVal.int (-50), LeanModels.Python.RVal.int (-57), LeanModels.Python.RVal.int (-18),
          LeanModels.Python.RVal.int 13, LeanModels.Python.RVal.int 4]),
     ("x", LeanModels.Python.RVal.int 4)]
    []
    (LeanModels.Python.GenStatus.closed),
  LeanModels.Python.Obj.generator
    "<genexpr@5>"
    [(".0",
      LeanModels.Python.RVal.tuple
        #[LeanModels.Python.RVal.int 17, LeanModels.Python.RVal.int 30, LeanModels.Python.RVal.int (-3),
          LeanModels.Python.RVal.int (-14), LeanModels.Python.RVal.int 6, LeanModels.Python.RVal.int (-1),
          LeanModels.Python.RVal.int 40, LeanModels.Python.RVal.int 18]),
     ("x", LeanModels.Python.RVal.int 18)]
    []
    (LeanModels.Python.GenStatus.closed),
  LeanModels.Python.Obj.generator
    "<genexpr@7>"
    [(".0", LeanModels.Python.RVal.rangeV 0 120 1), ("i", LeanModels.Python.RVal.int 119)]
    []
    (LeanModels.Python.GenStatus.closed)]

def acc9 : GlobalsAcc :=
  [("K_END",
  some (LeanModels.Python.RVal.tuple
    #[LeanModels.Python.RVal.int 59870, LeanModels.Python.RVal.int 59890, LeanModels.Python.RVal.int 59910,
      LeanModels.Python.RVal.int 59930, LeanModels.Python.RVal.int 59950, LeanModels.Python.RVal.int 59950,
      LeanModels.Python.RVal.int 59930, LeanModels.Python.RVal.int 59910, LeanModels.Python.RVal.int 59890,
      LeanModels.Python.RVal.int 59870, LeanModels.Python.RVal.int 59890, LeanModels.Python.RVal.int 59910,
      LeanModels.Python.RVal.int 59930, LeanModels.Python.RVal.int 59950, LeanModels.Python.RVal.int 59970,
      LeanModels.Python.RVal.int 59970, LeanModels.Python.RVal.int 59950, LeanModels.Python.RVal.int 59930,
      LeanModels.Python.RVal.int 59910, LeanModels.Python.RVal.int 59890, LeanModels.Python.RVal.int 59910,
      LeanModels.Python.RVal.int 59930, LeanModels.Python.RVal.int 59950, LeanModels.Python.RVal.int 59970,
      LeanModels.Python.RVal.int 59990, LeanModels.Python.RVal.int 59990, LeanModels.Python.RVal.int 59970,
      LeanModels.Python.RVal.int 59950, LeanModels.Python.RVal.int 59930, LeanModels.Python.RVal.int 59910,
      LeanModels.Python.RVal.int 59930, LeanModels.Python.RVal.int 59950, LeanModels.Python.RVal.int 59970,
      LeanModels.Python.RVal.int 59990, LeanModels.Python.RVal.int 60010, LeanModels.Python.RVal.int 60010,
      LeanModels.Python.RVal.int 59990, LeanModels.Python.RVal.int 59970, LeanModels.Python.RVal.int 59950,
      LeanModels.Python.RVal.int 59930, LeanModels.Python.RVal.int 59950, LeanModels.Python.RVal.int 59970,
      LeanModels.Python.RVal.int 59990, LeanModels.Python.RVal.int 60010, LeanModels.Python.RVal.int 60030,
      LeanModels.Python.RVal.int 60030, LeanModels.Python.RVal.int 60010, LeanModels.Python.RVal.int 59990,
      LeanModels.Python.RVal.int 59970, LeanModels.Python.RVal.int 59950, LeanModels.Python.RVal.int 59970,
      LeanModels.Python.RVal.int 59990, LeanModels.Python.RVal.int 60010, LeanModels.Python.RVal.int 60030,
      LeanModels.Python.RVal.int 60050, LeanModels.Python.RVal.int 60050, LeanModels.Python.RVal.int 60030,
      LeanModels.Python.RVal.int 60010, LeanModels.Python.RVal.int 59990, LeanModels.Python.RVal.int 59970,
      LeanModels.Python.RVal.int 59970, LeanModels.Python.RVal.int 59990, LeanModels.Python.RVal.int 60010,
      LeanModels.Python.RVal.int 60030, LeanModels.Python.RVal.int 60050, LeanModels.Python.RVal.int 60050,
      LeanModels.Python.RVal.int 60030, LeanModels.Python.RVal.int 60010, LeanModels.Python.RVal.int 59990,
      LeanModels.Python.RVal.int 59970, LeanModels.Python.RVal.int 59950, LeanModels.Python.RVal.int 59970,
      LeanModels.Python.RVal.int 59990, LeanModels.Python.RVal.int 60010, LeanModels.Python.RVal.int 60030,
      LeanModels.Python.RVal.int 60030, LeanModels.Python.RVal.int 60010, LeanModels.Python.RVal.int 59990,
      LeanModels.Python.RVal.int 59970, LeanModels.Python.RVal.int 59950, LeanModels.Python.RVal.int 59930,
      LeanModels.Python.RVal.int 59950, LeanModels.Python.RVal.int 59970, LeanModels.Python.RVal.int 59990,
      LeanModels.Python.RVal.int 60010, LeanModels.Python.RVal.int 60010, LeanModels.Python.RVal.int 59990,
      LeanModels.Python.RVal.int 59970, LeanModels.Python.RVal.int 59950, LeanModels.Python.RVal.int 59930,
      LeanModels.Python.RVal.int 59910, LeanModels.Python.RVal.int 59930, LeanModels.Python.RVal.int 59950,
      LeanModels.Python.RVal.int 59970, LeanModels.Python.RVal.int 59990, LeanModels.Python.RVal.int 59990,
      LeanModels.Python.RVal.int 59970, LeanModels.Python.RVal.int 59950, LeanModels.Python.RVal.int 59930,
      LeanModels.Python.RVal.int 59910, LeanModels.Python.RVal.int 59890, LeanModels.Python.RVal.int 59910,
      LeanModels.Python.RVal.int 59930, LeanModels.Python.RVal.int 59950, LeanModels.Python.RVal.int 59970,
      LeanModels.Python.RVal.int 59970, LeanModels.Python.RVal.int 59950, LeanModels.Python.RVal.int 59930,
      LeanModels.Python.RVal.int 59910, LeanModels.Python.RVal.int 59890, LeanModels.Python.RVal.int 59870,
      LeanModels.Python.RVal.int 59890, LeanModels.Python.RVal.int 59910, LeanModels.Python.RVal.int 59930,
      LeanModels.Python.RVal.int 59950, LeanModels.Python.RVal.int 59950, LeanModels.Python.RVal.int 59930,
      LeanModels.Python.RVal.int 59910, LeanModels.Python.RVal.int 59890, LeanModels.Python.RVal.int 59870])),
 ("K_MID",
  some (LeanModels.Python.RVal.tuple
    #[LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
      LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
      LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
      LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
      LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
      LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
      LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
      LeanModels.Python.RVal.int 60004, LeanModels.Python.RVal.int 60054, LeanModels.Python.RVal.int 60047,
      LeanModels.Python.RVal.int 59901, LeanModels.Python.RVal.int 59901, LeanModels.Python.RVal.int 60060,
      LeanModels.Python.RVal.int 60083, LeanModels.Python.RVal.int 59938, LeanModels.Python.RVal.int 0,
      LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 59968, LeanModels.Python.RVal.int 60010,
      LeanModels.Python.RVal.int 60055, LeanModels.Python.RVal.int 60056, LeanModels.Python.RVal.int 60056,
      LeanModels.Python.RVal.int 60055, LeanModels.Python.RVal.int 60010, LeanModels.Python.RVal.int 60003,
      LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 59938,
      LeanModels.Python.RVal.int 60012, LeanModels.Python.RVal.int 59943, LeanModels.Python.RVal.int 60044,
      LeanModels.Python.RVal.int 59933, LeanModels.Python.RVal.int 60028, LeanModels.Python.RVal.int 60037,
      LeanModels.Python.RVal.int 59969, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
      LeanModels.Python.RVal.int 59945, LeanModels.Python.RVal.int 60050, LeanModels.Python.RVal.int 60011,
      LeanModels.Python.RVal.int 59996, LeanModels.Python.RVal.int 59981, LeanModels.Python.RVal.int 60013,
      LeanModels.Python.RVal.int 60000, LeanModels.Python.RVal.int 59951, LeanModels.Python.RVal.int 0,
      LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 59945, LeanModels.Python.RVal.int 59957,
      LeanModels.Python.RVal.int 59948, LeanModels.Python.RVal.int 59972, LeanModels.Python.RVal.int 59949,
      LeanModels.Python.RVal.int 59953, LeanModels.Python.RVal.int 59992, LeanModels.Python.RVal.int 59950,
      LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 59953,
      LeanModels.Python.RVal.int 59958, LeanModels.Python.RVal.int 59957, LeanModels.Python.RVal.int 59921,
      LeanModels.Python.RVal.int 59936, LeanModels.Python.RVal.int 59968, LeanModels.Python.RVal.int 59971,
      LeanModels.Python.RVal.int 59968, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
      LeanModels.Python.RVal.int 59996, LeanModels.Python.RVal.int 60003, LeanModels.Python.RVal.int 59986,
      LeanModels.Python.RVal.int 59950, LeanModels.Python.RVal.int 59943, LeanModels.Python.RVal.int 59982,
      LeanModels.Python.RVal.int 60013, LeanModels.Python.RVal.int 60004, LeanModels.Python.RVal.int 0,
      LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 60017, LeanModels.Python.RVal.int 60030,
      LeanModels.Python.RVal.int 59997, LeanModels.Python.RVal.int 59986, LeanModels.Python.RVal.int 60006,
      LeanModels.Python.RVal.int 59999, LeanModels.Python.RVal.int 60040, LeanModels.Python.RVal.int 60018,
      LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
      LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
      LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
      LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
      LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
      LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
      LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0])),
 ("padrow", some (LeanModels.Python.RVal.ref 52)),
 ("table",
  some (LeanModels.Python.RVal.tuple
    #[LeanModels.Python.RVal.int 4, LeanModels.Python.RVal.int 54, LeanModels.Python.RVal.int 47,
      LeanModels.Python.RVal.int (-99), LeanModels.Python.RVal.int (-99), LeanModels.Python.RVal.int 60,
      LeanModels.Python.RVal.int 83, LeanModels.Python.RVal.int (-62), LeanModels.Python.RVal.int (-32),
      LeanModels.Python.RVal.int 10, LeanModels.Python.RVal.int 55, LeanModels.Python.RVal.int 56,
      LeanModels.Python.RVal.int 56, LeanModels.Python.RVal.int 55, LeanModels.Python.RVal.int 10,
      LeanModels.Python.RVal.int 3, LeanModels.Python.RVal.int (-62), LeanModels.Python.RVal.int 12,
      LeanModels.Python.RVal.int (-57), LeanModels.Python.RVal.int 44, LeanModels.Python.RVal.int (-67),
      LeanModels.Python.RVal.int 28, LeanModels.Python.RVal.int 37, LeanModels.Python.RVal.int (-31),
      LeanModels.Python.RVal.int (-55), LeanModels.Python.RVal.int 50, LeanModels.Python.RVal.int 11,
      LeanModels.Python.RVal.int (-4), LeanModels.Python.RVal.int (-19), LeanModels.Python.RVal.int 13,
      LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int (-49), LeanModels.Python.RVal.int (-55),
      LeanModels.Python.RVal.int (-43), LeanModels.Python.RVal.int (-52), LeanModels.Python.RVal.int (-28),
      LeanModels.Python.RVal.int (-51), LeanModels.Python.RVal.int (-47), LeanModels.Python.RVal.int (-8),
      LeanModels.Python.RVal.int (-50), LeanModels.Python.RVal.int (-47), LeanModels.Python.RVal.int (-42),
      LeanModels.Python.RVal.int (-43), LeanModels.Python.RVal.int (-79), LeanModels.Python.RVal.int (-64),
      LeanModels.Python.RVal.int (-32), LeanModels.Python.RVal.int (-29), LeanModels.Python.RVal.int (-32),
      LeanModels.Python.RVal.int (-4), LeanModels.Python.RVal.int 3, LeanModels.Python.RVal.int (-14),
      LeanModels.Python.RVal.int (-50), LeanModels.Python.RVal.int (-57), LeanModels.Python.RVal.int (-18),
      LeanModels.Python.RVal.int 13, LeanModels.Python.RVal.int 4, LeanModels.Python.RVal.int 17,
      LeanModels.Python.RVal.int 30, LeanModels.Python.RVal.int (-3), LeanModels.Python.RVal.int (-14),
      LeanModels.Python.RVal.int 6, LeanModels.Python.RVal.int (-1), LeanModels.Python.RVal.int 40,
      LeanModels.Python.RVal.int 18])),
 ("k", some (LeanModels.Python.RVal.str "K")),
 ("padrow", some (LeanModels.Python.RVal.ref 42)),
 ("table",
  some (LeanModels.Python.RVal.tuple
    #[LeanModels.Python.RVal.int 6, LeanModels.Python.RVal.int 1, LeanModels.Python.RVal.int (-8),
      LeanModels.Python.RVal.int (-104), LeanModels.Python.RVal.int 69, LeanModels.Python.RVal.int 24,
      LeanModels.Python.RVal.int 88, LeanModels.Python.RVal.int 26, LeanModels.Python.RVal.int 14,
      LeanModels.Python.RVal.int 32, LeanModels.Python.RVal.int 60, LeanModels.Python.RVal.int (-10),
      LeanModels.Python.RVal.int 20, LeanModels.Python.RVal.int 76, LeanModels.Python.RVal.int 57,
      LeanModels.Python.RVal.int 24, LeanModels.Python.RVal.int (-2), LeanModels.Python.RVal.int 43,
      LeanModels.Python.RVal.int 32, LeanModels.Python.RVal.int 60, LeanModels.Python.RVal.int 72,
      LeanModels.Python.RVal.int 63, LeanModels.Python.RVal.int 43, LeanModels.Python.RVal.int 2,
      LeanModels.Python.RVal.int 1, LeanModels.Python.RVal.int (-16), LeanModels.Python.RVal.int 22,
      LeanModels.Python.RVal.int 17, LeanModels.Python.RVal.int 25, LeanModels.Python.RVal.int 20,
      LeanModels.Python.RVal.int (-13), LeanModels.Python.RVal.int (-6), LeanModels.Python.RVal.int (-14),
      LeanModels.Python.RVal.int (-15), LeanModels.Python.RVal.int (-2), LeanModels.Python.RVal.int (-5),
      LeanModels.Python.RVal.int (-1), LeanModels.Python.RVal.int (-10), LeanModels.Python.RVal.int (-20),
      LeanModels.Python.RVal.int (-22), LeanModels.Python.RVal.int (-30), LeanModels.Python.RVal.int (-6),
      LeanModels.Python.RVal.int (-13), LeanModels.Python.RVal.int (-11), LeanModels.Python.RVal.int (-16),
      LeanModels.Python.RVal.int (-11), LeanModels.Python.RVal.int (-16), LeanModels.Python.RVal.int (-27),
      LeanModels.Python.RVal.int (-36), LeanModels.Python.RVal.int (-18), LeanModels.Python.RVal.int 0,
      LeanModels.Python.RVal.int (-19), LeanModels.Python.RVal.int (-15), LeanModels.Python.RVal.int (-15),
      LeanModels.Python.RVal.int (-21), LeanModels.Python.RVal.int (-38), LeanModels.Python.RVal.int (-39),
      LeanModels.Python.RVal.int (-30), LeanModels.Python.RVal.int (-31), LeanModels.Python.RVal.int (-13),
      LeanModels.Python.RVal.int (-31), LeanModels.Python.RVal.int (-36), LeanModels.Python.RVal.int (-34),
      LeanModels.Python.RVal.int (-42)])),
 ("k", some (LeanModels.Python.RVal.str "Q")),
 ("padrow", some (LeanModels.Python.RVal.ref 32)),
 ("table",
  some (LeanModels.Python.RVal.tuple
    #[LeanModels.Python.RVal.int 35, LeanModels.Python.RVal.int 29, LeanModels.Python.RVal.int 33,
      LeanModels.Python.RVal.int 4, LeanModels.Python.RVal.int 37, LeanModels.Python.RVal.int 33,
      LeanModels.Python.RVal.int 56, LeanModels.Python.RVal.int 50, LeanModels.Python.RVal.int 55,
      LeanModels.Python.RVal.int 29, LeanModels.Python.RVal.int 56, LeanModels.Python.RVal.int 67,
      LeanModels.Python.RVal.int 55, LeanModels.Python.RVal.int 62, LeanModels.Python.RVal.int 34,
      LeanModels.Python.RVal.int 60, LeanModels.Python.RVal.int 19, LeanModels.Python.RVal.int 35,
      LeanModels.Python.RVal.int 28, LeanModels.Python.RVal.int 33, LeanModels.Python.RVal.int 45,
      LeanModels.Python.RVal.int 27, LeanModels.Python.RVal.int 25, LeanModels.Python.RVal.int 15,
      LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 5, LeanModels.Python.RVal.int 16,
      LeanModels.Python.RVal.int 13, LeanModels.Python.RVal.int 18, LeanModels.Python.RVal.int (-4),
      LeanModels.Python.RVal.int (-9), LeanModels.Python.RVal.int (-6), LeanModels.Python.RVal.int (-28),
      LeanModels.Python.RVal.int (-35), LeanModels.Python.RVal.int (-16), LeanModels.Python.RVal.int (-21),
      LeanModels.Python.RVal.int (-13), LeanModels.Python.RVal.int (-29), LeanModels.Python.RVal.int (-46),
      LeanModels.Python.RVal.int (-30), LeanModels.Python.RVal.int (-42), LeanModels.Python.RVal.int (-28),
      LeanModels.Python.RVal.int (-42), LeanModels.Python.RVal.int (-25), LeanModels.Python.RVal.int (-25),
      LeanModels.Python.RVal.int (-35), LeanModels.Python.RVal.int (-26), LeanModels.Python.RVal.int (-46),
      LeanModels.Python.RVal.int (-53), LeanModels.Python.RVal.int (-38), LeanModels.Python.RVal.int (-31),
      LeanModels.Python.RVal.int (-26), LeanModels.Python.RVal.int (-29), LeanModels.Python.RVal.int (-43),
      LeanModels.Python.RVal.int (-44), LeanModels.Python.RVal.int (-53), LeanModels.Python.RVal.int (-30),
      LeanModels.Python.RVal.int (-24), LeanModels.Python.RVal.int (-18), LeanModels.Python.RVal.int 5,
      LeanModels.Python.RVal.int (-2), LeanModels.Python.RVal.int (-18), LeanModels.Python.RVal.int (-31),
      LeanModels.Python.RVal.int (-32)])),
 ("k", some (LeanModels.Python.RVal.str "R")),
 ("padrow", some (LeanModels.Python.RVal.ref 22)),
 ("table",
  some (LeanModels.Python.RVal.tuple
    #[LeanModels.Python.RVal.int (-59), LeanModels.Python.RVal.int (-78), LeanModels.Python.RVal.int (-82),
      LeanModels.Python.RVal.int (-76), LeanModels.Python.RVal.int (-23), LeanModels.Python.RVal.int (-107),
      LeanModels.Python.RVal.int (-37), LeanModels.Python.RVal.int (-50), LeanModels.Python.RVal.int (-11),
      LeanModels.Python.RVal.int 20, LeanModels.Python.RVal.int 35, LeanModels.Python.RVal.int (-42),
      LeanModels.Python.RVal.int (-39), LeanModels.Python.RVal.int 31, LeanModels.Python.RVal.int 2,
      LeanModels.Python.RVal.int (-22), LeanModels.Python.RVal.int (-9), LeanModels.Python.RVal.int 39,
      LeanModels.Python.RVal.int (-32), LeanModels.Python.RVal.int 41, LeanModels.Python.RVal.int 52,
      LeanModels.Python.RVal.int (-10), LeanModels.Python.RVal.int 28, LeanModels.Python.RVal.int (-14),
      LeanModels.Python.RVal.int 25, LeanModels.Python.RVal.int 17, LeanModels.Python.RVal.int 20,
      LeanModels.Python.RVal.int 34, LeanModels.Python.RVal.int 26, LeanModels.Python.RVal.int 25,
      LeanModels.Python.RVal.int 15, LeanModels.Python.RVal.int 10, LeanModels.Python.RVal.int 13,
      LeanModels.Python.RVal.int 10, LeanModels.Python.RVal.int 17, LeanModels.Python.RVal.int 23,
      LeanModels.Python.RVal.int 17, LeanModels.Python.RVal.int 16, LeanModels.Python.RVal.int 0,
      LeanModels.Python.RVal.int 7, LeanModels.Python.RVal.int 14, LeanModels.Python.RVal.int 25,
      LeanModels.Python.RVal.int 24, LeanModels.Python.RVal.int 15, LeanModels.Python.RVal.int 8,
      LeanModels.Python.RVal.int 25, LeanModels.Python.RVal.int 20, LeanModels.Python.RVal.int 15,
      LeanModels.Python.RVal.int 19, LeanModels.Python.RVal.int 20, LeanModels.Python.RVal.int 11,
      LeanModels.Python.RVal.int 6, LeanModels.Python.RVal.int 7, LeanModels.Python.RVal.int 6,
      LeanModels.Python.RVal.int 20, LeanModels.Python.RVal.int 16, LeanModels.Python.RVal.int (-7),
      LeanModels.Python.RVal.int 2, LeanModels.Python.RVal.int (-15), LeanModels.Python.RVal.int (-12),
      LeanModels.Python.RVal.int (-14), LeanModels.Python.RVal.int (-15), LeanModels.Python.RVal.int (-10),
      LeanModels.Python.RVal.int (-10)])),
 ("k", some (LeanModels.Python.RVal.str "B")),
 ("padrow", some (LeanModels.Python.RVal.ref 12)),
 ("table",
  some (LeanModels.Python.RVal.tuple
    #[LeanModels.Python.RVal.int (-66), LeanModels.Python.RVal.int (-53), LeanModels.Python.RVal.int (-75),
      LeanModels.Python.RVal.int (-75), LeanModels.Python.RVal.int (-10), LeanModels.Python.RVal.int (-55),
      LeanModels.Python.RVal.int (-58), LeanModels.Python.RVal.int (-70), LeanModels.Python.RVal.int (-3),
      LeanModels.Python.RVal.int (-6), LeanModels.Python.RVal.int 100, LeanModels.Python.RVal.int (-36),
      LeanModels.Python.RVal.int 4, LeanModels.Python.RVal.int 62, LeanModels.Python.RVal.int (-4),
      LeanModels.Python.RVal.int (-14), LeanModels.Python.RVal.int 10, LeanModels.Python.RVal.int 67,
      LeanModels.Python.RVal.int 1, LeanModels.Python.RVal.int 74, LeanModels.Python.RVal.int 73,
      LeanModels.Python.RVal.int 27, LeanModels.Python.RVal.int 62, LeanModels.Python.RVal.int (-2),
      LeanModels.Python.RVal.int 24, LeanModels.Python.RVal.int 24, LeanModels.Python.RVal.int 45,
      LeanModels.Python.RVal.int 37, LeanModels.Python.RVal.int 33, LeanModels.Python.RVal.int 41,
      LeanModels.Python.RVal.int 25, LeanModels.Python.RVal.int 17, LeanModels.Python.RVal.int (-1),
      LeanModels.Python.RVal.int 5, LeanModels.Python.RVal.int 31, LeanModels.Python.RVal.int 21,
      LeanModels.Python.RVal.int 22, LeanModels.Python.RVal.int 35, LeanModels.Python.RVal.int 2,
      LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int (-18), LeanModels.Python.RVal.int 10,
      LeanModels.Python.RVal.int 13, LeanModels.Python.RVal.int 22, LeanModels.Python.RVal.int 18,
      LeanModels.Python.RVal.int 15, LeanModels.Python.RVal.int 11, LeanModels.Python.RVal.int (-14),
      LeanModels.Python.RVal.int (-23), LeanModels.Python.RVal.int (-15), LeanModels.Python.RVal.int 2,
      LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 2, LeanModels.Python.RVal.int 0,
      LeanModels.Python.RVal.int (-23), LeanModels.Python.RVal.int (-20), LeanModels.Python.RVal.int (-74),
      LeanModels.Python.RVal.int (-23), LeanModels.Python.RVal.int (-26), LeanModels.Python.RVal.int (-24),
      LeanModels.Python.RVal.int (-19), LeanModels.Python.RVal.int (-35), LeanModels.Python.RVal.int (-22),
      LeanModels.Python.RVal.int (-69)])),
 ("k", some (LeanModels.Python.RVal.str "N")),
 ("padrow", some (LeanModels.Python.RVal.ref 2)),
 ("table",
  some (LeanModels.Python.RVal.tuple
    #[LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
      LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
      LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 78,
      LeanModels.Python.RVal.int 83, LeanModels.Python.RVal.int 86, LeanModels.Python.RVal.int 73,
      LeanModels.Python.RVal.int 102, LeanModels.Python.RVal.int 82, LeanModels.Python.RVal.int 85,
      LeanModels.Python.RVal.int 90, LeanModels.Python.RVal.int 7, LeanModels.Python.RVal.int 29,
      LeanModels.Python.RVal.int 21, LeanModels.Python.RVal.int 44, LeanModels.Python.RVal.int 40,
      LeanModels.Python.RVal.int 31, LeanModels.Python.RVal.int 44, LeanModels.Python.RVal.int 7,
      LeanModels.Python.RVal.int (-17), LeanModels.Python.RVal.int 16, LeanModels.Python.RVal.int (-2),
      LeanModels.Python.RVal.int 15, LeanModels.Python.RVal.int 14, LeanModels.Python.RVal.int 0,
      LeanModels.Python.RVal.int 15, LeanModels.Python.RVal.int (-13), LeanModels.Python.RVal.int (-26),
      LeanModels.Python.RVal.int 3, LeanModels.Python.RVal.int 10, LeanModels.Python.RVal.int 9,
      LeanModels.Python.RVal.int 6, LeanModels.Python.RVal.int 1, LeanModels.Python.RVal.int 0,
      LeanModels.Python.RVal.int (-23), LeanModels.Python.RVal.int (-22), LeanModels.Python.RVal.int 9,
      LeanModels.Python.RVal.int 5, LeanModels.Python.RVal.int (-11), LeanModels.Python.RVal.int (-10),
      LeanModels.Python.RVal.int (-2), LeanModels.Python.RVal.int 3, LeanModels.Python.RVal.int (-19),
      LeanModels.Python.RVal.int (-31), LeanModels.Python.RVal.int 8, LeanModels.Python.RVal.int (-7),
      LeanModels.Python.RVal.int (-37), LeanModels.Python.RVal.int (-36), LeanModels.Python.RVal.int (-14),
      LeanModels.Python.RVal.int 3, LeanModels.Python.RVal.int (-31), LeanModels.Python.RVal.int 0,
      LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
      LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0, LeanModels.Python.RVal.int 0,
      LeanModels.Python.RVal.int 0])),
 ("k", some (LeanModels.Python.RVal.str "P")),
 ("pst", some (LeanModels.Python.RVal.ref 1)),
 ("piece", some (LeanModels.Python.RVal.ref 0)),
 ("version", some (LeanModels.Python.RVal.str "sunfish 2026")),
 ("time", none)]

/-! ### The prefix RUNS — statements 0 to 6, in the kernel

Seven statements: the module docstring, the two imports (`import time`
poisons its own name, loudly), the `pass` the extractor leaves, `version`,
`piece` and the raw `pst` tables. Two heap objects, and `rfl` reaches them in
about a tenth of a second — the fold arms of the pipeline do not run the
interpreter at all. -/

theorem run_prefix :
    initFoldLive sunfish initExecFuel #[] [] #[] prefix7 = (h7, acc7) := by
  rfl

/-! ### The split, and the `done` bookkeeping

Both by `rfl` on the module's own array — the split is not a claim about
sunfish, it is `take`/`drop`. -/

theorem topLevel_split :
    sunfish.topLevel.toList = prefix7 ++ (pstPipeline ++ tail9) := by rfl

theorem done_split : done7 ++ pstPipeline.toArray = donePst := by rfl

theorem empty_append_done : (#[] : Array Stmt) ++ done7 = done7 := by rfl

/-! ### THE ONE HYPOTHESIS

The `pst` pipeline, from the state the prefix leaves to the state the tail
starts from. This is the whole of what this file assumes, it is a GROUND
equation between two pinned literals, and the `#guard` at the bottom runs it
through the compiled evaluator. -/

/-- **The `pst` pipeline's run** — statements 7 and 8 of the shipped file
(the padding loop over `pst.items()`, and `K_MID`/`K_END`). True (see the
`#guard`), and out of the kernel's reach on this hardware for the reason
measured in the header. -/
def PstPipelineRuns : Prop :=
  initFoldLive sunfish initExecFuel h7 acc7 done7 pstPipeline = (h9, acc9)

/-! ### The whole initializer, from that one hypothesis

`initFoldLive_append` twice and the pipeline's own fold/exec arms: the prefix
is `run_prefix`, the middle is the hypothesis, and the tail is left as a term
for the two projections below to reduce. -/

theorem run_all (hpst : PstPipelineRuns) :
    initFoldLive sunfish initExecFuel #[] [] #[] sunfish.topLevel.toList
      = initFoldLive sunfish initExecFuel h9 acc9 donePst tail9 := by
  rw [topLevel_split, initFoldLive_append, run_prefix]
  show initFoldLive sunfish initExecFuel h7 acc7 (#[] ++ done7) (pstPipeline ++ tail9) = _
  rw [empty_append_done, initFoldLive_append, hpst, done_split]

/-- The world the whole module makes, with only the tail left to reduce. -/
theorem initWorld_tail (hpst : PstPipelineRuns) :
    initWorld sunfish =
      { heap := (initFoldLive sunfish initExecFuel h9 acc9 donePst tail9).1,
        globals := resolvedG (initFoldLive sunfish initExecFuel h9 acc9 donePst tail9).2 } :=
  initWorld_of_run (by rw [run_all hpst])

/-! ### The flagship's two hypotheses, DISCHARGED past the pipeline

Each is one `rfl` through the fifteen remaining top-level statements
(0.72 s): the constants fold, `directions` allocates the sixty-FOURTH heap
object — which is why its address is 63 — the MATE window reads `piece`
through the live view, `opt_ranges` and the `__main__` guard fail their exec
attempts and are rolled back and poisoned, and `hist` allocates. None of that
is assumed here; all of it runs. -/

theorem dirs_ref (hpst : PstPipelineRuns) :
    Env.lookup (initWorld sunfish).globals "directions" = some (.ref 63) := by
  rw [initWorld_tail hpst]
  rfl

theorem dirs_obj (hpst : PstPipelineRuns) :
    Heap.get? (initWorld sunfish).heap 63 = some dirsObj := by
  rw [initWorld_tail hpst]
  rfl

/-! ### THE FLAGSHIP, from one statement of the shipped file

`gen_moves_eq_ref_of_dirs` (genmoves_drain.lean) took two hypotheses about
`initWorld sunfish`. It now takes ONE about the `pst` pipeline, and nothing
else about the starting world: for every position the reference enumeration
answers for, calling the shipped `Position.gen_moves` under the Lean
semantics and draining the object it returns yields exactly the reference's
moves, in the reference's order, at every fuel above a threshold. -/
theorem gen_moves_eq_ref_of_pst (hpst : PstPipelineRuns) : GenMovesEqRef :=
  gen_moves_eq_ref_of_dirs (dirs_ref hpst) (dirs_obj hpst)

/-! ### The next chop, entered on the SHIPPED statement

The residue's first half is a dict-items loop, and `ModuleInit`'s shell rule
takes it apart on the real program without any new pin: `initExecStmt` at
statement 7 IS `initItemsLoop` over the `pst` dict at address 1, six entries,
starting at 0. That is the door the sub-statement work goes through — what is
behind it is six rounds of `initItemsLoop_step`, each needing the body
statement this file measured as the wall. -/

/-- The padding-loop statement, and its pieces — projected, never retyped. -/
def pstStmt : Stmt := sunfish.topLevel[7]!

def pstTarget : Expr :=
  match pstStmt with | .forStmt t _ _ _ _ => t | _ => .name "?" ⟨0, 0, 0, 0⟩

def pstBody : Array Stmt :=
  match pstStmt with | .forStmt _ _ b _ _ => b | _ => #[]

/-- The loop's receiver expression (`pst`). -/
def pstRecv : Expr :=
  match pstStmt with
  | .forStmt _ (.call (.attribute d _ _) _ _ _ _) _ _ _ => d
  | _ => .name "?" ⟨0, 0, 0, 0⟩

/-- The module under the statement's own prefix view. -/
def m8 : Module := { sunfish with topLevel := done7.push pstStmt }

/-- The raw `pst` dict the loop iterates, read out of the pinned state. -/
def pstEntries : Array (RVal × RVal) :=
  match Heap.get? h7 1 with | some (.dict es _) => es | _ => #[]

def pstShape : Nat :=
  match Heap.get? h7 1 with | some (.dict _ sv) => sv | _ => 0

theorem pst_loop_entered :
    initExecStmt m8 initExecFuel h7 acc7 pstStmt
      = initItemsLoop m8 65535 h7 acc7 1 pstEntries.size 0 pstTarget pstBody.toList :=
  initExecStmt_items (st := ⟨⟨h7, resolvedG acc7, [], []⟩, []⟩) (a := 1)
    (entries := pstEntries) (sv := pstShape) (by rfl) (by rfl)

/-! ### The hypothesis and the pins, under the compiled evaluator

A `#guard` is a compiled check and not a proof (§L11 finding 2) — which is
exactly why it belongs here, next to the one thing this file does not prove.
The first runs `PstPipelineRuns` itself; the other two are the facts the
flagship consumes, so a stale pin cannot pass quietly. -/

#guard (initFoldLive sunfish initExecFuel h7 acc7 done7 pstPipeline) == (h9, acc9)

#guard (Env.lookup (initWorld sunfish).globals "directions") == some (RVal.ref 63)

#guard (Heap.get? (initWorld sunfish).heap 63) == some dirsObj

/-! ### Axioms

Nothing here reaches past the ambient three, on the flagship or on any step
of the chain. -/

#print axioms run_prefix
#print axioms run_all
#print axioms dirs_ref
#print axioms dirs_obj
#print axioms pst_loop_entered
#print axioms gen_moves_eq_ref_of_pst

end Examples.python.sunfish.init_chain
