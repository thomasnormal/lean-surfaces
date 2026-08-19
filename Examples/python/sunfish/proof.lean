/-
Proof module for `Examples/python/sunfish/spec.lean` (three-file
layout). The transplant of `position_mirror_callsIn`'s geometry
(Examples/python/sf_position) onto the SHIPPED file's
`Position.rotate`: one `callIn.eq_2` step, then `py_simp` — no nested
`callIn` exists (the `Position(…)` constructor is interpreter-inline
and the string methods are pure).

Two provisions keep the 955KB module literal out of the simp run:

* the module constant `sunfish` is passed to `py_simp` (its projections
  — `findFunction`, the class/namedtuple tables, `moduleGlobals` — must
  reduce), which IS the sf_position geometry, just on the real file;
* the two string-tier WORKER applications (the 120-char board through
  `strSlice` and `strSwapcase`) are precomputed as kernel `rfl` facts
  (`hrev`/`hswap`) and handed to `py_simp` as rewrites — the workers
  are deliberately outside the simp sets (the `sortInts` freeze
  doctrine, docs/memory-model.md §string semantics), so the goal keeps
  the compact handles and each collapses in ONE rewrite instead of
  thousands of character-level simp steps.

Envelope note (pass 8): RE-PINNED to engine master `e670434`
(sha256 `f6c481a6…`, 2026-08-19) — the #236 cap-break `bound()` and the
three new module scalars. `Position.rotate` is byte-identical again
(the whole `Position` class is, span-shifts aside), so the theorems and
proofs are untouched; this comment is the required real edit for the
re-extracted envelope.

Envelope note (pass 7): RE-PINNED to current engine master (the QS
walrus filter, explicit castling gen, branchless rights, the
literal-membership capture test, inlined bodies, the null-gate score
cap, the killer depth gate — docs/backlog.md §Pass 7). `Position.rotate`
is byte-identical again, so the theorems and proofs are untouched; this
comment is the required real edit for the re-extracted envelope.

Envelope note (pass 5): the example was RE-PINNED to the post-#158
shipped file — the module literal changed wholesale (new gen_moves
surface with the inlined `yield from`, the moves()-internal null
verification, the `not live` correction gate, `deadline = 1 << 63`).
`Position.rotate` itself is byte-identical in the new file, so the
theorems and their proofs are untouched; this comment is the content
edit that forces re-elaboration (`load_program` does not track its
JSON as a build input).
-/
import LeanModels

namespace Examples.python.sunfish.proof

open LeanModels LeanModels.Python

-- the 1MB post-#158 literal ingests through a deep recursion (seven
-- lowered genexp functions ride along)
set_option maxRecDepth 100000 in
load_program sunfish from "Examples/python/sunfish/sunfish.json"

private def board0 : String :=
  "         \n         \n rnbqkbnr\n pppppppp\n ........\n ........\n ........\n ........\n PPPPPPPP\n RNBQKBNR\n         \n         \n"

private def board0Rot : String :=
  "\n         \n         \nrnbkqbnr \npppppppp \n........ \n........ \n........ \n........ \nPPPPPPPP \nRNBKQBNR \n         \n         "

private def posB (s : Int) : RVal :=
  .ntuple "Position" #["board", "score", "wc", "bc", "ep", "kp"]
    #[.str board0, .int s, .tuple #[.bool true, .bool true],
      .tuple #[.bool false, .bool true], .int 95, .int 22]

private def posR (s : Int) : RVal :=
  .ntuple "Position" #["board", "score", "wc", "bc", "ep", "kp"]
    #[.str board0Rot, .int (-s), .tuple #[.bool false, .bool true],
      .tuple #[.bool true, .bool true], .int 24, .int 97]

private def posRN (s : Int) : RVal :=
  .ntuple "Position" #["board", "score", "wc", "bc", "ep", "kp"]
    #[.str board0Rot, .int (-s), .tuple #[.bool false, .bool true],
      .tuple #[.bool true, .bool true], .int 0, .int 0]

private def posH (s : Int) : RVal :=
  .ntuple "Position" #["board", "score", "wc", "bc", "ep", "kp"]
    #[.str board0, .int s, .tuple #[.bool true, .bool true],
      .tuple #[.bool true, .bool true], .int 0, .int 0]

private def posHR (s : Int) : RVal :=
  .ntuple "Position" #["board", "score", "wc", "bc", "ep", "kp"]
    #[.str board0Rot, .int (-s), .tuple #[.bool true, .bool true],
      .tuple #[.bool true, .bool true], .int 0, .int 0]

/- The 120-char board through `board[::-1]` — kernel-checked once
(literals throughout, so the rewrite matches the goal syntactically). -/
set_option maxRecDepth 131072 in
private theorem hrev :
    strSlice "         \n         \n rnbqkbnr\n pppppppp\n ........\n ........\n ........\n ........\n PPPPPPPP\n RNBQKBNR\n         \n         \n"
        RVal.none RVal.none (RVal.int (-1)) =
      .ok (.str "\n         \n         \nRNBKQBNR \nPPPPPPPP \n........ \n........ \n........ \n........ \npppppppp \nrnbkqbnr \n         \n         ") := by
  rfl

/- …and the reversed board through `.swapcase()`. -/
set_option maxRecDepth 131072 in
private theorem hswap :
    strSwapcase "\n         \n         \nRNBKQBNR \nPPPPPPPP \n........ \n........ \n........ \n........ \npppppppp \nrnbkqbnr \n         \n         " =
      .ok (.str "\n         \n         \nrnbkqbnr \npppppppp \n........ \n........ \n........ \n........ \nPPPPPPPP \nRNBKQBNR \n         \n         ") := by
  rfl

/- pass 4 (note: the envelope was RE-EXTRACTED again for the exceptions
tier — `raise Stop`/`main()`'s try now structure and `Stop` carries
`exception_base`; this comment is the required real edit, since
`load_program` does not track its JSON as a build input).
pass 3 (the envelope was re-extracted for the module-scope
lambda): the resolution arms and the
G1 fold grew (the diverged
discipline, the live-view consults), so one frame of the 955KB module
needs bigger simp budgets — `py_simp` itself now carries
`maxSteps := 1000000` (Logic.lean), and these three proofs the matching
heartbeat headroom. The statements are unchanged. -/
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 16384 in
theorem rotate_callsIn (s : Int) (w : World) :
    CallsIn sunfish w "Position.rotate" #[posB s] w (posR s) := by
  refine ⟨64, ?_⟩
  rw [callIn.eq_2]
  py_simp [sunfish, posB, posR, board0, board0Rot, hrev, hswap]

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 16384 in
theorem rotate_null_callsIn (s : Int) (w : World) :
    CallsIn sunfish w "Position.rotate" #[posB s, .bool true] w (posRN s) := by
  refine ⟨64, ?_⟩
  rw [callIn.eq_2]
  py_simp [sunfish, posB, posRN, board0, board0Rot, hrev, hswap]

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 16384 in
theorem rotate_home_callsIn (s : Int) (w : World) :
    CallsIn sunfish w "Position.rotate" #[posH s] w (posHR s) := by
  refine ⟨64, ?_⟩
  rw [callIn.eq_2]
  py_simp [sunfish, posH, posHR, board0, board0Rot, hrev, hswap]

end Examples.python.sunfish.proof
