/-
Shared surface for the sunfish PIN FILES (the pass-7 spec-pole split:
docs/backlog.md §Pass 7). The 927-line monolithic spec elaborated
~17–80 min and every re-pin paid all of it; the capstone check
batteries now live in per-capstone files —

  * `pins_init.lean`      — the dirty-name census, the padding-loop
                            capstone (`pst`/`K_MID`/`K_END`), `value()`
  * `pins_genmoves.lean`  — `gen_moves` runs + the Ref enumeration
  * `pins_bound.lean`     — the bound() battery + the trace-clock pins
  * `pins_search.lean`    — the stepped-search capstone

— each importing THIS module for the ingested program and the shared
probe defs. `Examples/python/sunfish/spec.lean` keeps the census and
the rotate theorems (with `proof.lean`, the three-file layout).

ENVELOPE NOTE (the standing trap): `load_program` does not track its
JSON as a build input and lake hashes CONTENT — after re-extracting
`sunfish.json`, make a real edit HERE (this comment is the place); the
import chain then rebuilds every pin file. The pin files themselves
need no touch.

Re-extraction log: pass 7 — the RE-PIN to current engine master (the
QS walrus filter now lowers, §the walrus filter; explicit castling
gen; branchless castling rights; the literal-membership capture test;
inlined single-statement bodies; the null-gate score cap replacing the
band-edge probe arm; the killer depth gate).

Re-extraction log: rebuild-20260814 -- f-strings LOWERED in the
envelope (str-call spelling) and the two benign from-imports now
STRUCTURED (Pass 0 import forms); frontend stamp moves to CPython
3.9.25, the pinned-oracle family (body-identical to the 3.14 stamps
everywhere the extractor did not change -- measured, 84/96 envelopes
version-line-only).
-/
import LeanModels

namespace Examples.python.sunfish.pins

open LeanModels LeanModels.Python

-- the 1MB post-#158 literal ingests through a deep recursion (seven
-- lowered genexp functions ride along)
set_option maxRecDepth 100000 in
load_program sunfish from "Examples/python/sunfish/sunfish.json"

/-- The shipped opening board (`sunfish.initial`): 120 chars, padded
ranks, newline separators. -/
def board0 : String :=
  "         \n         \n rnbqkbnr\n pppppppp\n ........\n ........\n ........\n ........\n PPPPPPPP\n RNBQKBNR\n         \n         \n"

/-- The opening self-value (ep = kp = 0). -/
def posH (s : Int) : RVal :=
  .ntuple "Position" #["board", "score", "wc", "bc", "ep", "kp"]
    #[.str board0, .int s, .tuple #[.bool true, .bool true],
      .tuple #[.bool true, .bool true], .int 0, .int 0]

def sp0 : Span := ⟨0, 0, 0, 0⟩

/-- A fresh shipped `Searcher()` over the real `initWorld`: the world
after `__init__` and the instance address. -/
def searcherW : Option (World × Addr) :=
  match evalExpr sunfish 4096 ⟨initWorld sunfish, []⟩
      (.call (.name "Searcher" sp0) #[] #[] Option.none sp0) with
  | .ok st (.ref a) => some (st.world, a)
  | _ => Option.none

end Examples.python.sunfish.pins
