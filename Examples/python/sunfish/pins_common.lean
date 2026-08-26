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

ENVELOPE NOTE (the standing trap, NOW CLOSED): `load_program` does not
track its JSON as a build input and lake hashes CONTENT — after
re-extracting `sunfish.json`, make a real edit HERE (this comment is the
place); the import chain then rebuilds every pin file. The pin files
themselves need no touch.

SUPERSEDED 2026-08-26 (qol-83): the lakefile declares `Examples/python`
as an `input_dir` in `Examples.needs`, so lake tracks this envelope as a
build input and the ritual above is HISTORY, not instruction. The note is
kept because SIX of these existed fleet-wide, this one carried a numbered
re-extraction log to pass 7, and a lane still lost a green to the trap:
the record of a discipline that did not hold is worth more than its
deletion. VERIFICATION IS PENDING — see qol-83; the falsifiable test is a
python envelope edited with zero `.lean` changes, whose loaders must come
back Built, not Replayed.

Re-extraction log: pass 7 — the RE-PIN to current engine master (the
QS walrus filter now lowers, §the walrus filter; explicit castling
gen; branchless castling rights; the literal-membership capture test;
inlined single-statement bodies; the null-gate score cap replacing the
band-edge probe arm; the killer depth gate).

Re-extraction log: pass 8 -- the RE-PIN to engine master `e670434`
(`sunfish.py` sha256 f6c481a6..., 2026-08-19). `Searcher.bound` is the
#236 cap-break body: `moves()` yields (value, move) PAIRS, `val_lower`
is gone, the consumer computes the score across five branches and
BREAKS on a settled cap, and four new head statements (`killer`,
`calm`/`guard`, `t`, `nmr`) take the body from 13 top-level statements
to 18. Module init gains three scalars (`LMR`, `NULL_MARGIN`, `DELAY`),
so `Module.topLevel` goes 24 -> 27. Unchanged, measured span-blind
against the previous envelope: `Position` in its entirety
(`gen_moves`/`value`/`move`/`rotate`/`king_capture`), `parse`,
`render`, and the whole table shape (probe, store, `Entry`).

Re-extraction log: rebuild-20260814 -- f-strings LOWERED in the
envelope (str-call spelling) and the two benign from-imports now
STRUCTURED (Pass 0 import forms); frontend stamp moves to CPython
3.9.25, the pinned-oracle family (body-identical to the 3.14 stamps
everywhere the extractor did not change -- measured, 84/96 envelopes
version-line-only).

Re-extraction log: pass 9 -- NOT a re-pin. `sunfish.py` is UNCHANGED;
this pass is the EXTRACTOR catching up. Two statements the envelope
recorded as `Unsupported` now lower as real `DeleteSubscript` nodes:

  511  del self.tp_move[next(k for k in self.tp_move if k != self.root)]
  541  del self.tp_score[next(iter(self.tp_score))]

Those are the two table evictions, and the tier gained the capability to
model them on 2026-08-24/25 (`iter(d)`+`next`; the genexp-over-keys
cursor) -- but the ENVELOPE was never re-extracted, so the model kept
ingesting both as `Unsupported` while `dict_lab`'s corpus rows exercised
the capability and passed. A capability is delivered when the artifact
the model LOADS is re-extracted, not when the model supports it.

NO CERTIFICATE CAN MOVE, and it is checkable rather than asserted: both
statements sit inside `if len(...) > TABLE_SIZE` with
`TABLE_SIZE = 10**6`, while the deepest pinned walk reaches 2053 nodes,
so neither branch is reachable. The refusal is LAZY, not eager -- this
battery already runs `bound()` today with those `Unsupported` nodes
inside it. If a pin moves, that argument was wrong and the change stops.
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

/-- `(bound, nodes)` of one probe `Searcher().bound(pos, gamma, depth)`
— fresh searcher per probe, exactly the CPython driver. -/
def boundProbe (pos : RVal) (gamma depth : Int) :
    Option (Int × Int) :=
  match searcherW with
  | some (w, a) =>
    (match callIn sunfish 1000000 w "Searcher.bound"
        #[.ref a, pos, .int gamma, .int depth] with
     | .ok w' (.int r) =>
       (match Heap.get? w'.heap a with
        | some (.instance _ attrs) =>
          (match Env.lookup attrs.toList "nodes" with
           | some (.int n) => some (r, n)
           | _ => Option.none)
        | _ => Option.none)
     | _ => Option.none)
  | Option.none => Option.none

/-- `Searcher()` constructed from `initWorld` with the clock trace
seeded BEFORE anything runs — the `∀ tr` twin of `pins.searcherW`. -/
def searcherWT (tr : ClockTrace) : Option (World × Addr) :=
  match evalExpr sunfish 4096 ⟨(initWorld sunfish).withClock tr, []⟩
      (.call (.name "Searcher" sp0) #[] #[] Option.none sp0) with
  | .ok st (.ref a) => some (st.world, a)
  | _ => Option.none

/-- `(bound, nodes)` of one probe under a seeded trace — the `∀ tr`
twin of the battery's `boundProbe` (pins_bound.lean). -/
def boundProbeT (tr : ClockTrace) (pos : RVal) (gamma depth : Int) :
    Option (Int × Int) :=
  match searcherWT tr with
  | some (w, a) =>
    (match callIn sunfish 1000000 w "Searcher.bound"
        #[.ref a, pos, .int gamma, .int depth] with
     | .ok w' (.int r) =>
       (match Heap.get? w'.heap a with
        | some (.instance _ attrs) =>
          (match Env.lookup attrs.toList "nodes" with
           | some (.int n) => some (r, n)
           | _ => Option.none)
        | _ => Option.none)
     | _ => Option.none)
  | Option.none => Option.none

/-- Midgame (Italian-shaped, after 1.e4 e5 2.Nf3 Nc6 3.Bc4 Nf6 4.d3
Bc5 — the position the side to move sees). -/
def posMid : RVal :=
  .ntuple "Position" #["board", "score", "wc", "bc", "ep", "kp"]
    #[.str "         \n         \n r.bqk..r\n pppp.ppp\n ..n..n..\n ..b.p...\n ..B.P...\n ...P.N..\n PPP..PPP\n RNBQK..R\n         \n         \n",
      .int (-13), .tuple #[.bool true, .bool true],
      .tuple #[.bool true, .bool true], .int 0, .int 0]

end Examples.python.sunfish.pins
