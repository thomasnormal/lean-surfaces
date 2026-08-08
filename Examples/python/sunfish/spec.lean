/-
Examples/python/sunfish — THE SHIPPED FILE. `sunfish.py` here is
byte-identical to the sunfish repository's engine (no wrappers, no
edits); the envelope is its real AST. This example carries the first
theorems proved against that file as shipped: `Position.rotate`
score-negation — symbolic in the score AND in the world — on the real
120-char opening board, through the real string tier
(`board[::-1].swapcase()`), the real `IfExp`/`and`/`not` en-passant
flip, the real literal default (`nullmove=False`), and the real
value-like namedtuple subclass construction.

No `#py_check` block CAN exist here (recorded): every function in the
shipped file is outside the public-boundary tier — `parse`/`render`
need `ord`/`chr`, and the Position/Searcher methods receive or return
namedtuples/heap state, which never cross the boundary (`CallsIn` is
the surface that sees them; the loud refusal itself is pinned by
`sf_position.mirror_is_loud`). Non-vacuity is therefore pinned by raw
`#guard`s — the ingestion census and kernel-evaluated `CallsIn` runs,
both in the empty world and in the module's REAL `initWorld`
(piece/pst heap included).
-/
import Examples.python.sunfish.proof

open LeanModels LeanModels.Python

load_program sunfish from "Examples/python/sunfish/sunfish.json"

/-! ### The census, pinned: the shipped file's namedtuples recognize
as-is; `Position` is an instantiable value-like subclass carrying its
six-field base; every def/method extracts with plain positional
parameters (`Position.move` is the one static-locals refusal — its
`put` lambda binding). -/

#guard sunfish.namedtuples.map (fun nt => (nt.name, nt.fields)) ==
  #[("Move", #["i", "j", "prom"]), ("Entry", #["lower", "upper"])]
#guard sunfish.classes.map (fun c => (c.name, c.ok, c.ntBase.map NamedTupleDefn.fields)) ==
  #[("Position", true, some #["board", "score", "wc", "bc", "ep", "kp"]),
    ("Stop", false, Option.none), ("Searcher", true, Option.none)]
#guard sunfish.functions.map (fun f => (f.name, f.argsOk, f.localsOk)) ==
  #[("Position.gen_moves", true, true), ("Position.rotate", true, true),
    ("Position.move", true, false), ("Position.value", true, true),
    ("Position.king_capture", true, true), ("Searcher.__init__", true, true),
    ("Searcher.bound", true, true), ("Searcher.search", true, true),
    ("parse", true, true), ("render", true, true), ("main", true, true)]

/-- The shipped opening board (`sunfish.initial`): 120 chars, padded
ranks, newline separators. -/
private def board0 : String :=
  "         \n         \n rnbqkbnr\n pppppppp\n ........\n ........\n ........\n ........\n PPPPPPPP\n RNBQKBNR\n         \n         \n"

/-- `board0[::-1].swapcase()` — the rotated board `rotate` builds
(kernel-checked against the string tier below; differentially pinned
against CPython by `Examples/python/str_lab`'s `board_flip` and
`Examples/python/sf_position`'s `rotate_*` rows). -/
private def board0Rot : String :=
  "\n         \n         \nrnbkqbnr \npppppppp \n........ \n........ \n........ \n........ \nPPPPPPPP \nRNBKQBNR \n         \n         "

/-- The self-value of the rotate theorems: the REAL opening board, a
symbolic score, distinct castling tuples, nonzero ep/kp (so the flip
arithmetic is exercised, not just the falsy branch). -/
private def posB (s : Int) : RVal :=
  .ntuple "Position" #["board", "score", "wc", "bc", "ep", "kp"]
    #[.str board0, .int s, .tuple #[.bool true, .bool true],
      .tuple #[.bool false, .bool true], .int 95, .int 22]

/-- `posB.rotate()`: board reversed and case-swapped, score NEGATED,
castling rights swapped, ep/kp flipped through `119 - _`. -/
private def posR (s : Int) : RVal :=
  .ntuple "Position" #["board", "score", "wc", "bc", "ep", "kp"]
    #[.str board0Rot, .int (-s), .tuple #[.bool false, .bool true],
      .tuple #[.bool true, .bool true], .int 24, .int 97]

/-- `posB.rotate(True)` (nullmove): same rotation, ep/kp ZEROED. -/
private def posRN (s : Int) : RVal :=
  .ntuple "Position" #["board", "score", "wc", "bc", "ep", "kp"]
    #[.str board0Rot, .int (-s), .tuple #[.bool false, .bool true],
      .tuple #[.bool true, .bool true], .int 0, .int 0]

/-- The opening self-value (ep = kp = 0 — the `and`-chain's falsy
short-circuit). -/
private def posH (s : Int) : RVal :=
  .ntuple "Position" #["board", "score", "wc", "bc", "ep", "kp"]
    #[.str board0, .int s, .tuple #[.bool true, .bool true],
      .tuple #[.bool true, .bool true], .int 0, .int 0]

/-- `posH.rotate()`: ep/kp stay 0 (`0 and …` is falsy). -/
private def posHR (s : Int) : RVal :=
  .ntuple "Position" #["board", "score", "wc", "bc", "ep", "kp"]
    #[.str board0Rot, .int (-s), .tuple #[.bool true, .bool true],
      .tuple #[.bool true, .bool true], .int 0, .int 0]

/-! ### Non-vacuity, kernel-evaluated: the method RUNS — in the empty
world and in the module's real `initWorld` (the piece/pst dict heap) —
and a namedtuple result refuses the public boundary loudly. -/

#guard (match callIn sunfish 4096 ⟨#[], [], []⟩ "Position.rotate" #[posB 5] with
        | .ok _ v => v == posR 5
        | _ => false)
#guard (match callIn sunfish 4096 (initWorld sunfish) "Position.rotate" #[posB 5] with
        | .ok _ v => v == posR 5
        | _ => false)
#guard (match callIn sunfish 4096 ⟨#[], [], []⟩ "Position.rotate" #[posB 5, .bool true] with
        | .ok _ v => v == posRN 5
        | _ => false)
#guard (match callIn sunfish 4096 ⟨#[], [], []⟩ "Position.rotate" #[posH 5] with
        | .ok _ v => v == posHR 5
        | _ => false)

/-! ### The theorems: the headline deliverable — `Position.rotate`
score-negation on the shipped sunfish.py, symbolic in the score and in
the WORLD (rotate touches neither heap nor globals: strings and
namedtuples are values). -/

/-- **`Position.rotate` on the shipped file**: for every score `s` and
every world `w`, rotating the opening-board position negates the score,
reverses and case-swaps the real 120-char board, swaps the castling
tuples, and flips en-passant/king-passant through `119 - _` — with the
world handed back untouched. `nullmove` fills from the shipped literal
default (`False`). -/
theorem rotate_callsIn (s : Int) (w : World) :
    CallsIn sunfish w "Position.rotate" #[posB s] w (posR s) := by
  proofs

/-- `rotate(True)` — the nullmove variant: same rotation and score
negation, en-passant state zeroed. -/
theorem rotate_null_callsIn (s : Int) (w : World) :
    CallsIn sunfish w "Position.rotate" #[posB s, .bool true] w (posRN s) := by
  proofs

/-- The opening position (`ep = kp = 0`): the `and`-chain
short-circuits falsy and both squares stay 0. -/
theorem rotate_home_callsIn (s : Int) (w : World) :
    CallsIn sunfish w "Position.rotate" #[posH s] w (posHR s) := by
  proofs
