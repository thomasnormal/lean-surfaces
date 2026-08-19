/-
Examples/python/sunfish — THE SHIPPED FILE. `sunfish.py` here is
byte-identical to the sunfish repository's engine (no wrappers, no
edits); the envelope is its real AST. PASS 8 re-pinned it to engine
master `e670434` (sha256 `f6c481a6…`, 2026-08-19) — the #236 cap-break
`bound()`: `moves()` yields (value, move) PAIRS, the consumer computes
the score across five branches and BREAKS on a settled cap, and the
head gains `killer`/`calm`/`guard`/`t`/`nmr` (13 top-level statements
to 18); module init gains `LMR`/`NULL_MARGIN`/`DELAY`. `Position` is
byte-identical to pass 7's, span-shifts aside, so the whole generator
tier's object is unmoved. This example carries the first theorems
proved against the file as shipped: `Position.rotate` score-negation — symbolic in the
score AND in the world — on the real 120-char opening board, through
the real string tier (`board[::-1].swapcase()`), the real
`IfExp`/`and`/`not` en-passant flip, the real literal default
(`nullmove=False`), and the real value-like namedtuple subclass
construction.

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

-- the 1MB post-#158 literal ingests through a deep recursion (seven
-- lowered genexp functions ride along)
set_option maxRecDepth 100000 in
load_program sunfish from "Examples/python/sunfish/sunfish.json"

/-! ### The census, pinned: the shipped file's namedtuples recognize
as-is; `Position` is an instantiable value-like subclass carrying its
six-field base; every def/method extracts with plain positional
parameters — since the bound() arc's lambda tier, with NO refusals
left in this table. -/

#guard sunfish.namedtuples.map (fun nt => (nt.name, nt.fields)) ==
  #[("Move", #["i", "j", "prom"]), ("Entry", #["lower", "upper"])]
#guard sunfish.classes.map (fun c => (c.name, c.ok, c.ntBase.map NamedTupleDefn.fields)) ==
  #[("Position", true, some #["board", "score", "wc", "bc", "ep", "kp"]),
    -- the exceptions tier: `class Stop(Exception): pass` is the THIRD
    -- recognized class kind — no longer an unsupported-bases class
    ("Stop", true, Option.none), ("Searcher", true, Option.none)]

/-! The exceptions census (docs/memory-model.md §exceptions): `Stop` is
an ADMITTED exception class on the shipped file — `raise Stop`
structures and would raise its class identity; the census proved
`Exception` unshadowed. Post-#158 the guard is
`if self.nodes % 2048 == 0 and time.time() > self.deadline: raise Stop`
with `deadline = 1 << 63` — no None test, so `time.time()` is
dynamically LIVE at every 2048th node (the wall-clock refusal is
pinned below; every battery row stays under 2048 nodes). -/

#guard sunfish.classes.map (fun c => (c.name, c.isExc)) ==
  #[("Position", false), ("Stop", true), ("Searcher", false)]
#guard sunfish.functions.map (fun f => (f.name, f.argsOk, f.localsOk)) ==
  #[("Position.gen_moves", true, true), ("Position.rotate", true, true),
    -- bound() arc pass 1: `Position.move`'s `put = lambda board, i, p: …`
    -- now extracts as the H7 NestedDef shape (capture-free, assigned
    -- once — the lambda tier), so `move` RUNS; exercised differentially
    -- by `sf_order.move_probe` (verbatim move + rotate)
    ("Position.move", true, true), ("Position.value", true, true),
    ("Position.king_capture", true, true), ("Searcher.__init__", true, true),
    ("Searcher.bound", true, true), ("Searcher.search", true, true),
    ("parse", true, true), ("render", true, true), ("main", true, true),
    -- pass 8 (the re-pin): ingestion lowers SEVEN generator
    -- expressions, CPython's own compilation (`<genexpr>` with the
    -- evaluated outer iterator as its first argument) —
    -- `king_capture`'s filtered probe (@0), THE ORDERING LINE inside
    -- `bound`'s nested `moves()` (@1 — walrus-filtered, `if (v :=
    -- pos.value(m)) >= QS or depth`: `v` becomes a local of the
    -- synthesized frame, admitted because the enclosing body never
    -- mentions it), `calm`'s piece probe (@3 — `any(c in pos.board for
    -- c in "RBNQ")`, which #236 lifted OUT of `moves()` into `bound`'s
    -- own body), the mate/stalemate CORRECTION's scan (@4 —
    -- `pos.move(m).king_capture()` under the immediate `all(…)` drain),
    -- and the module-init trio: the padding loop's pair (@5, @6) and
    -- K_END's single formula genexp (@7).
    --
    -- **Index 2 is a GAP, and the gap is load-bearing.** `genExpName`
    -- and `yieldFromName` (LeanModels/Python/Json.lean) draw from ONE
    -- counter, so `<yieldfrom@2>` — the fresh loop target the general
    -- `yield from` lowering synthesizes for `yield from sorted(…)`, a
    -- NON-genexp delegate (docs/memory-model.md §closure CELLS …, the
    -- §L14 arm) — took index 2. It is a NAME, not a function, so it
    -- never appears in this table. gen_moves's promotion `yield from`
    -- IS a genexp delegate and inlines with no counter at all, which is
    -- why pass 7's numbering was contiguous and this one is not. The
    -- eviction genexps (`next(k for k in self.tp_move if k !=
    -- self.root)`, `next(iter(self.tp_score))`) sit inside
    -- extraction-unsupported `del` statements, dead under the
    -- TABLE_SIZE guard, so they never reach the lowering.
    ("<genexpr@0>", true, true), ("<genexpr@1>", true, true),
    ("<genexpr@3>", true, true), ("<genexpr@4>", true, true),
    ("<genexpr@5>", true, true), ("<genexpr@6>", true, true),
    ("<genexpr@7>", true, true)]

/-! ### The H4 generator census on the shipped file

CPython's rule is scope-local and syntactic, and it lands here exactly:
`Position.gen_moves` and `Searcher.search` are GENERATORS, everything
else is an ordinary def. `bound`'s `moves()` is still not in THIS list —
it is a NESTED def, structured since H7 as `Stmt.defStmt` INSIDE
`bound`'s body, generator flag set, and the closure tier carries it
inline with no flattening. Its capture list is pinned below rather than
described: #236 moved the calmness test out and `guard` in, and `guard`
is written AFTER the `def`, so it is the file's one CELLED capture
(§L14's tier item — the directory key `<cell>guard`, one cell per
frame). The census equals CPython's own `co_freevars` for this def,
checked by `compile()` and not asserted. A generator def evicts the
module from the heap-free fragment (creation ALLOCATES and syntax
cannot tell), which sunfish already was, having classes. -/

#guard (match findFunction sunfish "Searcher.bound" with
  | some f => f.body.toList.filterMap (fun s => match s with
      | Stmt.defStmt n _ _ _ _ ig _ caps _ => some (n, ig, caps.toList)
      | _ => Option.none)
  | Option.none => []) ==
  [("moves", true, ["depth", "gamma", "<cell>guard", "killer", "pos"])]

#guard sunfish.functions.map (fun f => (f.name, f.isGenerator)) ==
  #[("Position.gen_moves", true), ("Position.rotate", false),
    ("Position.move", false), ("Position.value", false),
    ("Position.king_capture", false), ("Searcher.__init__", false),
    ("Searcher.bound", false), ("Searcher.search", true),
    ("parse", false), ("render", false), ("main", false),
    ("<genexpr@0>", true), ("<genexpr@1>", true),
    ("<genexpr@3>", true), ("<genexpr@4>", true), ("<genexpr@5>", true),
    ("<genexpr@6>", true), ("<genexpr@7>", true)]
#guard !moduleGenFree sunfish

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

#guard (match callIn sunfish 4096 ⟨#[], [], [], []⟩ "Position.rotate" #[posB 5] with
        | .ok _ v => v == posR 5
        | _ => false)
#guard (match callIn sunfish 4096 (initWorld sunfish) "Position.rotate" #[posB 5] with
        | .ok _ v => v == posR 5
        | _ => false)
#guard (match callIn sunfish 4096 ⟨#[], [], [], []⟩ "Position.rotate" #[posB 5, .bool true] with
        | .ok _ v => v == posRN 5
        | _ => false)
#guard (match callIn sunfish 4096 ⟨#[], [], [], []⟩ "Position.rotate" #[posH 5] with
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
/-! ### The capstone pin batteries — SPLIT (pass 7, docs/backlog.md
§Pass 7)

The kernel-evaluated capstone batteries that lived below this line
elaborated ~17–80 min as one file; they are now per-capstone modules
next to this one, sharing the ingested program through
`pins_common.lean` (the JSON-trap note lives there):

  * `pins_init.lean`      — the dirty-name census; the padding-loop
                            capstone (`pst`/`K_MID`/`K_END`); `value()`
  * `pins_genmoves.lean`  — `gen_moves` runs; the Ref enumeration
  * `pins_bound.lean`     — the bound() battery; the trace-clock pins
  * `pins_search.lean`    — the stepped-search capstone

This file keeps the ingestion census and the rotate theorems — the
three-file layout with `proof.lean` is unchanged. -/
