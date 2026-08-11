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

-- the 955KB literal ingests through a deep recursion (H4 added four
-- lowered genexp functions to it)
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
an ADMITTED exception class on the shipped file — `raise Stop` (line
332, dynamically dead under `deadline = None`) structures and would
raise its class identity; the census proved `Exception` unshadowed. -/

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
    -- H4/H7/pass 3/pass 4: ingestion LOWERED ELEVEN generator
    -- expressions into implicit generator functions, CPython's own
    -- compilation (`<genexpr>` with the evaluated outer iterator as its
    -- first argument) — the two inside `bound`'s nested `moves()` (the
    -- null-move `any` probe and THE ORDERING LINE), the fold's
    -- legality scan, and since pass 4 the mate/stalemate CORRECTION's
    -- scan too (its captures `depth`/`val_lower` are body-assigned —
    -- the immediate-drain boundBefore admission, docs/memory-model.md
    -- §bound() end-to-end); plus the module-init ones: the padding
    -- loop's pair (the lambda's inner genexp and the sum-over-slices
    -- genexp) and K_END's NESTED pair (the inner captures the OUTER
    -- genexp's target `rank` — the drain-gated admission, §module-init
    -- execution).
    ("<genexpr@0>", true, true), ("<genexpr@1>", true, true),
    ("<genexpr@2>", true, true), ("<genexpr@3>", true, true),
    ("<genexpr@4>", true, true), ("<genexpr@5>", true, true),
    ("<genexpr@6>", true, true), ("<genexpr@7>", true, true),
    ("<genexpr@8>", true, true), ("<genexpr@9>", true, true),
    ("<genexpr@10>", true, true)]

/-! ### The H4 generator census on the shipped file

CPython's rule is scope-local and syntactic, and it lands here exactly:
`Position.gen_moves` and `Searcher.search` are GENERATORS, everything
else is an ordinary def. `bound`'s `moves()` is still not in THIS list —
it is a NESTED def, structured since H7 as `Stmt.defStmt` INSIDE
`bound`'s body (captures `depth`/`gamma`/`pos`/`root`/`self`/
`val_lower`, admitted by the never-rebound analysis, generator flag
set) — the closure tier carries it inline, no flattening. A generator
def evicts the module from the heap-free fragment (creation ALLOCATES
and syntax cannot tell), which sunfish already was, having classes. -/

#guard sunfish.functions.map (fun f => (f.name, f.isGenerator)) ==
  #[("Position.gen_moves", true), ("Position.rotate", false),
    ("Position.move", false), ("Position.value", false),
    ("Position.king_capture", false), ("Searcher.__init__", false),
    ("Searcher.bound", false), ("Searcher.search", true),
    ("parse", false), ("render", false), ("main", false),
    ("<genexpr@0>", true), ("<genexpr@1>", true),
    ("<genexpr@2>", true), ("<genexpr@3>", true), ("<genexpr@4>", true),
    ("<genexpr@5>", true), ("<genexpr@6>", true), ("<genexpr@7>", true),
    ("<genexpr@8>", true), ("<genexpr@9>", true), ("<genexpr@10>", true)]
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

/-! ### The G1 dirty-name pass on the shipped file (2026-08-09)

Before it, `import time` on line 12 poisoned EVERY module global and
`Position.gen_moves` refused at `directions[p]`. Poisoning is now
per-name, so the census below is the load-bearing new fact and is pinned
here rather than described: `time` poisoned (bound by CPython, so loud —
never a fake `NameError`); `count` absent, resolving to the model's
`itertools.count`; `piece`/`pst` valued, then the
`for k, table in pst.items()` loop poisoning `pst` (twice — one per
subscript store), `padrow`, `table`, `k`, so `K_MID = pst["K"]` stays
statically poisoned; `A1/H1/A8/H8`, `initial`, `N/E/S/W` and the search
constants resolve STATICALLY (heap-pure literals survive the pass-3
DIVERGED discipline); `directions` (a dict display — a ref) and
`MATE_LOWER/MATE_UPPER` (heap reads of `piece`) sit AFTER the first
exec-attempted statement (the padding loop, line 79), so pass 3 moves
them to the LIVE VIEW — statically poisoned here, valued in
`initWorld`'s globals below, same values, one heap. `opt_ranges` (a
keyword call) and `hist` (a constructor call) are out-of-tier right-hand
sides. Reverse order = source order. -/

#guard ((moduleGlobals sunfish).1.map (fun p => (p.1, p.2.isSome))).reverse ==
  [("time", false), ("__version__", true), ("version", true),
   ("piece", true), ("pst", true), ("pst", false), ("pst", false),
   ("padrow", false), ("table", false), ("k", false),
   ("K_MID", false), ("K_END", false),
   ("A1", true), ("H1", true), ("A8", true), ("H8", true),
   ("initial", true), ("N", true), ("E", true), ("S", true), ("W", true),
   ("directions", false), ("MATE_LOWER", false), ("MATE_UPPER", false),
   ("QS", true), ("QS_A", true), ("EVAL_ROUGHNESS", true),
   ("TABLE_SIZE", true), ("opt_ranges", false), ("hist", false)]

/-! The live view serves what the static table ceded (same values — the
fold step runs on the live state, so `directions` is the same dict shape
at a live address and the MATE window the same ints). -/

#guard (Env.lookup (initWorld sunfish).globals "MATE_LOWER") ==
  some (RVal.int 47923)
#guard (Env.lookup (initWorld sunfish).globals "MATE_UPPER") ==
  some (RVal.int 69290)
#guard (Env.lookup (initWorld sunfish).globals "directions").isSome

/-! Every top-level statement's binding set was determined, so a missing
module name is the faithful `NameError` — the second, independent half of
the pass. (`isModuleDunder` keeps `__name__`/`__doc__`/… loud regardless:
the import machinery binds them, no statement does.) -/

#guard (moduleGlobals sunfish).2

/-! ### `Position.gen_moves` RUNS on the shipped file

The capstone's precondition, kernel-evaluated: the real generator over
the real opening board, through the real `enumerate`/`count` iterator
frames, the real `directions` dict and the real `Move` namedtuple. The
20 moves below are CPython's own answer for this position, IN CPython's
order (16 pawn pushes, then the four knight moves) — the order is part
of the claim, since `bound`'s cutoffs depend on it. -/

private def drainMoves (w : World) (a : Addr) : Nat → Option (List (Int × Int × String))
  | 0 => Option.none
  | n + 1 =>
    match stepIter sunfish 16384 w a with
    | .ok w' (some (.ntuple _ _ #[.int i, .int j, .str p])) =>
      (drainMoves w' a n).map ((i, j, p) :: ·)
    | .ok _ Option.none => some []
    | _ => Option.none

#guard (match callIn sunfish 8192 (initWorld sunfish) "Position.gen_moves" #[posH 0] with
        | .ok w (.ref a) => drainMoves w a 64
        | _ => Option.none) ==
  some [(81, 71, ""), (81, 61, ""), (82, 72, ""), (82, 62, ""),
        (83, 73, ""), (83, 63, ""), (84, 74, ""), (84, 64, ""),
        (85, 75, ""), (85, 65, ""), (86, 76, ""), (86, 66, ""),
        (87, 77, ""), (87, 67, ""), (88, 78, ""), (88, 68, ""),
        (92, 73, ""), (92, 71, ""), (97, 78, ""), (97, 76, "")]

/-! ### PASS 3 CAPSTONE: the module-init padding loop RUNS

`for k, table in pst.items(): padrow = lambda …; pst[k] = sum(…); …`
executes in the live pipeline — the dict-items shell, the module-level
zero-capture lambda rebound per iteration (its body reads `piece` and
the CURRENT `k` through the live globals at call time), the lowered
genexp of computed tuple slices, `sum(…, ())`, and `(0,)*20` padding —
so the SHIPPED `pst` materializes in the model. The values below are
CPython's own (the shipped module imported and probed; A1 = 91, H8 = 28
are real squares, 0 and 119 the padding ring). `K_MID`/`K_END` land
with it, and `Position.value()` — refused before this pass because
`pst` was poisoned — now runs on the shipped file. -/

private def pstAt (p : String) (sq : Nat) : Option RVal :=
  match Env.lookup (initWorld sunfish).globals "pst" with
  | some (.ref a) =>
    (match Heap.get? (initWorld sunfish).heap a with
     | some (.dict es _) =>
       (match dictFind es.toList (.str p) with
        | some (.tuple xs) => some (xs.getD sq .none)
        | _ => Option.none)
     | _ => Option.none)
  | _ => Option.none

#guard pstAt "P" 91 == some (.int 100)
#guard pstAt "N" 91 == some (.int 206)
#guard pstAt "N" 54 == some (.int 317)
#guard pstAt "B" 28 == some (.int 270)
#guard pstAt "R" 54 == some (.int 492)
#guard pstAt "Q" 28 == some (.int 955)
#guard pstAt "K" 91 == some (.int 60017)
#guard ["P", "N", "B", "R", "Q", "K"].all fun p =>
  pstAt p 0 == some (.int 0) && pstAt p 119 == some (.int 0)

/-! `K_MID` is the padded shipped K table; `K_END` the mop-up
centralization gradient — both 120 wide, both live-view bindings. -/

#guard (match Env.lookup (initWorld sunfish).globals "K_MID" with
        | some (.tuple xs) => xs.size == 120 && xs.getD 95 .none == .int 60006
        | _ => false)
#guard (match Env.lookup (initWorld sunfish).globals "K_END" with
        | some (.tuple xs) =>
          xs.size == 120 && xs.getD 95 .none == .int 59990
            && xs.getD 54 .none == .int 60050
        | _ => false)

/-! ### `Position.value()` on the shipped file — UNBLOCKED

The move-ordering heuristic over the REAL padded tables (the values are
CPython's: 46 for the double push e2e4-shaped Move(84, 64), 42 for
Move(85, 65), 5 for the knight Move(92, 71) — the same probes
`sf_order` pinned against its oracle-generated table, now answered by
the SHIPPED file's own init). -/

private def mv (i j : Int) (prom : String) : RVal :=
  .ntuple "Move" #["i", "j", "prom"] #[.int i, .int j, .str prom]

#guard (match callIn sunfish 8192 (initWorld sunfish) "Position.value"
          #[posH 0, mv 84 64 ""] with
        | .ok _ v => v == .int 46 | _ => false)
#guard (match callIn sunfish 8192 (initWorld sunfish) "Position.value"
          #[posH 0, mv 85 65 ""] with
        | .ok _ v => v == .int 42 | _ => false)
#guard (match callIn sunfish 8192 (initWorld sunfish) "Position.value"
          #[posH 0, mv 92 71 ""] with
        | .ok _ v => v == .int 5 | _ => false)

/-! ### The reference enumeration (the decided theorem's right-hand side)

The owner picked equality against a REFERENCE ENUMERATION with ORDER
pinned (`bound`'s cutoffs depend on move order), and the design note is
that the reference must optimise for OBVIOUSNESS over efficiency — plain
nested scans — because its whole job is to be trustworthy by INSPECTION
against sunfish.py lines 185-226. It is written to be read side by side
with the shipped Python, one Lean line per Python line, and it declines
(`Except.error`) rather than guessing: a real CPython `IndexError` and
an exhausted ray budget are both errors, so neither can be mistaken for
a short move list.

The theorem itself is NOT stated yet — it lands with its proof. What
lands here is the reference and the evidence that it is the right
right-hand side. -/

namespace Ref

/-- A generated move, in the shipped `Move` field order. `prom` is a
`String`, matching `Move(i, j, prom)`. -/
structure RefMove where
  i : Int
  j : Int
  prom : String
deriving DecidableEq, Repr, Inhabited, BEq

/-! ### The shipped constants, copied verbatim (sunfish.py 104, 121) -/

def N : Int := -10
def E : Int := 1
def S : Int := 10
def W : Int := -1
def A1 : Int := 91
def H1 : Int := 98
def A8 : Int := 21
def H8 : Int := 28

/-- `directions` (sunfish.py 122-129), one arm per key, verbatim. -/
def directions (p : Char) : List Int :=
  if p == 'P' then [N, N+N, N+W, N+E]
  else if p == 'N' then [N+N+E, E+N+E, E+S+E, S+S+E, S+S+W, W+S+W, W+N+W, N+N+W]
  else if p == 'B' then [N+E, S+E, S+W, N+W]
  else if p == 'R' then [N, E, S, W]
  else if p == 'Q' then [N, E, S, W, N+E, S+E, S+W, N+W]
  else if p == 'K' then [N, E, S, W, N+E, S+E, S+W, N+W]
  else []

/-! ### Python's own primitives, spelled out

The reference declines rather than guesses: `Except String` carries the
two ways the enumeration can fail to have an answer — a real CPython
`IndexError`, and the step budget standing in for the unbounded
`count`. Neither can be mistaken for a short move list. -/

/-- `board[j]`, Python semantics: a negative index counts from the end,
and an out-of-range index is an `IndexError`. -/
def at? (b : List Char) (j : Int) : Except String Char :=
  let n : Int := b.length
  let k := if j < 0 then j + n else j
  if 0 ≤ k ∧ k < n then
    match b[k.toNat]? with
    | some c => .ok c
    | none => .error "IndexError"
  else .error "IndexError"

/-- `c in "…"` on a string literal. -/
def inStr (c : Char) (s : String) : Bool := s.toList.contains c

/-! ### The body, statement for statement -/

/-- sunfish.py 199-216, the `if p == "P":` block. `none` = the block fell
through to the ordinary yield below it; `some ms` = the block BROKE out
of the ray, having yielded `ms` first (`[]` for a bare `break`, the four
promotions for the last-row case).

Note the `or` on the double-move guard: `i < A1 + N` short-circuits, so
`board[i + N]` is only ever read for `i ≥ 81` and never goes out of
range. The reference makes that visible instead of relying on it. -/
def pawnBreak (b : List Char) (ep kp : Int) (i : Int) (p q : Char) (d j : Int) :
    Except String (Option (List RefMove)) := do
  if p != 'P' then return none
  -- if d in (N, N + N) and q != ".": break
  if (d == N || d == N + N) && q != '.' then return some []
  -- if d == N + N and (i < A1 + N or self.board[i + N] != "."): break
  if d == N + N then
    if i < A1 + N then return some []
    if (← at? b (i + N)) != '.' then return some []
  -- if d in (N + W, N + E) and q == "." and j not in (ep, kp, kp-1, kp+1): break
  if (d == N + W || d == N + E) && q == '.'
      && !(j == ep || j == kp || j == kp - 1 || j == kp + 1) then return some []
  -- if A8 <= j <= H8: for prom in "NBRQ": yield Move(i, j, prom); break
  if A8 ≤ j && j ≤ H8 then
    return some ("NBRQ".toList.map fun pr => ⟨i, j, pr.toString⟩)
  return none

/-- sunfish.py 194-226, one RAY: `for j in count(i + d, d)`. `fuel`
bounds CPython's unbounded `count`; running out is an error, never a
truncated answer. -/
def ray (b : List Char) (wc0 wc1 : Bool) (ep kp : Int) (i : Int) (p : Char) (d : Int) :
    Nat → Int → Except String (List RefMove)
  | 0, _ => .error "ray budget exhausted"
  | fuel + 1, j => do
    let q ← at? b j
    -- if q in " \nPNBRQK": break
    if inStr q " \nPNBRQK" then return []
    match ← pawnBreak b ep kp i p q d j with
    | some ms => return ms
    | none =>
      -- yield Move(i, j, "")
      let here : RefMove := ⟨i, j, ""⟩
      -- if p in "PNK" or q in "pnbrqk": break
      if inStr p "PNK" || inStr q "pnbrqk" then return [here]
      -- the two castling slides, each guarded by its own `if`
      let castle1 ← if i == A1 then
          (do if (← at? b (j + E)) == 'K' && wc0 then
                return [(⟨j + E, j + W, ""⟩ : RefMove)] else return [])
        else pure []
      let castle2 ← if i == H1 then
          (do if (← at? b (j + W)) == 'K' && wc1 then
                return [(⟨j + W, j + E, ""⟩ : RefMove)] else return [])
        else pure []
      let rest ← ray b wc0 wc1 ep kp i p d fuel (j + d)
      return here :: castle1 ++ castle2 ++ rest

/-- sunfish.py 193, one PIECE: every ray, in `directions[p]` order. -/
def piece (b : List Char) (wc0 wc1 : Bool) (ep kp : Int) (fuel : Nat)
    (i : Int) (p : Char) : Except String (List RefMove) :=
  List.flatten <$> (directions p).mapM fun d =>
    ray b wc0 wc1 ep kp i p d fuel (i + d)

/-- sunfish.py 192-194, the whole enumeration:
`for i, p in enumerate(self.board)`, skipping every square that does not
hold one of OUR pieces. -/
def refMoves (b : List Char) (wc0 wc1 : Bool) (ep kp : Int) (fuel : Nat) :
    Except String (List RefMove) :=
  List.flatten <$> (List.range b.length).mapM fun (i : Nat) =>
    match b[i]? with
    | some p =>
      if inStr p "PNBRQK" then piece b wc0 wc1 ep kp fuel (i : Int) p else pure []
    | none => pure []
end Ref

/-! Reference vs CPython, on the shipped opening board and on thirteen
boards chosen for the parts of `gen_moves` random play does not reach:
both promotion forms, en passant, the king-passant squares, castling in
three rights combinations, sliders, edge knights, and both pawn
double-move boundaries. Every expected list below is CPython's own
answer, in CPython's order. (A further 40 boards reached by random play
from the opening — 987 more moves — were checked the same way while the
reference was written.) -/

-- the shipped opening board, the same 20 moves the interpreter yields above
#guard (match Ref.refMoves board0.toList true true 0 0 64 with
        | .ok ms => ms.map (fun m => (m.i, m.j, m.prom)) ==
            [(81, 71, ""), (81, 61, ""), (82, 72, ""), (82, 62, ""),
             (83, 73, ""), (83, 63, ""), (84, 74, ""), (84, 64, ""),
             (85, 75, ""), (85, 65, ""), (86, 76, ""), (86, 66, ""),
             (87, 77, ""), (87, 67, ""), (88, 78, ""), (88, 68, ""),
             (92, 73, ""), (92, 71, ""), (97, 78, ""), (97, 76, "")]
        | .error _ => false)

-- promotion push (7 moves)
#guard (match Ref.refMoves "         \n         \n ........\n P.......\n ........\n ........\n ........\n ........\n ........\n K.......\n         \n         \n".toList false false 0 0 64 with
        | .ok ms => ms == [⟨31, 21, "N"⟩, ⟨31, 21, "B"⟩, ⟨31, 21, "R"⟩, ⟨31, 21, "Q"⟩, ⟨91, 81, ""⟩, ⟨91, 92, ""⟩, ⟨91, 82, ""⟩]
        | .error _ => false)
-- promotion captures (3 moves)
#guard (match Ref.refMoves "         \n         \n .r.r....\n .P......\n ........\n ........\n ........\n ........\n ........\n K.......\n         \n         \n".toList false false 0 0 64 with
        | .ok ms => ms == [⟨91, 81, ""⟩, ⟨91, 92, ""⟩, ⟨91, 82, ""⟩]
        | .error _ => false)
-- en passant (4 moves)
#guard (match Ref.refMoves "         \n         \n ........\n ........\n ........\n pP......\n ........\n ........\n ........\n K.......\n         \n         \n".toList false false 42 0 64 with
        | .ok ms => ms == [⟨52, 42, ""⟩, ⟨91, 81, ""⟩, ⟨91, 92, ""⟩, ⟨91, 82, ""⟩]
        | .error _ => false)
-- kp squares (18 moves)
#guard (match Ref.refMoves "         \n         \n ........\n ........\n ........\n ..p.....\n ........\n ........\n ........\n K...R..K\n         \n         \n".toList false false 0 95 64 with
        | .ok ms => ms == [⟨91, 81, ""⟩, ⟨91, 92, ""⟩, ⟨91, 82, ""⟩, ⟨95, 85, ""⟩, ⟨95, 75, ""⟩, ⟨95, 65, ""⟩, ⟨95, 55, ""⟩, ⟨95, 45, ""⟩, ⟨95, 35, ""⟩, ⟨95, 25, ""⟩, ⟨95, 96, ""⟩, ⟨95, 97, ""⟩, ⟨95, 94, ""⟩, ⟨95, 93, ""⟩, ⟨95, 92, ""⟩, ⟨98, 88, ""⟩, ⟨98, 97, ""⟩, ⟨98, 87, ""⟩]
        | .error _ => false)
-- castling both (26 moves)
#guard (match Ref.refMoves "         \n         \n ........\n ........\n ........\n ........\n ........\n ........\n ........\n R...K..R\n         \n         \n".toList true true 0 0 64 with
        | .ok ms => ms == [⟨91, 81, ""⟩, ⟨91, 71, ""⟩, ⟨91, 61, ""⟩, ⟨91, 51, ""⟩, ⟨91, 41, ""⟩, ⟨91, 31, ""⟩, ⟨91, 21, ""⟩, ⟨91, 92, ""⟩, ⟨91, 93, ""⟩, ⟨91, 94, ""⟩, ⟨95, 93, ""⟩, ⟨95, 85, ""⟩, ⟨95, 96, ""⟩, ⟨95, 94, ""⟩, ⟨95, 86, ""⟩, ⟨95, 84, ""⟩, ⟨98, 88, ""⟩, ⟨98, 78, ""⟩, ⟨98, 68, ""⟩, ⟨98, 58, ""⟩, ⟨98, 48, ""⟩, ⟨98, 38, ""⟩, ⟨98, 28, ""⟩, ⟨98, 97, ""⟩, ⟨98, 96, ""⟩, ⟨95, 97, ""⟩]
        | .error _ => false)
-- castling east only (25 moves)
#guard (match Ref.refMoves "         \n         \n ........\n ........\n ........\n ........\n ........\n ........\n ........\n R...K..R\n         \n         \n".toList false true 0 0 64 with
        | .ok ms => ms == [⟨91, 81, ""⟩, ⟨91, 71, ""⟩, ⟨91, 61, ""⟩, ⟨91, 51, ""⟩, ⟨91, 41, ""⟩, ⟨91, 31, ""⟩, ⟨91, 21, ""⟩, ⟨91, 92, ""⟩, ⟨91, 93, ""⟩, ⟨91, 94, ""⟩, ⟨95, 85, ""⟩, ⟨95, 96, ""⟩, ⟨95, 94, ""⟩, ⟨95, 86, ""⟩, ⟨95, 84, ""⟩, ⟨98, 88, ""⟩, ⟨98, 78, ""⟩, ⟨98, 68, ""⟩, ⟨98, 58, ""⟩, ⟨98, 48, ""⟩, ⟨98, 38, ""⟩, ⟨98, 28, ""⟩, ⟨98, 97, ""⟩, ⟨98, 96, ""⟩, ⟨95, 97, ""⟩]
        | .error _ => false)
-- castling west only (25 moves)
#guard (match Ref.refMoves "         \n         \n ........\n ........\n ........\n ........\n ........\n ........\n ........\n R...K..R\n         \n         \n".toList true false 0 0 64 with
        | .ok ms => ms == [⟨91, 81, ""⟩, ⟨91, 71, ""⟩, ⟨91, 61, ""⟩, ⟨91, 51, ""⟩, ⟨91, 41, ""⟩, ⟨91, 31, ""⟩, ⟨91, 21, ""⟩, ⟨91, 92, ""⟩, ⟨91, 93, ""⟩, ⟨91, 94, ""⟩, ⟨95, 93, ""⟩, ⟨95, 85, ""⟩, ⟨95, 96, ""⟩, ⟨95, 94, ""⟩, ⟨95, 86, ""⟩, ⟨95, 84, ""⟩, ⟨98, 88, ""⟩, ⟨98, 78, ""⟩, ⟨98, 68, ""⟩, ⟨98, 58, ""⟩, ⟨98, 48, ""⟩, ⟨98, 38, ""⟩, ⟨98, 28, ""⟩, ⟨98, 97, ""⟩, ⟨98, 96, ""⟩]
        | .error _ => false)
-- sliders (50 moves)
#guard (match Ref.refMoves "         \n         \n ...q....\n ........\n ..Q.....\n ........\n ....B...\n ........\n .R......\n ...K....\n         \n         \n".toList false false 0 0 64 with
        | .ok ms => ms == [⟨43, 33, ""⟩, ⟨43, 23, ""⟩, ⟨43, 44, ""⟩, ⟨43, 45, ""⟩, ⟨43, 46, ""⟩, ⟨43, 47, ""⟩, ⟨43, 48, ""⟩, ⟨43, 53, ""⟩, ⟨43, 63, ""⟩, ⟨43, 73, ""⟩, ⟨43, 83, ""⟩, ⟨43, 93, ""⟩, ⟨43, 42, ""⟩, ⟨43, 41, ""⟩, ⟨43, 34, ""⟩, ⟨43, 25, ""⟩, ⟨43, 54, ""⟩, ⟨43, 52, ""⟩, ⟨43, 61, ""⟩, ⟨43, 32, ""⟩, ⟨43, 21, ""⟩, ⟨65, 56, ""⟩, ⟨65, 47, ""⟩, ⟨65, 38, ""⟩, ⟨65, 76, ""⟩, ⟨65, 87, ""⟩, ⟨65, 98, ""⟩, ⟨65, 74, ""⟩, ⟨65, 83, ""⟩, ⟨65, 92, ""⟩, ⟨65, 54, ""⟩, ⟨82, 72, ""⟩, ⟨82, 62, ""⟩, ⟨82, 52, ""⟩, ⟨82, 42, ""⟩, ⟨82, 32, ""⟩, ⟨82, 22, ""⟩, ⟨82, 83, ""⟩, ⟨82, 84, ""⟩, ⟨82, 85, ""⟩, ⟨82, 86, ""⟩, ⟨82, 87, ""⟩, ⟨82, 88, ""⟩, ⟨82, 92, ""⟩, ⟨82, 81, ""⟩, ⟨94, 84, ""⟩, ⟨94, 95, ""⟩, ⟨94, 93, ""⟩, ⟨94, 85, ""⟩, ⟨94, 83, ""⟩]
        | .error _ => false)
-- knights edges (19 moves)
#guard (match Ref.refMoves "         \n         \n N......N\n ........\n ........\n ....N...\n ........\n ........\n ........\n N.....NK\n         \n         \n".toList false false 0 0 64 with
        | .ok ms => ms == [⟨21, 33, ""⟩, ⟨21, 42, ""⟩, ⟨28, 47, ""⟩, ⟨28, 36, ""⟩, ⟨55, 36, ""⟩, ⟨55, 47, ""⟩, ⟨55, 67, ""⟩, ⟨55, 76, ""⟩, ⟨55, 74, ""⟩, ⟨55, 63, ""⟩, ⟨55, 43, ""⟩, ⟨55, 34, ""⟩, ⟨91, 72, ""⟩, ⟨91, 83, ""⟩, ⟨97, 78, ""⟩, ⟨97, 85, ""⟩, ⟨97, 76, ""⟩, ⟨98, 88, ""⟩, ⟨98, 87, ""⟩]
        | .error _ => false)
-- opening rows (20 moves)
#guard (match Ref.refMoves "         \n         \n rnbqkbnr\n pppppppp\n ........\n ........\n ........\n ........\n PPPPPPPP\n RNBQKBNR\n         \n         \n".toList true true 0 0 64 with
        | .ok ms => ms == [⟨81, 71, ""⟩, ⟨81, 61, ""⟩, ⟨82, 72, ""⟩, ⟨82, 62, ""⟩, ⟨83, 73, ""⟩, ⟨83, 63, ""⟩, ⟨84, 74, ""⟩, ⟨84, 64, ""⟩, ⟨85, 75, ""⟩, ⟨85, 65, ""⟩, ⟨86, 76, ""⟩, ⟨86, 66, ""⟩, ⟨87, 77, ""⟩, ⟨87, 67, ""⟩, ⟨88, 78, ""⟩, ⟨88, 68, ""⟩, ⟨92, 73, ""⟩, ⟨92, 71, ""⟩, ⟨97, 78, ""⟩, ⟨97, 76, ""⟩]
        | .error _ => false)
-- pawn off home rank (4 moves)
#guard (match Ref.refMoves "         \n         \n ........\n ........\n ........\n ........\n ........\n P.......\n ........\n K.......\n         \n         \n".toList false false 0 0 64 with
        | .ok ms => ms == [⟨71, 61, ""⟩, ⟨91, 81, ""⟩, ⟨91, 92, ""⟩, ⟨91, 82, ""⟩]
        | .error _ => false)
-- double blocked far (4 moves)
#guard (match Ref.refMoves "         \n         \n ........\n ........\n ........\n ........\n ..p.....\n ........\n ..P.....\n K.......\n         \n         \n".toList false false 0 0 64 with
        | .ok ms => ms == [⟨83, 73, ""⟩, ⟨91, 81, ""⟩, ⟨91, 92, ""⟩, ⟨91, 82, ""⟩]
        | .error _ => false)
-- double blocked near (3 moves)
#guard (match Ref.refMoves "         \n         \n ........\n ........\n ........\n ........\n ........\n ..p.....\n ..P.....\n K.......\n         \n         \n".toList false false 0 0 64 with
        | .ok ms => ms == [⟨91, 81, ""⟩, ⟨91, 92, ""⟩, ⟨91, 82, ""⟩]
        | .error _ => false)

/-! ### THE PASS-4 CAPSTONE: `Searcher().bound()` runs END TO END on
the shipped file

Every probe instantiates a fresh `Searcher()` — the hand-built call
below, CPython's own driver shape: `__init__`'s two tuple-ATTRIBUTE
unpacks bind the empty tables, the empty history set, `nodes = 0` and
`deadline = None` (so the structured `raise Stop` guard short-circuits
dead and the wall clock is never consulted) — in the module's REAL
`initWorld`, calls the shipped `Searcher.bound` through `callIn` with
`root` filled from its literal default, and reads back the RETURNED
BOUND and `self.nodes` from the instance: the pair CPython answers.

NODE-COUNT EQUALITY IS THE LOCKSTEP SIGNAL: `self.nodes += 1` runs
once per entry, so one extra or missing node anywhere in the tree — a
mis-ordered move list, a wrong futility/beta cutoff, a table probe
that hit where CPython missed, a correction scan that ran where
CPython's didn't — breaks the pair. Live in these runs: the tp_score
probe under the dict-key doctrine (`(pos, depth)` tuple keys carrying
the Position value), the history-set membership, the nested `moves()`
generator with recursion through the captured `self`, the killer/
null-move/IID prologue, the verbatim ordering line, the fold with the
virtual-cutoff validation and the mate/stalemate correction (the
pass-4 genexp admission: `depth`/`val_lower` under the immediate
`all(…)` drain), the attribute `+=`, and the table store.

Every expected pair below is CPython's own answer (the shipped module
imported and probed). The tactical rows end at MATE_LOWER = 47923 —
the king-capture sentinel path; the endgame rows walk the correction
(depth 3 at gamma 0 answers the repetition/stalemate-corrected 0). -/

private def sp0 : Span := ⟨0, 0, 0, 0⟩

/-- A fresh shipped `Searcher()` over the real `initWorld`: the world
after `__init__` and the instance address. -/
private def searcherW : Option (World × Addr) :=
  match evalExpr sunfish 4096 ⟨initWorld sunfish, []⟩
      (.call (.name "Searcher" sp0) #[] #[] Option.none sp0) with
  | .ok st (.ref a) => some (st.world, a)
  | _ => Option.none

/-- `(bound, nodes)` of one probe `Searcher().bound(pos, gamma, depth)`
— fresh searcher per probe, exactly the CPython driver. -/
private def boundProbe (pos : RVal) (gamma depth : Int) :
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

/-- Midgame (Italian-shaped, after 1.e4 e5 2.Nf3 Nc6 3.Bc4 Nf6 4.d3
Bc5 — the position the side to move sees). -/
private def posMid : RVal :=
  .ntuple "Position" #["board", "score", "wc", "bc", "ep", "kp"]
    #[.str "         \n         \n r.bqk..r\n pppp.ppp\n ..n..n..\n ..b.p...\n ..B.P...\n ...P.N..\n PPP..PPP\n RNBQK..R\n         \n         \n",
      .int (-13), .tuple #[.bool true, .bool true],
      .tuple #[.bool true, .bool true], .int 0, .int 0]

/-- Tactical (a Scholar's-mate-shaped attack: the side to move has a
mate-band line — the king-capture sentinel path). -/
private def posTac : RVal :=
  .ntuple "Position" #["board", "score", "wc", "bc", "ep", "kp"]
    #[.str "         \n         \n r.bqkb.r\n pppp.ppp\n ..n..n..\n ....p..Q\n ..B.P...\n ........\n PPPP.PPP\n RNB.K.NR\n         \n         \n",
      .int (-38), .tuple #[.bool true, .bool true],
      .tuple #[.bool true, .bool true], .int 0, .int 0]

/-- Rook endgame (KRK-shaped — the mop-up/correction territory). -/
private def posEnd : RVal :=
  .ntuple "Position" #["board", "score", "wc", "bc", "ep", "kp"]
    #[.str "         \n         \n ....k...\n ........\n ....K...\n ........\n .R......\n ........\n ........\n ........\n         \n         \n",
      .int 0, .tuple #[.bool false, .bool false],
      .tuple #[.bool false, .bool false], .int 0, .int 0]

/-- Quiet pawn endgame (kings and one pawn each). -/
private def posPend : RVal :=
  .ntuple "Position" #["board", "score", "wc", "bc", "ep", "kp"]
    #[.str "         \n         \n ....k...\n .....p..\n ........\n ........\n .....P..\n ........\n ....K...\n         \n         \n         \n",
      .int 0, .tuple #[.bool false, .bool false],
      .tuple #[.bool false, .bool false], .int 0, .int 0]

-- the opening board, depths 1-3 across failing-low and failing-high windows
#guard boundProbe (posH 0) 0 1 == some (0, 2)
#guard boundProbe (posH 0) 40 1 == some (37, 35)
#guard boundProbe (posH 0) (-100) 1 == some (0, 2)
#guard boundProbe (posH 0) 0 2 == some (0, 3)
#guard boundProbe (posH 0) 40 2 == some (36, 139)
#guard boundProbe (posH 0) 0 3 == some (0, 39)
#guard boundProbe (posH 0) 40 3 == some (39, 226)
#guard boundProbe (posH 0) (-100) 3 == some ((-46), 3)

-- midgame
#guard boundProbe posMid 0 1 == some (2, 66)
#guard boundProbe posMid 60 1 == some (35, 5)
#guard boundProbe posMid 0 2 == some ((-1), 587)
#guard boundProbe posMid 60 2 == some (59, 241)
#guard boundProbe posMid 0 3 == some (2, 430)
#guard boundProbe posMid 60 3 == some (59, 268)

-- tactical: the mate band (MATE_LOWER exactly — the sentinel discipline)
#guard boundProbe posTac 0 2 == some (47923, 34)
#guard boundProbe posTac 0 3 == some (47923, 67)

-- endgames: the correction arms
#guard boundProbe posEnd 0 1 == some (111, 8)
#guard boundProbe posEnd 0 2 == some (91, 10)
#guard boundProbe posEnd 0 3 == some (0, 3)
#guard boundProbe posEnd 60 3 == some (137, 21)
#guard boundProbe posPend 0 2 == some (19, 3)
#guard boundProbe posPend 60 2 == some (50, 13)
#guard boundProbe posPend 0 3 == some (50, 15)
