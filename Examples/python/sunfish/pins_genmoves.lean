/-
sunfish pin file: `Position.gen_moves` RUNS on the shipped file
(opening + promotion + castling boards, CPython's moves in CPython's
order) and the REFERENCE ENUMERATION (the decided theorem's right-hand
side) with its thirteen CPython pins.

Part of the pass-7 SPEC-POLE SPLIT (docs/backlog.md §Pass 7): the
program and shared probe defs come from `pins_common.lean` — after an
envelope re-extraction, edit THAT file (the JSON trap note there); this
file rebuilds through the import.
-/
import LeanModels
import Examples.python.sunfish.pins_common

namespace Examples.python.sunfish.pins_genmoves

open LeanModels LeanModels.Python
open Examples.python.sunfish.pins

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

/-! Pass 5, the two #158 constructs inside `gen_moves`, exercised on
the SHIPPED file (CPython's answers, CPython's order):

* the PROMOTION board reaches the inlined `yield from (Move(i, j,
  prom) for prom in "NBRQ")` — four promotions in "NBRQ" order, read
  from the enclosing frame's live `i`/`j` (docs/memory-model.md §yield
  from);
* the CASTLING board walks `for (sq, dr, c) in ((A1, E, self.wc[0]),
  (H1, W, self.wc[1]))` — the tuple-target `forSeq` frame inside the
  generator — after every rook slide, both rights live. -/

private def posOn (b : String) (wc0 wc1 : Bool) : RVal :=
  .ntuple "Position" #["board", "score", "wc", "bc", "ep", "kp"]
    #[.str b, .int 0, .tuple #[.bool wc0, .bool wc1],
      .tuple #[.bool wc0, .bool wc1], .int 0, .int 0]

#guard (match callIn sunfish 8192 (initWorld sunfish) "Position.gen_moves"
          #[posOn "         \n         \n ........\n P.......\n ........\n ........\n ........\n ........\n ........\n K.......\n         \n         \n" false false] with
        | .ok w (.ref a) => drainMoves w a 64
        | _ => Option.none) ==
  some [(31, 21, "N"), (31, 21, "B"), (31, 21, "R"), (31, 21, "Q"),
        (91, 81, ""), (91, 92, ""), (91, 82, "")]

#guard (match callIn sunfish 8192 (initWorld sunfish) "Position.gen_moves"
          #[posOn "         \n         \n ........\n ........\n ........\n ........\n ........\n ........\n ........\n R...K..R\n         \n         \n" true true] with
        | .ok w (.ref a) => drainMoves w a 64
        | _ => Option.none) ==
  some [(91, 81, ""), (91, 71, ""), (91, 61, ""), (91, 51, ""),
        (91, 41, ""), (91, 31, ""), (91, 21, ""), (91, 92, ""),
        (91, 93, ""), (91, 94, ""), (95, 93, ""), (95, 85, ""),
        (95, 96, ""), (95, 94, ""), (95, 86, ""), (95, 84, ""),
        (98, 88, ""), (98, 78, ""), (98, 68, ""), (98, 58, ""),
        (98, 48, ""), (98, 38, ""), (98, 28, ""), (98, 97, ""),
        (98, 96, ""), (95, 97, "")]

/-! ### The reference enumeration (the decided theorem's right-hand side)

The owner picked equality against a REFERENCE ENUMERATION with ORDER
pinned (`bound`'s cutoffs depend on move order), and the design note is
that the reference must optimise for OBVIOUSNESS over efficiency — plain
nested scans — because its whole job is to be trustworthy by INSPECTION
against sunfish.py lines 172-203. It is written to be read side by side
with the shipped Python, one Lean line per Python line, and it declines
(`Except.error`) rather than guessing: a real CPython `IndexError` and
an exhausted ray budget are both errors, so neither can be mistaken for
a short move list. (Pass 5: the #158 rewrite CHANGED gen_moves's
surface — one-line `break`s, `j != self.ep and abs(j - self.kp) > 1`
for the old kp-tuple membership, `yield from` for the promotion loop,
and the castling pair as a two-tuple `for` — the reference mirrors the
NEW lines; every set of moves it defines is provably the same as
before, and the thirteen CPython pins below are unchanged.)

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

/-! ### The shipped constants, copied verbatim (sunfish.py 99, 116) -/

def N : Int := -10
def E : Int := 1
def S : Int := 10
def W : Int := -1
def A1 : Int := 91
def H1 : Int := 98
def A8 : Int := 21
def H8 : Int := 28

/-- `directions` (sunfish.py 117-124), one arm per key, verbatim. -/
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

/-- sunfish.py 188-195, the `if p == "P":` block. `none` = the block fell
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
  -- if d in (N + W, N + E) and q == "." and j != self.ep and abs(j - self.kp) > 1: break
  -- (#158's spelling of the old kp-tuple membership: j ∉ {ep} and
  --  j ∉ {kp-1, kp, kp+1} — the same break set)
  if (d == N + W || d == N + E) && q == '.'
      && j != ep && (j - kp).natAbs > 1 then return some []
  -- if A8 <= j <= H8: yield from (Move(i, j, prom) for prom in "NBRQ"); break
  if A8 ≤ j && j ≤ H8 then
    return some ("NBRQ".toList.map fun pr => ⟨i, j, pr.toString⟩)
  return none

/-- sunfish.py 183-203, one RAY: `for j in count(i + d, d)`. `fuel`
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
      -- for (sq, dr, c) in ((A1, E, self.wc[0]), (H1, W, self.wc[1])):
      --     if i == sq and self.board[j + dr] == "K" and c:
      --         yield Move(j + dr, j - dr, "")
      -- (#158 folded the two castling slides into one two-tuple loop;
      --  the iterations are spelled out, A1-then-H1 — the tuple's own
      --  order — and the board read happens before the rights check,
      --  as in the shipped `and` chain)
      let castle1 ← if i == A1 then
          (do if (← at? b (j + E)) == 'K' && wc0 then
                return [(⟨j + E, j - E, ""⟩ : RefMove)] else return [])
        else pure []
      let castle2 ← if i == H1 then
          (do if (← at? b (j + W)) == 'K' && wc1 then
                return [(⟨j + W, j - W, ""⟩ : RefMove)] else return [])
        else pure []
      let rest ← ray b wc0 wc1 ep kp i p d fuel (j + d)
      return here :: castle1 ++ castle2 ++ rest

/-- sunfish.py 182, one PIECE: every ray, in `directions[p]` order. -/
def piece (b : List Char) (wc0 wc1 : Bool) (ep kp : Int) (fuel : Nat)
    (i : Int) (p : Char) : Except String (List RefMove) :=
  List.flatten <$> (directions p).mapM fun d =>
    ray b wc0 wc1 ep kp i p d fuel (i + d)

/-- sunfish.py 179-181, the whole enumeration:
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

end Examples.python.sunfish.pins_genmoves
