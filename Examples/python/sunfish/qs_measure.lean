/-
**F1a — THE QUIESCENCE MEASURE'S CELL CALCULUS.** docs/backlog.md §L30's census
killed all three of §L27's candidate measures and left a fourth standing: the
LEXICOGRAPHIC pair `(pieceCount board, -pstTotal board)`, a function of the BOARD
alone — no window, no score, no table. This file is the board mathematics that
pair's strict descent runs on, and it is the campaign's only new mathematics:
everything else in the fail-low arm is interpreter gates or arithmetic.

**The measure is NOT redefined here.** `pstTotal`, `pieceCount` and `pstAt` are
`faillow_census.lean`'s own definitions — the ones §L30's 12 660 measured edges
were measured with — imported rather than restated, so a re-pin of the census
moves this file with it. `pstTotal_cellSum` and `alphaCount_eq` are the two
bridges: the census's `foldl` over `zipIdx` and its `filter … |>.length`, re-read
as structural sums so an induction has something to walk.

**The string residue is CENSUSED BEFORE any premise is written** (§L30's F1 risk
note, and §L20's copy-the-residue law). `Position.move` builds its board by
STRING SLICING — `put = lambda board, i, p: board[:i] + p + board[i + 1:]`, twice,
then `.rotate()`'s `board[::-1].swapcase()` — while `value` is `pst` arithmetic.
`moveCells` below is that pipeline modelled on `List Char`, and the FIRST thing
in §6 is a `#guard` that it reproduces the engine's own two child boards
character for character. Nothing downstream was stated until that guard passed.

**The one failure mode, stated and not hidden.** `Position.value`'s
castle-transit arm (`if abs(j - self.kp) < 2: score += pst["K"][119 - j]`) adds a
term with NO piece leaving the board, so `val` can be large while `pstTotal`
FALLS — pieces equal, `pstTotal` down, the lex pair NOT descending. The census
could not fire that arm once in 400 positions' full move lists, which is a reason
to state a side condition and not a reason to omit one (§L30's finding 6). It is
stated in two places and both are load-bearing: `qsMeasure_lt_of_board`'s `hpst`
DEMANDS the identity `pstTotal b' = pstTotal b + v` at an unchanged piece count
rather than assuming it, and `cellSum_moveCells`'s `hqj` (the target square is
EMPTY) is what makes that identity true for the plain-move pipeline. The transit
arm is exactly the case those two exclude.

**What F1a does NOT do.** It does not run the shipped `Position.move`, and it
does not prove that the interpreter's two `put`s ARE `List.set` — that bridge,
and the identification of `pstCell p j - pstCell p i` with `Position.value`'s own
`pst[p][j] - pst[p][i]`, is F1b. Here the first is MEASURED on the fixture's two
edges and the second is `#guard`ed against §L29's drained 46 and 42.
-/
import Examples.python.sunfish.faillow_census

namespace Examples.python.sunfish.qs_measure

open LeanModels LeanModels.Python
open Examples.python.sunfish.pins
open Examples.python.sunfish.faillow_census

set_option maxRecDepth 100000

/-! ## §1 The cell, and the sum

`faillow_census.lean`'s `pstTotal` is a `foldl` over `List.zipIdx`. Every lemma
below is an induction, so the first thing owed is the same number read as a
STRUCTURAL sum — and the bridge is a theorem, not a re-definition. -/

/-- **One square's contribution**, in the census's own spelling, copied and not
tidied: the mover's pieces at their own square, the opponent's mirrored through
`119 - i`. -/
def pstCell (c : Char) (i : Nat) : Int :=
  if c.isUpper then pstAt (String.singleton c) i
  else if c.isLower then pstAt (String.singleton c.toUpper) (119 - i)
  else 0

/-- The indexed sum, from an arbitrary starting index. `f` stays free: the whole
calculus below is blind to `pst`, which is what lets a later re-pin of the table
(the shipped `pst["K"]` is swapped once per SEARCH, `sunfish.py:557`) be a rename
here rather than a reproof. -/
def cellSum (f : Char → Nat → Int) : Nat → List Char → Int
  | _, [] => 0
  | i, c :: cs => f c i + cellSum f (i + 1) cs

private theorem foldl_cellSum (f : Char → Nat → Int) :
    ∀ (l : List Char) (i : Nat) (acc : Int),
      (l.zipIdx i).foldl (fun a p => a + f p.1 p.2) acc = acc + cellSum f i l
  | [], i, acc => by simp [cellSum]
  | c :: cs, i, acc => by
      simp only [List.zipIdx_cons, List.foldl_cons, cellSum]
      rw [foldl_cellSum f cs (i + 1) (acc + f c i)]
      omega

private theorem census_body :
    (fun (a : Int) (p : Char × Nat) =>
      if p.1.isUpper then a + pstAt (String.singleton p.1) p.2
      else if p.1.isLower then a + pstAt (String.singleton p.1.toUpper) (119 - p.2) else a)
    = (fun (a : Int) (p : Char × Nat) => a + pstCell p.1 p.2) := by
  funext a p
  unfold pstCell
  rcases Bool.eq_false_or_eq_true p.1.isUpper with h1 | h1 <;>
    rcases Bool.eq_false_or_eq_true p.1.isLower with h2 | h2 <;> simp [h1, h2]

/-- **THE BRIDGE.** The census's measured `pstTotal` IS `cellSum pstCell` — so
every lemma below is about the number §L30 ran on 12 660 edges, and not about a
neighbouring one. -/
theorem pstTotal_cellSum (b : String) : pstTotal b = cellSum pstCell 0 b.toList := by
  unfold pstTotal
  rw [census_body, foldl_cellSum pstCell b.toList 0 0]
  omega

/-! ## §2 The `set` calculus — one square at a time -/

theorem cellSum_append (f : Char → Nat → Int) :
    ∀ (l₁ l₂ : List Char) (i : Nat),
      cellSum f i (l₁ ++ l₂) = cellSum f i l₁ + cellSum f (i + l₁.length) l₂
  | [], l₂, i => by simp [cellSum]
  | c :: cs, l₂, i => by
      have h : i + 1 + cs.length = i + (cs.length + 1) := by omega
      simp only [List.cons_append, cellSum, List.length_cons]
      rw [cellSum_append f cs l₂ (i + 1), h]
      omega

theorem cellSum_single (f : Char → Nat → Int) (c : Char) (i : Nat) :
    cellSum f i [c] = f c i := by simp [cellSum]

theorem cellSum_map (f : Char → Nat → Int) (g : Char → Char) :
    ∀ (l : List Char) (i : Nat),
      cellSum f i (l.map g) = cellSum (fun c k => f (g c) k) i l
  | [], i => by simp [cellSum]
  | c :: cs, i => by
      simp only [List.map_cons, cellSum]
      rw [cellSum_map f g cs (i + 1)]

/-- **A single `put`, at the sum.** The square's old contribution leaves and the
new one arrives; nothing else moves. This is `board[:k] + c + board[k+1:]` at the
list level, and §6's `#guard` is what says the interpreter's slicing agrees. -/
theorem cellSum_set (f : Char → Nat → Int) :
    ∀ (l : List Char) (k : Nat) (c : Char) (i : Nat) (h : k < l.length),
      cellSum f i (l.set k c) = cellSum f i l - f (l[k]'h) (i + k) + f c (i + k)
  | c₀ :: cs, 0, c, i, h => by
      simp only [List.set_cons_zero, cellSum, List.getElem_cons_zero, Nat.add_zero]
      omega
  | c₀ :: cs, k + 1, c, i, h => by
      have h' : k < cs.length := by simpa using h
      have hik : i + 1 + k = i + (k + 1) := by omega
      simp only [List.set_cons_succ, cellSum, List.getElem_cons_succ]
      rw [cellSum_set f cs k c (i + 1) h', hik]
      omega

/-! ## §3 The rotate, at the sum

`Position.move` returns `Position(...).rotate()`, and `rotate` is
`self.board[::-1].swapcase()`. `pstTotal` is BUILT to be blind to it — that is
what makes it `pos.score`'s companion (the score is the two sides' DIFFERENCE and
this is their SUM) rather than a second copy of it — but blind by construction is
not blind by proof, and this is the proof. -/

theorem cellSum_reverse (f g : Char → Nat → Int) (N : Nat) :
    ∀ (l : List Char) (i : Nat), i + l.length ≤ N →
      (∀ c ∈ l, ∀ k, k < N → g c k = f c (N - 1 - k)) →
      cellSum g i l.reverse = cellSum f (N - i - l.length) l
  | [], i, _, _ => by simp [cellSum]
  | c :: cs, i, hle, hfg => by
      simp only [List.length_cons] at hle
      have hcs : i + cs.length ≤ N := by omega
      have hlt : i + cs.length < N := by omega
      have h1 : N - 1 - (i + cs.length) = N - i - (cs.length + 1) := by omega
      have h2 : N - i - cs.length = N - i - (cs.length + 1) + 1 := by omega
      simp only [List.reverse_cons, List.length_cons]
      rw [cellSum_append g cs.reverse [c] i, List.length_reverse,
        cellSum_reverse f g N cs i hcs (fun d hd => hfg d (by simp [hd])),
        cellSum_single, hfg c (by simp) (i + cs.length) hlt, h1, h2]
      simp only [cellSum]
      omega

/-! ## §4 The board alphabet, and the mirror identity

The swap identity is the one place a general ASCII round-trip
(`(c.toLower).toUpper = c`) would be needed — and it is not needed, because a
sunfish board is made of fifteen characters and every fact about a CONCRETE one
is `rfl`. The alphabet is therefore a stated side condition, discharged per
fixture, in preference to an unproved `UInt32` lemma. -/

/-! `swapChar` — Python's `str.swapcase` one character at a time — is the MODEL's
own worker (`LeanModels/Python/Semantics.lean`, `strSwapcase`'s kernel), not a
restatement of it. F1a first wrote a private twin and F1b's census found the two
character-identical; the twin is gone and this file speaks the residue's own
spelling, so the bridge in `move_residue.lean` is a rename and not an argument. -/

/-- The fifteen characters `sunfish.initial` and every `Position.move` output are
built from: the two padding characters, the empty square, and the twelve
pieces. -/
def boardChars : List Char :=
  ['\n', ' ', '.', 'P', 'N', 'B', 'R', 'Q', 'K', 'p', 'n', 'b', 'r', 'q', 'k']

private theorem pstCell_up {c : Char} (h : c.isUpper = true) (i : Nat) :
    pstCell c i = pstAt (String.singleton c) i := by simp [pstCell, h]

private theorem pstCell_low {c : Char} (hu : c.isUpper = false) (h : c.isLower = true) (i : Nat) :
    pstCell c i = pstAt (String.singleton c.toUpper) (119 - i) := by simp [pstCell, hu, h]

private theorem pstCell_none {c : Char} (hu : c.isUpper = false) (hl : c.isLower = false)
    (i : Nat) : pstCell c i = 0 := by simp [pstCell, hu, hl]

theorem pstCell_dot (i : Nat) : pstCell '.' i = 0 := pstCell_none rfl rfl i

private theorem swap_up {c : Char} (hc : c.isUpper = true)
    (hd : (swapChar c).isUpper = false) (hdl : (swapChar c).isLower = true)
    (hdu : (swapChar c).toUpper = c) (i : Nat) :
    pstCell (swapChar c) i = pstCell c (119 - i) := by
  rw [pstCell_low hd hdl, hdu, pstCell_up hc]

private theorem swap_low {c : Char} (hc : c.isUpper = false) (hcl : c.isLower = true)
    (hd : (swapChar c).isUpper = true) (hcu : c.toUpper = swapChar c) (i : Nat)
    (hi : i ≤ 119) : pstCell (swapChar c) i = pstCell c (119 - i) := by
  have hii : 119 - (119 - i) = i := by omega
  rw [pstCell_up hd, pstCell_low hc hcl, hcu, hii]

private theorem swap_none {c : Char} (hu : c.isUpper = false) (hl : c.isLower = false)
    (hswap : swapChar c = c) (i : Nat) :
    pstCell (swapChar c) i = pstCell c (119 - i) := by
  rw [hswap, pstCell_none hu hl, pstCell_none hu hl]

/-- **THE MIRROR IDENTITY.** Swapping a board character's case and reading it at
`i` is reading it unswapped at `119 - i` — which is exactly why `pstTotal` cannot
see a rotation. Fifteen cases; every `rfl` below is a closed `Char` fact. -/
theorem pstCell_swapChar (c : Char) (hc : c ∈ boardChars) (i : Nat) (hi : i ≤ 119) :
    pstCell (swapChar c) i = pstCell c (119 - i) := by
  simp only [boardChars, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;>
    first
      | exact swap_none rfl rfl rfl i
      | exact swap_up rfl rfl rfl rfl i
      | exact swap_low rfl rfl rfl rfl i hi

/-- …and the swap does not move a character across the alpha test, nor out of the
alphabet — the same fact for `pieceCount`, and what keeps the rotate invisible to
both halves of the pair. -/
theorem isAlpha_swapChar (c : Char) (hc : c ∈ boardChars) :
    (swapChar c).isAlpha = c.isAlpha := by
  simp only [boardChars, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;> rfl

theorem swapChar_mem (c : Char) (hc : c ∈ boardChars) : swapChar c ∈ boardChars := by
  simp only [boardChars, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;> decide

/-! ## §5 The piece count, on the same template

`pieceCount` is `filter … |>.length`, which is no more an induction target than
`foldl` was. `alphaCount` is the structural twin and `alphaCount_eq` is its
bridge; after that the three lemmas are `cellSum`'s, one component down. -/

def alphaCount : List Char → Nat
  | [] => 0
  | c :: cs => (if c.isAlpha then 1 else 0) + alphaCount cs

theorem alphaCount_eq : ∀ (l : List Char), (l.filter Char.isAlpha).length = alphaCount l
  | [] => rfl
  | c :: cs => by
      have ih := alphaCount_eq cs
      simp only [List.filter_cons, alphaCount]
      rcases Bool.eq_false_or_eq_true c.isAlpha with h | h <;> simp [h, ih] <;> omega

theorem pieceCount_alphaCount (b : String) : pieceCount b = alphaCount b.toList :=
  alphaCount_eq b.toList

theorem alphaCount_append : ∀ (l₁ l₂ : List Char),
    alphaCount (l₁ ++ l₂) = alphaCount l₁ + alphaCount l₂
  | [], l₂ => by simp [alphaCount]
  | c :: cs, l₂ => by
      have ih := alphaCount_append cs l₂
      simp only [List.cons_append, alphaCount]
      omega

theorem alphaCount_reverse : ∀ (l : List Char), alphaCount l.reverse = alphaCount l
  | [] => rfl
  | c :: cs => by
      have ih := alphaCount_reverse cs
      simp only [List.reverse_cons, alphaCount_append, alphaCount]
      omega

theorem alphaCount_map_swapChar : ∀ (l : List Char), (∀ c ∈ l, c ∈ boardChars) →
    alphaCount (l.map swapChar) = alphaCount l
  | [], _ => rfl
  | c :: cs, h => by
      have ih := alphaCount_map_swapChar cs (fun d hd => h d (by simp [hd]))
      have hc := isAlpha_swapChar c (h c (by simp))
      simp only [List.map_cons, alphaCount, hc, ih]

/-- **A single `put`, at the count.** One character leaves and one arrives, so the
count moves by their two alpha bits and by nothing else. -/
theorem alphaCount_set :
    ∀ (l : List Char) (k : Nat) (c : Char) (h : k < l.length),
      alphaCount (l.set k c) + (if (l[k]'h).isAlpha then 1 else 0)
        = alphaCount l + (if c.isAlpha then 1 else 0)
  | c₀ :: cs, 0, c, h => by
      simp only [List.set_cons_zero, alphaCount, List.getElem_cons_zero]
      omega
  | c₀ :: cs, k + 1, c, h => by
      have h' : k < cs.length := by simpa using h
      have ih := alphaCount_set cs k c h'
      simp only [List.set_cons_succ, alphaCount, List.getElem_cons_succ]
      omega

/-! ## §6 THE STRING RESIDUE, CENSUSED FIRST

`Position.move`'s board is two `put`s and a rotate. `moveCells` is that pipeline
on `List Char`; the two `#guard`s under it are the whole reason the premises
below may be written, because they say the model reproduces the ENGINE's own
child boards — `d4B` and `e4B`, which `faillow_census.lean` §3 pinned against
`Position.move` itself. -/

/-- `put(put(board, j, board[i]), i, ".")`, then `board[::-1].swapcase()`. The
`getD` default never fires under `hi` below; it is there because Python's
indexing is total on a 120-character board, and the residue must not acquire a
proof obligation the shipped code does not have.

**This is the PLAIN move and only the plain move.** `Position.move` has three
more `put`s behind conditionals — the castling rook slide, the promotion
replacement, and the EN PASSANT removal at `j + S`. The last one matters for the
side conditions below and §L30's plan did not name it, so it was MEASURED
against CPython before this docstring was written: on a real ep capture
(`Move(56, 45, "")` four plies into the opening tree) the target square is `'.'`,
`Position.value` answers **149**, the piece count goes **32 → 31**, and
`pstTotal` FALLS by **69**.

So an ep capture satisfies `hqj` and still breaks the quiet identity. It is SAFE
for the descent — the count falls, which is §8's FIRST arm, and
`qsMeasure_lt_of_board`'s `hpst` is vacuous there — but it is not this pipeline.
**The classification that matters is the piece COUNT, not whether the target
square is empty**, and F1b's bridge from the shipped `Position.move` to
`moveCells` must exclude `j == self.ep` alongside promotion and castling. -/
def moveCells (L : List Char) (i j : Nat) : List Char :=
  (((L.set j (L.getD i '.')).set i '.').reverse).map swapChar

/-- The same, at the shipped `String`. -/
def plainMoveBoard (b : String) (i j : Nat) : String := String.ofList (moveCells b.toList i j)

/-! **THE CENSUS.** Both of the reference fixture's admitted edges, character for
character against the engine's own output. `1. d4` is `(84, 64)` and `1. e4` is
`(85, 65)`; both are quiet, both targets are `'.'`. -/
#guard plainMoveBoard board0 84 64 == d4B
#guard plainMoveBoard board0 85 65 == e4B
#guard board0.toList.length == 120
#guard board0.toList.getD 84 'x' == 'P' && board0.toList.getD 64 'x' == '.'
#guard board0.toList.getD 85 'x' == 'P' && board0.toList.getD 65 'x' == '.'

/-! …and the bridges hold on the fixture's numbers: the census's `pstTotal` and
`pieceCount` agree with the structural sums, and the per-square delta is §L29's
drained pair. -/
#guard pstTotal board0 == 127158
#guard cellSum pstCell 0 board0.toList == 127158
#guard pieceCount board0 == 32
#guard alphaCount board0.toList == 32
#guard pstCell 'P' 64 - pstCell 'P' 84 == 46
#guard pstCell 'P' 65 - pstCell 'P' 85 == 42

/-! ## §7 THE TWO HALVES, ACROSS A PLAIN MOVE

The identity §L30 ran on 10 368 moves before a line of Lean was written, proved:
a move onto an EMPTY square raises `pstTotal` by exactly the piece's own
`pst[p][j] - pst[p][i]`, which is `Position.value`'s first line, and leaves the
piece count alone. -/

private theorem mem_of_mem_set {l : List Char} {k : Nat} {c d : Char}
    (h : d ∈ l.set k c) : d ∈ l ∨ d = c := by
  induction l generalizing k with
  | nil => simp at h
  | cons a as ih =>
      cases k with
      | zero =>
          simp only [List.set_cons_zero, List.mem_cons] at h
          rcases h with rfl | h
          · exact Or.inr rfl
          · exact Or.inl (by simp [h])
      | succ k =>
          simp only [List.set_cons_succ, List.mem_cons] at h
          rcases h with rfl | h
          · exact Or.inl (by simp)
          · rcases ih h with h' | h'
            · exact Or.inl (by simp [h'])
            · exact Or.inr h'

/-- `getElem?` collapses to `getElem` under a size hypothesis — the law, applied
once so no proof below carries an index proof term through a `rw`. -/
private theorem charAt_of_getElem? {l : List Char} {k : Nat} {c : Char}
    (h : l[k]? = some c) (hk : k < l.length) : l[k]'hk = c := by
  have hg := List.getElem?_eq_getElem hk
  rw [h] at hg
  exact (Option.some.inj hg).symm

/-- The four facts the two arms share, so no proof re-derives them. `q` is the
character ON the target square: `'.'` for the quiet arm and a piece for the
capture arm, which is the ONLY place the two differ. -/
private structure MoveFacts (L : List Char) (i j : Nat) (p q : Char) : Prop where
  gi : L.getD i '.' = p
  ej : ∀ h : j < L.length, L[j]'h = q
  pm : (∀ c ∈ L, c ∈ boardChars) → p ∈ boardChars
  ps : ∀ (r : Char) (h : i < (L.set j r).length), i ≠ j → (L.set j r)[i]'h = p

private theorem moveFacts (L : List Char) (i j : Nat) (p q : Char)
    (hlen : L.length = 120) (hi : i < 120) (_hj : j < 120)
    (hpi : L[i]? = some p) (hqj : L[j]? = some q) : MoveFacts L i j p q := by
  have hiL : i < L.length := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [List.getD_eq_getElem?_getD, hpi]; rfl
  · intro h; exact charAt_of_getElem? hqj h
  · intro hchars
    rw [← charAt_of_getElem? hpi hiL]; exact hchars _ (List.getElem_mem hiL)
  · intro q h hne
    refine charAt_of_getElem? ?_ h
    rw [List.getElem?_set_ne (by omega)]
    exact hpi

private theorem memX (L : List Char) (i j : Nat) (p : Char)
    (hchars : ∀ c ∈ L, c ∈ boardChars) (hp : p ∈ boardChars) :
    ∀ c ∈ (L.set j p).set i '.', c ∈ boardChars := by
  intro c hc
  rcases mem_of_mem_set hc with hc' | rfl
  · rcases mem_of_mem_set hc' with hc'' | rfl
    · exact hchars c hc''
    · exact hp
  · decide

/-- **THE QUIET IDENTITY**, at the list level. `hqj` is the target square being
EMPTY — the capture case descends in the count instead and is §8's other arm. -/
theorem cellSum_moveCells (L : List Char) (i j : Nat) (p : Char)
    (hlen : L.length = 120)
    (hchars : ∀ c ∈ L, c ∈ boardChars)
    (hi : i < 120) (hj : j < 120) (hij : i ≠ j)
    (hpi : L[i]? = some p) (hqj : L[j]? = some '.') :
    cellSum pstCell 0 (moveCells L i j)
      = cellSum pstCell 0 L + (pstCell p j - pstCell p i) := by
  obtain ⟨hgetD, hej, hpm, hps⟩ := moveFacts L i j p '.' hlen hi hj hpi hqj
  have hjL : j < L.length := by omega
  have hlen2 : ((L.set j p).set i '.').length = 120 := by simp [hlen]
  have hiL1 : i < (L.set j p).length := by simp [hlen]; omega
  have hmemX := memX L i j p hchars (hpm hchars)
  have hpi' : (L.set j p)[i]'hiL1 = p := hps p hiL1 hij
  have hrot : cellSum pstCell 0 (moveCells L i j)
      = cellSum pstCell 0 ((L.set j p).set i '.') := by
    rw [moveCells, hgetD, cellSum_map pstCell swapChar,
      cellSum_reverse pstCell (fun c k => pstCell (swapChar c) k) 120
        ((L.set j p).set i '.') 0 (by omega)
        (fun c hc k hk => pstCell_swapChar c (hmemX c hc) k (by omega)),
      hlen2]
  rw [hrot, cellSum_set pstCell (L.set j p) i '.' 0 hiL1, hpi',
    cellSum_set pstCell L j p 0 hjL, hej hjL, pstCell_dot, pstCell_dot,
    Nat.zero_add, Nat.zero_add]
  omega

/-- The same, at the shipped `String`, in `pstTotal`'s own words. -/
theorem pstTotal_plainMove (b : String) (i j : Nat) (p : Char)
    (hlen : b.toList.length = 120)
    (hchars : ∀ c ∈ b.toList, c ∈ boardChars)
    (hi : i < 120) (hj : j < 120) (hij : i ≠ j)
    (hpi : b.toList[i]? = some p) (hqj : b.toList[j]? = some '.') :
    pstTotal (plainMoveBoard b i j) = pstTotal b + (pstCell p j - pstCell p i) := by
  rw [pstTotal_cellSum, pstTotal_cellSum, plainMoveBoard, String.toList_ofList]
  exact cellSum_moveCells b.toList i j p hlen hchars hi hj hij hpi hqj

/-- **AND THE COUNT DOES NOT MOVE.** A quiet move puts a piece where an empty
square was and leaves an empty square behind — which is precisely why the
fixture's own two edges refute §L27's first candidate and need the pair's second
component. -/
theorem pieceCount_plainMove (b : String) (i j : Nat) (p : Char)
    (hlen : b.toList.length = 120)
    (hchars : ∀ c ∈ b.toList, c ∈ boardChars)
    (hi : i < 120) (hj : j < 120) (hij : i ≠ j)
    (halpha : p.isAlpha = true)
    (hpi : b.toList[i]? = some p) (hqj : b.toList[j]? = some '.') :
    pieceCount (plainMoveBoard b i j) = pieceCount b := by
  obtain ⟨hgetD, hej, hpm, hps⟩ := moveFacts b.toList i j p '.' hlen hi hj hpi hqj
  have hjL : j < b.toList.length := by omega
  have hiL1 : i < (b.toList.set j p).length := by simp [hlen]; omega
  have hmemX := memX b.toList i j p hchars (hpm hchars)
  have hpi' : (b.toList.set j p)[i]'hiL1 = p := hps p hiL1 hij
  have h2 := alphaCount_set (b.toList.set j p) i '.' hiL1
  have h1 := alphaCount_set b.toList j p hjL
  rw [hpi'] at h2
  rw [hej hjL] at h1
  have hdot : ('.' : Char).isAlpha = false := rfl
  rw [pieceCount_alphaCount, pieceCount_alphaCount, plainMoveBoard, String.toList_ofList,
    moveCells, hgetD,
    alphaCount_map_swapChar _ (fun c hc => hmemX c (by simpa using hc)),
    alphaCount_reverse]
  simp only [halpha, hdot, if_false, Bool.false_eq_true, if_pos] at h1 h2
  omega

/-- **THE CAPTURE ARM.** When the target square holds a PIECE the count falls by
exactly one: the piece that was standing there is overwritten and the square the
mover left becomes empty. `alphaCount_set` is applied twice, once per `put`, and
the two alpha bits do the rest.

Note what this arm does NOT need: no QS floor, no `pstTotal`, no hypothesis about
the move's value at all. A capture descends because a piece left the board, which
is why §8's first component exists. -/
theorem pieceCount_plainMove_capture (b : String) (i j : Nat) (p q : Char)
    (hlen : b.toList.length = 120)
    (hchars : ∀ c ∈ b.toList, c ∈ boardChars)
    (hi : i < 120) (hj : j < 120) (hij : i ≠ j)
    (halpha : p.isAlpha = true) (hqa : q.isAlpha = true)
    (hpi : b.toList[i]? = some p) (hqj : b.toList[j]? = some q) :
    pieceCount (plainMoveBoard b i j) + 1 = pieceCount b := by
  obtain ⟨hgetD, hej, hpm, hps⟩ := moveFacts b.toList i j p q hlen hi hj hpi hqj
  have hjL : j < b.toList.length := by omega
  have hiL1 : i < (b.toList.set j p).length := by simp [hlen]; omega
  have hmemX := memX b.toList i j p hchars (hpm hchars)
  have hpi' : (b.toList.set j p)[i]'hiL1 = p := hps p hiL1 hij
  have h2 := alphaCount_set (b.toList.set j p) i '.' hiL1
  have h1 := alphaCount_set b.toList j p hjL
  rw [hpi'] at h2
  rw [hej hjL] at h1
  have hdot : ('.' : Char).isAlpha = false := rfl
  rw [pieceCount_alphaCount, pieceCount_alphaCount, plainMoveBoard, String.toList_ofList,
    moveCells, hgetD,
    alphaCount_map_swapChar _ (fun c hc => hmemX c (by simpa using hc)),
    alphaCount_reverse]
  simp only [halpha, hqa, hdot, if_false, Bool.false_eq_true, if_pos] at h1 h2
  omega

/-! ## §8 THE MEASURE, AND ITS STRICT DESCENT -/

/-- **§L30's surviving measure.** A function of the BOARD alone — which is what
makes the fuel index the position and lets `gamma` stay universally quantified
inside the strengthened statement F2 will write (§L30's finding 2). -/
def qsMeasure (b : String) : Nat × Int := (pieceCount b, -pstTotal b)

/-- Lexicographic strict order on the pair. Stated rather than imported:
`Prod.Lex` is Mathlib and this repository is core-only. -/
def qsLt (x y : Nat × Int) : Prop := x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 < y.2)

/-- A `Bool` mirror so a `#guard` can read the order — and the two-line proof
that it is the same proposition, on `reportB_iff`'s template: a mirror that
drifted from its `Prop` would make every guard in §9 say nothing. -/
def qsLtB (x y : Nat × Int) : Bool :=
  decide (x.1 < y.1) || (decide (x.1 = y.1) && decide (x.2 < y.2))

theorem qsLtB_iff (x y : Nat × Int) : qsLtB x y = true ↔ qsLt x y := by
  simp [qsLtB, qsLt]

/-- **THE DESCENT.** Two arms, one line each, exactly as §L30 read them off
`Position.value`: a move that TAKES a piece drops `pieceCount`; a move that does
not leaves it alone and raises `pstTotal` by its own admitted value, which the QS
filter forces to be at least `QS = 40 > 0`.

`hpst` is where the castle-transit side condition is STATED. The transit arm is
exactly the case where a move leaves the piece count alone and does NOT raise
`pstTotal` by the value the filter admitted, so a caller that discharges `hpst`
has ruled it out; a caller that cannot must fall back on the `-60000`
king-capture leaf §L30 names, and must say so. -/
theorem qsMeasure_lt_of_board {b b' : String} {v : Int}
    (hv : 40 ≤ v)
    (hpc : pieceCount b' ≤ pieceCount b)
    (hpst : pieceCount b' = pieceCount b → pstTotal b' = pstTotal b + v) :
    qsLt (qsMeasure b') (qsMeasure b) := by
  by_cases h : pieceCount b' = pieceCount b
  · refine Or.inr ⟨h, ?_⟩
    have hd := hpst h
    show -pstTotal b' < -pstTotal b
    omega
  · exact Or.inl (by show pieceCount b' < pieceCount b; omega)

/-- **THE PLAIN-MOVE COROLLARY**, both halves composed: §7's two identities feed
§8's two arms, and what is left is the QS floor on the move's own value. -/
theorem qsMeasure_plainMove_lt (b : String) (i j : Nat) (p : Char)
    (hlen : b.toList.length = 120)
    (hchars : ∀ c ∈ b.toList, c ∈ boardChars)
    (hi : i < 120) (hj : j < 120) (hij : i ≠ j)
    (halpha : p.isAlpha = true)
    (hpi : b.toList[i]? = some p) (hqj : b.toList[j]? = some '.')
    (hfloor : 40 ≤ pstCell p j - pstCell p i) :
    qsLt (qsMeasure (plainMoveBoard b i j)) (qsMeasure b) :=
  qsMeasure_lt_of_board hfloor
    (Nat.le_of_eq (pieceCount_plainMove b i j p hlen hchars hi hj hij halpha hpi hqj))
    (fun _ => pstTotal_plainMove b i j p hlen hchars hi hj hij hpi hqj)

/-- **THE CAPTURE COROLLARY** — the pair's FIRST component alone, and it needs no
floor. -/
theorem qsMeasure_plainMove_capture_lt (b : String) (i j : Nat) (p q : Char)
    (hlen : b.toList.length = 120)
    (hchars : ∀ c ∈ b.toList, c ∈ boardChars)
    (hi : i < 120) (hj : j < 120) (hij : i ≠ j)
    (halpha : p.isAlpha = true) (hqa : q.isAlpha = true)
    (hpi : b.toList[i]? = some p) (hqj : b.toList[j]? = some q) :
    qsLt (qsMeasure (plainMoveBoard b i j)) (qsMeasure b) := by
  refine Or.inl ?_
  show pieceCount (plainMoveBoard b i j) < pieceCount b
  have hc := pieceCount_plainMove_capture b i j p q hlen hchars hi hj hij halpha hqa hpi hqj
  omega

/-! ## §9 INSTANTIATED — the reference fixture's two edges

The pair descends on both edges the opening position admits, and it descends in
the SECOND component on both: §L27's first candidate stands still (32 → 32 → 32,
the census's own refutation) while `pstTotal` rises by 46 and 42 — the two values
§L29 drained and `Position.value` computes. -/
#guard pieceCount d4B == 32 && pieceCount e4B == 32
#guard pstTotal d4B - pstTotal board0 == 46
#guard pstTotal e4B - pstTotal board0 == 42
#guard qsLtB (qsMeasure d4B) (qsMeasure board0)
#guard qsLtB (qsMeasure e4B) (qsMeasure board0)

/-! And the order is not vacuous: it does NOT hold backwards, which is the shape
a `pstTotal` that FALLS at an unchanged piece count would have — the castle
transit's signature, and what `hpst` exists to exclude. -/
#guard !qsLtB (qsMeasure board0) (qsMeasure d4B)

/-! ### The CAPTURE arm, on a real search edge

The opening board admits no capture, so this arm's fixture is a position four
plies in, reached by `gen_moves` and measured against CPython BEFORE it was
written down: `P` on 63 takes `p` on 54, `Position.value` answers **111**, the
count goes **32 → 31**, and `pstTotal` **FALLS by 101**.

That fall is the point. The lex pair descends here through its FIRST component
ONLY, and the second component moves the WRONG way — so a measure that had
`pstTotal` alone would not descend on a capture at all, and §L27's first
candidate (`pieceCount` alone) would not descend on the quiet edges of §9. Each
component is refuted on its own by the other arm's fixture, and neither refutes
the pair. -/
private def capB : String :=
  "\n         \n         \nrnbkqbnr \nppp.ppp. \n.......p \n...p.... \n..P..... \n........ \nPP.PPPPP \nRNBKQBNR \n         \n         "
private def capChildB : String :=
  "         \n         \n rnbqkbnr\n ppppp.pp\n ........\n ........\n ....p...\n P.......\n .PPP.PPP\n RNBQKBNR\n         \n         \n"

/-! The residue first, as always: the model's pipeline reproduces the engine's own
child board on the capture edge too, not only on the two quiet ones. -/
#guard plainMoveBoard capB 63 54 == capChildB
#guard capB.toList.length == 120 && capChildB.toList.length == 120
#guard capB.toList.getD 63 'x' == 'P' && capB.toList.getD 54 'x' == 'p'
#guard pieceCount capB == 32 && pieceCount capChildB == 31
#guard pstTotal capB == 127226 && pstTotal capChildB == 127125
#guard qsLtB (qsMeasure capChildB) (qsMeasure capB)
#guard !qsLtB (qsMeasure capB) (qsMeasure capChildB)

/-! …and the second component really does move the wrong way here, which is the
guard that would fail if anybody dropped `pieceCount` from the pair. -/
#guard decide (pstTotal capChildB < pstTotal capB)

/-! ### The premises, RUN rather than admired

§L24's finding 1 is the standing law: *a premise is not paid until something
DISCHARGES it.* `qsMeasure_lt_of_board`'s hypotheses are collected into one
`Bool` so the fixture answers whether they are SATISFIED, and
`qsMeasure_lt_of_descendsB` is the theorem that consumes the answer.

**Why a `#guard` and not a `decide`-closed theorem.** `pstTotal` reads the live
`pst` out of `initWorld sunfish`, whose module initialiser pads and joins the
tables at elaboration time; the elaborator runs that in milliseconds and the
KERNEL would not. So the fixture instantiation is a guard through a proved
mirror — the same shape `faillow_census.lean`'s `reportB`/`reportB_iff` takes,
and for the same reason. -/
def descendsB (b b' : String) (v : Int) : Bool :=
  decide (40 ≤ v) &&
    decide (pieceCount b' < pieceCount b
      ∨ (pieceCount b' = pieceCount b ∧ pstTotal b' = pstTotal b + v))

theorem qsMeasure_lt_of_descendsB {b b' : String} {v : Int} (h : descendsB b b' v = true) :
    qsLt (qsMeasure b') (qsMeasure b) := by
  simp only [descendsB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hv, hcase⟩ := h
  rcases hcase with hlt | ⟨he, hp⟩
  · exact Or.inl hlt
  · exact qsMeasure_lt_of_board hv (Nat.le_of_eq he) (fun _ => hp)

/-! Both edges: the premises HOLD at the fixture's own two values, and so does
the conclusion the theorem draws from them. -/
#guard descendsB board0 d4B 46 && qsLtB (qsMeasure d4B) (qsMeasure board0)
#guard descendsB board0 e4B 42 && qsLtB (qsMeasure e4B) (qsMeasure board0)

/-! And they are not trivially satisfiable: below the QS floor the same board pair
is REFUSED, which is where the filter earns its place in the argument. -/
#guard !descendsB board0 d4B 39

/-! ### The axioms -/

#print axioms pstTotal_cellSum
#print axioms cellSum_append
#print axioms cellSum_single
#print axioms cellSum_map
#print axioms cellSum_set
#print axioms cellSum_reverse
#print axioms pstCell_dot
#print axioms pstCell_swapChar
#print axioms isAlpha_swapChar
#print axioms swapChar_mem
#print axioms alphaCount_eq
#print axioms pieceCount_alphaCount
#print axioms alphaCount_append
#print axioms alphaCount_reverse
#print axioms alphaCount_map_swapChar
#print axioms alphaCount_set
#print axioms cellSum_moveCells
#print axioms pstTotal_plainMove
#print axioms pieceCount_plainMove
#print axioms qsLtB_iff
#print axioms qsMeasure_lt_of_board
#print axioms pieceCount_plainMove_capture
#print axioms qsMeasure_plainMove_lt
#print axioms qsMeasure_plainMove_capture_lt
#print axioms qsMeasure_lt_of_descendsB

end Examples.python.sunfish.qs_measure
