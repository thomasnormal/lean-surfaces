/-
**F1b-i — THE INTERPRETER'S STRING RESIDUE, and the bridge to F1a's
`moveCells`.** docs/backlog.md §L37 left F1b owing three things, of which this is
the first and the one §L30 named as F1's RISK: *"`Position.move` builds its board
by STRING SLICING while `value` is `pst` arithmetic — so this is a string lemma,
not an omega."* Here is the string lemma.

**The residue was censused before a premise was written** (§L24's exit law,
§L20's copy-the-residue law). §1 runs all four of the model's string workers on
the shipped board and pins what they answer; every statement below was written
against those shapes and not against a reading of `sunfish.py`.

**`swapChar` is the MODEL's worker, and F1a's twin is gone.** The census's first
finding: `LeanModels/Python/Semantics.lean`'s `swapChar` is character-identical to
the `swapCase` F1a had written for itself (`example : swapChar = swapCase := rfl`
passed on the first run). One definition survives — the interpreter's — so
`qs_measure.lean` now speaks the residue's own spelling and the bridge below is a
rename rather than an argument.

**What this file does NOT do.** It does not gate `Position.move`. That method is
THIRTEEN statements — two unpacks, a `defStmt` binding the `put` lambda, seven
assignments, two `if`s with their own inner `put`s, and a `return` through
`.rotate()` — and none of them is `Stmt.unsupported`, so the gate is a full inch
on the scale of `Position.value`'s eight (§L28). Its exit law is measured in §1
and left for F1b-ii, where the measurement already decides the statement's shape:
the call ALLOCATES exactly one object (the closure) and MUTATES nothing.
-/
import Examples.python.sunfish.qs_measure

namespace Examples.python.sunfish.move_residue

open LeanModels LeanModels.Python
open Examples.python.sunfish.pins
open Examples.python.sunfish.basecase_depth0 (mvOf)
open Examples.python.sunfish.faillow_census (pstAt pstRowOf)
open Examples.python.sunfish.qs_measure

set_option maxRecDepth 100000

/-! ## §1 THE CENSUS — the four workers, run on the shipped board

`put = lambda board, i, p: board[:i] + p + board[i + 1:]` is two slices and two
appends; `rotate` is `self.board[::-1].swapcase()`. That is four calls into the
model's frozen VALUE workers, and these are the shapes they answer with. -/

#guard board0.length == 120
#guard board0.length == board0.toList.length
#guard strAscii board0

/-! `board[:i]` — the prefix. -/
#guard strSlice board0 .none (.int 84) .none
    == .ok (.str (String.ofList (board0.toList.take 84)))
/-! `board[i + 1:]` — the suffix. -/
#guard strSlice board0 (.int 85) .none .none
    == .ok (.str (String.ofList (board0.toList.drop 85)))
/-! `board[::-1]` — the rotate's reversal, a NEGATIVE-step slice, which is a
different arm of `strSlice` from the two above. -/
#guard strSlice board0 .none .none (.int (-1))
    == .ok (.str (String.ofList board0.toList.reverse))
/-! `.swapcase()`. -/
#guard strSwapcase board0 == .ok (.str (String.ofList (board0.toList.map swapChar)))

/-! And the two `put`s composed, at the fixture's own `1. d4` squares: the board
the interpreter builds before rotating is `List.set` twice. -/
#guard (String.ofList (board0.toList.take 64) ++ String.singleton 'P'
        ++ String.ofList (board0.toList.drop 65)).toList == board0.toList.set 64 'P'

/-! ### `Position.move`'s OWN exit law, measured for F1b-ii

The law says the heap and the fuel come before the premise, and here the
measurement decides the next inch's statement shape outright. `Position.move` on
the fixture allocates **one** object — the `put` lambda's closure — and changes
**no** existing slot, so its gate's conclusion is a single-object append and not
an update. The minimum fuel is **32**; 31 refuses. -/
private def mvRun (F : Nat) : Option (Nat × Nat × List Nat) :=
  match callIn sunfish F (initWorld sunfish) "Position.move" #[posH 0, mvOf 84 64 ""] with
  | .ok w _ =>
    some ((initWorld sunfish).heap.size, w.heap.size,
      (List.range w.heap.size).filter
        (fun k => Heap.get? (initWorld sunfish).heap k != Heap.get? w.heap k))
  | _ => Option.none

#guard mvRun 32 == some (66, 67, [66])
#guard (mvRun 31).isNone

/-! ## §2 `strSliceChars`, at the two steps the shipped code uses

`strSliceChars` walks by an `Int` step from an `Int` index, so both directions
are one definition. The shipped code uses exactly two instantiations — `+1` for
the two `put` slices and `-1` for the rotate — and each collapses to a `List`
operation under the size hypothesis the slice's own bounds supply. -/

theorem strSliceChars_fwd : ∀ (n i : Nat) (cs : List Char), i + n ≤ cs.length →
    strSliceChars cs n (i : Int) 1 = (cs.drop i).take n
  | 0, i, cs, _ => by simp [strSliceChars]
  | n + 1, i, cs, h => by
      have hi : i < cs.length := by omega
      have hn : ((i : Int)).toNat = i := by simp
      have hg : cs.getD ((i : Int)).toNat ' ' = cs[i]'hi := by
        rw [hn, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
      have hc : ((i : Int) + 1) = ((i + 1 : Nat) : Int) := by omega
      rw [strSliceChars, hg, hc, strSliceChars_fwd n (i + 1) cs (by omega),
        List.drop_eq_getElem_cons hi, List.take_succ_cons]

theorem strSliceChars_rev : ∀ (n : Nat) (cs : List Char), n ≤ cs.length →
    strSliceChars cs n ((n : Int) - 1) (-1) = (cs.take n).reverse
  | 0, cs, _ => by simp [strSliceChars]
  | n + 1, cs, h => by
      have hi : n < cs.length := by omega
      have hn : ((((n + 1 : Nat) : Int) - 1)).toNat = n := by omega
      have hg : cs.getD ((((n + 1 : Nat) : Int) - 1)).toNat ' ' = cs[n]'hi := by
        rw [hn, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
      have hstep : (((n + 1 : Nat) : Int) - 1) + (-1) = ((n : Int) - 1) := by omega
      have hr : List.take (n + 1) cs = List.take n cs ++ [cs[n]'hi] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hi]; rfl
      rw [strSliceChars, hg, hstep, strSliceChars_rev n cs (by omega), hr,
        List.reverse_append]
      rfl

private theorem strSliceChars_from0 (n : Nat) (cs : List Char) (h : n ≤ cs.length) :
    strSliceChars cs n 0 1 = cs.take n := by
  have hx := strSliceChars_fwd n 0 cs (by omega)
  simpa using hx

private theorem strSliceChars_tail (i : Nat) (cs : List Char) (h : i ≤ cs.length) :
    strSliceChars cs (cs.length - i) (i : Int) 1 = cs.drop i := by
  rw [strSliceChars_fwd (cs.length - i) i cs (by omega)]
  rw [show cs.length - i = (cs.drop i).length from by simp]
  exact List.take_length

/-! ## §3 The bounds, at the three shipped spellings

`sliceAdj` and `sliceCount` are CPython's own `PySlice_AdjustIndices` and
slice-length formula, restated in the model. At a `Nat` index inside the string
they collapse; the collapses are separated out so §4's three theorems are each a
`rw` chain rather than an arithmetic argument. -/

private theorem sliceAdj_nat (i len : Nat) (h : i ≤ len) :
    sliceAdj (i : Int) (len : Int) true = (i : Int) := by
  unfold sliceAdj
  rw [if_neg (show ¬ ((i : Int) < 0) from by omega)]
  simp only [ite_true]
  omega

private theorem sliceCount_pre (i : Nat) : sliceCount 0 (i : Int) 1 = i := by
  unfold sliceCount
  rw [if_pos (by decide : (0 : Int) < 1)]
  by_cases hz : (0 : Int) < (i : Int)
  · rw [if_pos hz, Int.ediv_one]; omega
  · rw [if_neg hz]; omega

private theorem sliceCount_suf (i len : Nat) (h : i ≤ len) :
    sliceCount (i : Int) (len : Int) 1 = len - i := by
  unfold sliceCount
  rw [if_pos (by decide : (0 : Int) < 1)]
  by_cases hz : (i : Int) < (len : Int)
  · rw [if_pos hz, Int.ediv_one]; omega
  · rw [if_neg hz]; omega

private theorem sliceCount_rev (len : Nat) :
    sliceCount ((len : Int) - 1) (-1) (-1) = len := by
  unfold sliceCount
  rw [if_neg (by decide : ¬ (0 : Int) < -1)]
  by_cases hz : (-1 : Int) < (len : Int) - 1
  · rw [if_pos hz]
    have hneg : (-(-1 : Int)) = 1 := by decide
    have hnum : (((len : Int) - 1) - (-1) - 1) = ((len : Int) - 1) := by omega
    rw [hnum, hneg, Int.ediv_one]; omega
  · rw [if_neg hz]; omega

/-! ## §4 THE THREE SLICES, at their shipped spellings

Each is `strSlice`'s own body with the three components the source supplies, and
each answers a `List` operation. `.none` for an omitted bound is not this file's
choice: ingestion normalizes an absent slice bound to the `None` constant, which
is CPython's own compilation, and `asSliceIdx` reads it. -/

theorem strSlice_prefix (b : String) (i : Nat) (h : i ≤ b.toList.length) :
    strSlice b .none (.int (i : Int)) .none
      = .ok (.str (String.ofList (b.toList.take i))) := by
  have hlen : (b.length : Int) = (b.toList.length : Int) := by
    rw [String.length_toList]
  simp only [strSlice, asSliceIdx, asInt, Option.map_some, Option.getD_none,
    beq_iff_eq, hlen]
  rw [if_neg (by decide : ¬ ((1 : Int) = 0))]
  show Res.ok (RVal.str (String.ofList (strSliceChars b.toList
      (sliceCount 0 (sliceAdj (i : Int) (b.toList.length : Int) true) 1) 0 1)))
    = Res.ok (RVal.str (String.ofList (b.toList.take i)))
  rw [sliceAdj_nat i b.toList.length h, sliceCount_pre i,
    strSliceChars_from0 i b.toList (by omega)]

theorem strSlice_suffix (b : String) (i : Nat) (h : i ≤ b.toList.length) :
    strSlice b (.int (i : Int)) .none .none
      = .ok (.str (String.ofList (b.toList.drop i))) := by
  have hlen : (b.length : Int) = (b.toList.length : Int) := by
    rw [String.length_toList]
  simp only [strSlice, asSliceIdx, asInt, Option.map_some, Option.getD_none,
    beq_iff_eq, hlen]
  rw [if_neg (by decide : ¬ ((1 : Int) = 0))]
  show Res.ok (RVal.str (String.ofList (strSliceChars b.toList
      (sliceCount (sliceAdj (i : Int) (b.toList.length : Int) true) (b.toList.length : Int) 1)
      (sliceAdj (i : Int) (b.toList.length : Int) true) 1)))
    = Res.ok (RVal.str (String.ofList (b.toList.drop i)))
  rw [sliceAdj_nat i b.toList.length h, sliceCount_suf i b.toList.length h,
    strSliceChars_tail i b.toList h]

theorem strSlice_reverse (b : String) :
    strSlice b .none .none (.int (-1))
      = .ok (.str (String.ofList b.toList.reverse)) := by
  have hlen : (b.length : Int) = (b.toList.length : Int) := by
    rw [String.length_toList]
  simp only [strSlice, asSliceIdx, asInt, Option.map_some,
    Option.getD_some, beq_iff_eq, hlen]
  rw [if_neg (by decide : ¬ ((-1 : Int) = 0))]
  show Res.ok (RVal.str (String.ofList (strSliceChars b.toList
      (sliceCount ((b.toList.length : Int) - 1) (-1) (-1)) ((b.toList.length : Int) - 1) (-1))))
    = Res.ok (RVal.str (String.ofList b.toList.reverse))
  rw [sliceCount_rev b.toList.length, strSliceChars_rev b.toList.length b.toList (by omega),
    List.take_length]

/-! ## §5 `put` IS `List.set`

The named risk, discharged. `put` is `board[:i] + p + board[i + 1:]`; its two
slices are §4's and its two appends are `String.toList_append`. What is left is
core's own `set_eq_take_append_cons_drop`. -/

/-- The shipped `put`, spelled in the two payloads §4 says the slices answer. -/
def putStr (b : String) (k : Nat) (c : Char) : String :=
  String.ofList (b.toList.take k) ++ String.singleton c
    ++ String.ofList (b.toList.drop (k + 1))

/-- …and it IS the `List.set` F1a's `moveCells` is written in. -/
theorem putStr_toList (b : String) (k : Nat) (c : Char) (h : k < b.toList.length) :
    (putStr b k c).toList = b.toList.set k c := by
  rw [List.set_eq_take_append_cons_drop, if_pos h]
  simp [putStr, String.toList_append, String.toList_ofList]

theorem putStr_length (b : String) (k : Nat) (c : Char) (h : k < b.toList.length) :
    (putStr b k c).toList.length = b.toList.length := by
  rw [putStr_toList b k c h, List.length_set]

/-- **The two slices `putStr` is built from are the ones the interpreter runs**,
stated so a later gate can discharge both halves from one place. The inserted
character does not appear: `put`'s two slices are taken from the board BEFORE it,
which is why the same pair serves both of `Position.move`'s calls. -/
theorem putStr_slices (b : String) (k : Nat) (h : k < b.toList.length) :
    strSlice b .none (.int (k : Int)) .none
        = .ok (.str (String.ofList (b.toList.take k)))
      ∧ strSlice b (.int ((k : Int) + 1)) .none .none
        = .ok (.str (String.ofList (b.toList.drop (k + 1)))) := by
  refine ⟨strSlice_prefix b k (by omega), ?_⟩
  have hc : ((k : Int) + 1) = ((k + 1 : Nat) : Int) := by omega
  rw [hc]
  exact strSlice_suffix b (k + 1) (by omega)

/-! ## §6 `rotate` IS reverse-then-map

`self.board[::-1].swapcase()` is §4's negative-step slice followed by
`strSwapcase`, whose own body is `String.ofList (s.toList.map swapChar)` behind
an ASCII guard. The guard survives the reversal, which is the only thing that
needed proving. -/

theorem strAscii_ofList_reverse (b : String) (h : strAscii b = true) :
    strAscii (String.ofList b.toList.reverse) = true := by
  unfold strAscii at h ⊢
  rw [String.toList_ofList]
  simp only [List.all_eq_true] at h ⊢
  intro x hx
  exact h x (List.mem_reverse.mp hx)

/-- The rotated board, spelled in the workers' own payloads. -/
def rotStr (b : String) : String := String.ofList (b.toList.reverse.map swapChar)

/-- **The two calls the shipped `rotate` makes, and what they answer.** -/
theorem rotStr_residue (b : String) (h : strAscii b = true) :
    strSlice b .none .none (.int (-1))
        = .ok (.str (String.ofList b.toList.reverse))
      ∧ strSwapcase (String.ofList b.toList.reverse) = .ok (.str (rotStr b)) := by
  refine ⟨strSlice_reverse b, ?_⟩
  unfold strSwapcase
  rw [if_pos (strAscii_ofList_reverse b h), String.toList_ofList]
  rfl

/-! ## §7 THE BRIDGE — the pipeline IS `moveCells`

Two `put`s and a rotate, each spelled in the interpreter's own workers, and the
board they produce is F1a's `plainMoveBoard` character for character. This is the
statement `pstTotal_plainMove` and `pieceCount_plainMove` have been waiting for,
and the reason F1a could stop where it did. -/

/-- The board `Position.move` builds for a PLAIN move, at the workers. -/
def moveStr (b : String) (i j : Nat) : String :=
  rotStr (putStr (putStr b j (b.toList.getD i '.')) i '.')

theorem moveStr_eq_plainMoveBoard (b : String) (i j : Nat)
    (hi : i < b.toList.length) (hj : j < b.toList.length) :
    moveStr b i j = plainMoveBoard b i j := by
  have hj1 : j < b.toList.length := hj
  have hlen1 : (putStr b j (b.toList.getD i '.')).toList.length = b.toList.length :=
    putStr_length b j _ hj1
  have hi1 : i < (putStr b j (b.toList.getD i '.')).toList.length := by omega
  refine String.toList_injective ?_
  rw [moveStr, rotStr, plainMoveBoard, String.toList_ofList, String.toList_ofList,
    moveCells, putStr_toList _ i '.' hi1, putStr_toList b j _ hj1]

/-! ## §8 THE EXCLUSION, stated exactly

§L37's en-passant finding demanded that F1b's bridge exclude the conditional
`put`s, and reading the two `if`s against the census sharpens it. All THREE extra
`put`s live inside statement 10 (`if p == "K"`) or statement 11 (`if p == "P"`),
so the board-level condition is a statement about `p`, `j`, `i` and `self.ep`
alone — and it is finer than *"not a pawn move"*, which would have thrown away
the fixture's own two edges.

The shipped constants are `A1, H1, A8, H8 = 91, 98, 21, 28` and
`N, E, S, W = -10, 1, 10, -1`. Under statement 11 the double-push arm writes only
`ep` and never the board, so it is NOT excluded — which is why the predicate has
three conjuncts and not four. -/

/-- **`PlainBoard`** — the exact condition under which `Position.move`'s BOARD is
`moveStr`: the castling rook slide does not fire, the promotion replacement does
not fire, and the en-passant removal does not fire.

Read it as the two guards the shipped code writes: *if the mover is a king then
this is not a castle*, and *if the mover is a pawn then the target is outside the
promotion rank and is not the en-passant square*. It is spelled disjunctively
because that is the shape `plainBoardB` decides, and a `Prop` that has to be
massaged into its own mirror is a mirror that can drift. -/
def PlainBoard (p : Char) (i j ep : Int) : Prop :=
  (p ≠ 'K' ∨ (j - i ≠ 2 ∧ i - j ≠ 2)) ∧
  (p ≠ 'P' ∨ ((j < 21 ∨ 28 < j) ∧ j ≠ ep))

/-- Its `Bool` mirror, so the fixture can answer it — and the two-line proof that
the mirror is the predicate, on `reportB_iff`'s template. -/
def plainBoardB (p : Char) (i j ep : Int) : Bool :=
  (!(p == 'K') || (decide (j - i ≠ 2) && decide (i - j ≠ 2))) &&
  (!(p == 'P') || (!(decide (21 ≤ j) && decide (j ≤ 28)) && decide (j ≠ ep)))

theorem plainBoardB_iff (p : Char) (i j ep : Int) :
    plainBoardB p i j ep = true ↔ PlainBoard p i j ep := by
  simp [plainBoardB, PlainBoard]

/-! **The fixture's own two edges are PLAIN, and the three excluded shapes are
not.** `1. d4` is `(84, 64)` and `1. e4` is `(85, 65)`, both pawns, neither
promoting (64 and 65 are well below `H8 = 28`) and neither capturing en passant
(`ep = 0`). The refutations underneath are the three arms the predicate exists to
exclude, each at the square the shipped code tests. -/
#guard plainBoardB 'P' 84 64 0
#guard plainBoardB 'P' 85 65 0
#guard !plainBoardB 'K' 95 97 0
#guard !plainBoardB 'K' 95 93 0
#guard !plainBoardB 'P' 34 24 0
#guard !plainBoardB 'P' 56 45 45

/-! And the double push is NOT excluded, because it writes `ep` and never the
board: `1. d4` itself is one (`84 → 64` is `2 * N`), and it is the first guard
above. -/
#guard plainBoardB 'P' 84 64 0 && decide ((64 : Int) - 84 = 2 * (-10))

/-! ## §9 THE VALUE SIDE — `pstCell`'s delta IS `Position.value`'s first line

`Position.move`'s statement 5 is `score = self.score + self.value(move)`, and
`Position.value`'s own first line (its statement 2, gated as `value_scores` in
`value_bound.lean`, §L28) is

    score = pst[p][j] - pst[p][i]

`value_scores` states its answer as `zj - zi` in the ROW's own entries, with no
120-wide constant written down — *"an AGREEMENT, at this statement"*. F1a's
`pstCell` reads the same two entries through `pstAt`. This section is the one
line that says they are the same number, which is the second of the three things
§L41 left F1b owing.

**The `isUpper` branch is the whole content.** `pstCell` is a three-way match and
only its first arm reads `pst[p][sq]` unmirrored; the mover on a sunfish board is
always uppercase (the board is kept from the side to move), so that is the arm
`Position.value` computes in — and stating the hypothesis is how the other two
arms are excluded rather than assumed away. -/

/-- `pstAt` at a row the caller has already located — the shape `value_scores`
hands over. -/
theorem pstAt_of_row (c : String) (pa : Addr) (es : Array (RVal × RVal)) (sv : Nat)
    (xs : Array RVal) (k : Nat) (z : Int)
    (hg : Env.lookup (initWorld sunfish).globals "pst" = some (.ref pa))
    (hd : Heap.get? (initWorld sunfish).heap pa = some (.dict es sv))
    (hrow : dictFind es.toList (.str c) = some (.tuple xs))
    (hx : xs[k]?.getD .none = .int z) :
    pstAt c k = z := by
  unfold pstAt pstRowOf
  simp only [hg, hd, hrow, hx]

/-- **THE IDENTIFICATION.** At an uppercase mover, `pstCell`'s delta across the
two squares is exactly the `zj - zi` `value_scores` answers with. -/
theorem pstCell_sub_eq (c : Char) (hup : c.isUpper = true) (i j : Nat)
    (pa : Addr) (es : Array (RVal × RVal)) (sv : Nat) (xs : Array RVal) (zi zj : Int)
    (hg : Env.lookup (initWorld sunfish).globals "pst" = some (.ref pa))
    (hd : Heap.get? (initWorld sunfish).heap pa = some (.dict es sv))
    (hrow : dictFind es.toList (.str (String.singleton c)) = some (.tuple xs))
    (hxi : xs[i]?.getD .none = .int zi)
    (hxj : xs[j]?.getD .none = .int zj) :
    pstCell c j - pstCell c i = zj - zi := by
  have hj : pstCell c j = zj := by
    rw [show pstCell c j = pstAt (String.singleton c) j from by simp [pstCell, hup]]
    exact pstAt_of_row _ pa es sv xs j zj hg hd hrow hxj
  have hi : pstCell c i = zi := by
    rw [show pstCell c i = pstAt (String.singleton c) i from by simp [pstCell, hup]]
    exact pstAt_of_row _ pa es sv xs i zi hg hd hrow hxi
  rw [hi, hj]

/-! **INSTANTIATED against the shipped `Position.value`.** The identification is
worth nothing if the two numbers ever part, so the fixture's own two edges are
run through the ENGINE and compared to `pstCell`'s delta — not to a constant.
`1. d4` and `1. e4`, `46` and `42`, on the live interpreter. -/
private def valueRuns (i j : Int) (p : Char) : Bool :=
  match callIn sunfish 8192 (initWorld sunfish) "Position.value" #[posH 0, mvOf i j ""] with
  | .ok _ (.int v) => v == pstCell p j.toNat - pstCell p i.toNat
  | _ => false

#guard valueRuns 84 64 'P'
#guard valueRuns 85 65 'P'

/-! And the identification is not vacuous in the other direction either: the
LOWERCASE arm of `pstCell` is a different number at the same square, which is
what `hup` is there to exclude. -/
#guard pstCell 'P' 64 != pstCell 'p' 64

/-! ### The axioms -/

#print axioms strSliceChars_fwd
#print axioms strSliceChars_rev
#print axioms strSlice_prefix
#print axioms strSlice_suffix
#print axioms strSlice_reverse
#print axioms putStr_toList
#print axioms putStr_length
#print axioms putStr_slices
#print axioms strAscii_ofList_reverse
#print axioms rotStr_residue
#print axioms moveStr_eq_plainMoveBoard
#print axioms plainBoardB_iff
#print axioms pstAt_of_row
#print axioms pstCell_sub_eq

end Examples.python.sunfish.move_residue
