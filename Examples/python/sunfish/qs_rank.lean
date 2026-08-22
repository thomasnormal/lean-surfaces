/-
**F2 — `RefinesAtQ`, the strengthened statement.** docs/backlog.md §L30 priced
this as *"one sitting, ~30 lines, the cheapest thing left"*, and named its shape
exactly: *"`RefinesAtQ V (k : Nat) …` is `RefinesAt` plus the hypothesis
`qsRank pos ≤ k` (`qsRank` the `Nat` collapse of F1's pair), so the induction is
ordinary strong induction on `k`. `RefinesAt` is its `∃ k` closure, and the
closure is TOTAL because the measure is a total function of the board."*

**The collapse needs a window, and the window is a stated side condition.** F1's
measure is a PAIR, `(pieceCount b, -pstTotal b)` — `Nat × Int` under a
lexicographic order, which is not well-founded on its own because `Int` has no
floor. A `Nat` rank therefore needs `pstTotal` bounded, and rather than prove a
bound on the shipped `pst` table (which would pin this file to the table and
undo the blindness `cellSum` was written for), the bound is a PREDICATE the
caller discharges. `PstInWindow` is that predicate; the fixture satisfies it with
five orders of magnitude to spare, and the `#guard`s at the bottom say so.

**What this file does NOT do.** It does not prove `RecursionStepW`, and it does
not prove any `RefinesAtQ` — it *states* the strengthened proposition, proves the
two facts that make the strengthening sound (the rank descends where the measure
descends, and the `∃ k` closure is total), and instantiates both. §L30's own
words for F2 are "the strengthened statement", not "the strengthened proof".
-/
import Examples.python.sunfish.qs_measure

namespace Examples.python.sunfish.qs_rank

open LeanModels LeanModels.Python
open Examples.python.sunfish.pins
open Examples.python.sunfish.genmoves_theorem (posOf)
open Examples.python.sunfish.faillow_census (pieceCount pstTotal d4B e4B)
open Examples.python.sunfish.basecase_depth0 (RefinesAt)
open Examples.python.sunfish.qs_measure

set_option maxRecDepth 100000

/-! ## §1 THE WINDOW, and why it is a premise

A sunfish board is 120 characters and every cell contributes at most one piece's
`pst` entry, so `|pstTotal|` is bounded by `120 ×` the table's largest entry —
the king's, about `60050`. `qsHi` is that product rounded up. It is a bound this
file ASSUMES of the boards it ranks, not one it proves of the table: §L37 made
`cellSum` blind to `pst` on purpose, and a bound proved here would put the table
back into the calculus. -/

/-- The half-width of the `pstTotal` window. `120 × 60050 = 7 206 000`; this is
that, rounded up. -/
def qsHi : Int := 8000000

/-- One more than the window's full width, so a tie-break can never carry into
the piece-count digit. -/
def qsSpan : Nat := 16000001

/-- **The side condition.** A board whose `pstTotal` sits inside the window. -/
def PstInWindow (b : String) : Prop := -qsHi ≤ pstTotal b ∧ pstTotal b ≤ qsHi

/-- Its `Bool` mirror, so a fixture can answer it — `plainBoardB_iff`'s template
(§L41). -/
def pstInWindowB (b : String) : Bool := decide (-qsHi ≤ pstTotal b ∧ pstTotal b ≤ qsHi)

theorem pstInWindowB_iff (b : String) : pstInWindowB b = true ↔ PstInWindow b := by
  simp [pstInWindowB, PstInWindow]

/-! ## §2 THE RANK — F1's pair, collapsed

Mixed radix: the piece count is the high digit and the window offset is the low
one. `Int.toNat` clamps, so `qsRank` is TOTAL on every string — which is what
makes §3's closure total, and it is why the window is needed only for the
DESCENT and not for the definition. -/

/-- **`qsRank`** — F1's `(pieceCount, -pstTotal)` as a single `Nat`. -/
def qsRank (b : String) : Nat := pieceCount b * qsSpan + (qsHi - pstTotal b).toNat

/-- Inside the window the low digit really is a digit. -/
theorem qsRank_lo_lt (b : String) (h : PstInWindow b) : (qsHi - pstTotal b).toNat < qsSpan := by
  obtain ⟨h1, h2⟩ := h
  have : qsHi - pstTotal b ≤ 2 * qsHi := by unfold qsHi at *; omega
  unfold qsHi qsSpan at *
  omega

/-- **THE DESCENT.** Where F1's lexicographic measure falls, the `Nat` rank
falls — which is the whole content of the collapse, and the only thing the
strengthened induction needs of it. -/
theorem qsRank_lt_of_qsLt (b b' : String) (hb : PstInWindow b) (hb' : PstInWindow b')
    (h : qsLt (qsMeasure b') (qsMeasure b)) : qsRank b' < qsRank b := by
  have hlo' := qsRank_lo_lt b' hb'
  unfold qsMeasure qsLt at h
  unfold qsRank
  rcases h with hpc | ⟨hpc, hpt⟩
  · -- a piece left the board: the high digit falls and the low one cannot catch up
    have hle : pieceCount b' + 1 ≤ pieceCount b := by omega
    have hmul : (pieceCount b' + 1) * qsSpan ≤ pieceCount b * qsSpan :=
      Nat.mul_le_mul_right _ hle
    have hexp : (pieceCount b' + 1) * qsSpan = pieceCount b' * qsSpan + qsSpan :=
      Nat.succ_mul _ _
    omega
  · -- same pieces, more `pstTotal`: the low digit falls
    obtain ⟨h1, h2⟩ := hb
    obtain ⟨h1', h2'⟩ := hb'
    have hpc' : pieceCount b' = pieceCount b := hpc
    have hgt : pstTotal b < pstTotal b' := by omega
    have hlow : (qsHi - pstTotal b').toNat < (qsHi - pstTotal b).toNat := by omega
    rw [hpc']
    omega

/-! ## §3 `RefinesAtQ`, and the closure

`RefinesAt` already NAMES its world (§L26's trap, recorded), so the strengthening
adds a hypothesis and nothing else — no `∃ w'`, no second existential. -/

/-- The board a `Position` VALUE carries, for ranking. -/
def boardOf (pos : RVal) : String :=
  match pos with
  | .ntuple _ _ xs => (match xs[0]?.getD .none with | .str b => b | _ => "")
  | _ => ""

theorem boardOf_posOf (b : String) (sc : Int) (wc0 wc1 bc0 bc1 : Bool) (ep kp : Int) :
    boardOf (posOf b sc wc0 wc1 bc0 bc1 ep kp) = b := rfl

/-- **`RefinesAtQ`** — `RefinesAt` under a rank budget. The induction on `k` is
ordinary strong induction on a `Nat`; F1's measure is what makes the budget fall
at every QS child. -/
def RefinesAtQ (V : RVal → Int → Int) (k : Nat) (d : Int) (w : World) (sa ts : Addr)
    (gamma : Int) (pos : RVal) : Prop :=
  qsRank (boardOf pos) ≤ k → RefinesAt V d w sa ts gamma pos

/-- **THE CLOSURE IS TOTAL**, and this is the one line that says so: the budget
can always be met by taking `k` to BE the rank, because `qsRank` is a total
function of the board. So `RefinesAt` is exactly `∀ k, RefinesAtQ … k …` and the
strengthening costs the consumer nothing. -/
theorem refinesAt_of_forallQ {V : RVal → Int → Int} {d : Int} {w : World} {sa ts : Addr}
    {gamma : Int} {pos : RVal} (h : ∀ k, RefinesAtQ V k d w sa ts gamma pos) :
    RefinesAt V d w sa ts gamma pos :=
  h (qsRank (boardOf pos)) (Nat.le_refl _)

/-- …and the other direction, which is immediate and worth stating so the two are
visibly the same proposition rather than one being weaker. -/
theorem forallQ_of_refinesAt {V : RVal → Int → Int} {d : Int} {w : World} {sa ts : Addr}
    {gamma : Int} {pos : RVal} (h : RefinesAt V d w sa ts gamma pos) :
    ∀ k, RefinesAtQ V k d w sa ts gamma pos := fun _ _ => h

/-- **`RefinesAt` IS its own `∃ k` closure.** The receipt that the strengthening
restates nothing — §L30's *"the closure is TOTAL"*, as an `iff`. -/
theorem refinesAt_iff_forallQ {V : RVal → Int → Int} {d : Int} {w : World} {sa ts : Addr}
    {gamma : Int} {pos : RVal} :
    RefinesAt V d w sa ts gamma pos ↔ ∀ k, RefinesAtQ V k d w sa ts gamma pos :=
  ⟨forallQ_of_refinesAt, refinesAt_of_forallQ⟩

/-! ## §4 INSTANTIATED — the rank is finite, and the children are strictly below

§L30 asked for exactly two checks: *"`#guard` the rank finite on the fixture, and
that the two children's ranks are strictly below the parent's."* Both, on the
live boards, plus the window premise each one needs. -/

/-! The window premise, on the three boards the fixture uses. `pstTotal board0`
is `127 158` — inside a window of `±8 000 000` by five orders of magnitude. -/
#guard pstInWindowB board0
#guard pstInWindowB d4B
#guard pstInWindowB e4B

/-! The rank is FINITE and it is what the mixed radix says it is. -/
#guard qsRank board0 == 32 * 16000001 + (8000000 - 127158)
#guard qsRank board0 == 519872874

/-! **And both children rank strictly below the parent.** `1. d4` and `1. e4` are
QUIET moves: the piece count is unchanged (32 → 32) and the whole descent is the
low digit, which falls by exactly the move's own value — `46` and `42`, the two
numbers §L37 measured. -/
#guard qsRank d4B < qsRank board0
#guard qsRank e4B < qsRank board0
#guard qsRank board0 - qsRank d4B == 46
#guard qsRank board0 - qsRank e4B == 42

/-! **And the HIGH digit dominates**, which is the refutation §L44 banked, now
visible in the rank. A board with one piece FEWER — here the opening board with
the `b1` knight lifted off — ranks a whole `qsSpan` lower whatever the `pst`
swing does, so a capture can never be outranked by any amount of table movement.
The board is synthetic on purpose: the point is about the RADIX, not about a
legal move. -/
private def noKnightB : String := String.ofList (board0.toList.set 92 '.')
#guard pstInWindowB noKnightB
#guard pieceCount noKnightB + 1 == pieceCount board0
#guard qsRank noKnightB < qsRank board0
#guard qsRank board0 - qsRank noKnightB > 15000000

/-! And the descent theorem's own hypothesis is met on the quiet edge: F1's
`qsMeasure` really is lower for the child, which is what `qsRank_lt_of_qsLt`
consumes. -/
#guard qsLtB (qsMeasure d4B) (qsMeasure board0)
#guard qsLtB (qsMeasure e4B) (qsMeasure board0)
#guard qsLtB (qsMeasure noKnightB) (qsMeasure board0)

/-! ### The axioms -/

#print axioms pstInWindowB_iff
#print axioms qsRank_lo_lt
#print axioms qsRank_lt_of_qsLt
#print axioms boardOf_posOf
#print axioms refinesAt_of_forallQ
#print axioms forallQ_of_refinesAt
#print axioms refinesAt_iff_forallQ

end Examples.python.sunfish.qs_rank
