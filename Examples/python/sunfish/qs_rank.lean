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

**§5 ADDS THE INDUCTION ITSELF** (2026-08-25). The strengthened statement was
written to make an induction possible and then nobody wrote the induction, so
`RefinesAtQ` sat with ZERO consumers for three days while the chain document
recorded rung 8 as BLOCKED. §5 discharges it — once, here — so that
`BoundRefinesW V 0` reduces to exactly ONE named obligation and no proof shape.
That is `flagship.lean`'s move (rung 1) applied to the base case, and it has the
same finding attached: the rung that blocked the most was the one nobody had
made anybody's explicit task.
-/
import Examples.python.sunfish.qs_measure

namespace Examples.python.sunfish.qs_rank

open LeanModels LeanModels.Python
open Examples.python.sunfish.pins
open Examples.python.sunfish.genmoves_theorem (posOf)
open Examples.python.sunfish.faillow_census (pieceCount pstTotal d4B e4B)
open Examples.python.sunfish.basecase_depth0
  (RefinesAt BoundWF BoundRefinesW IsPosition
   refinesAt_king_capture refinesAt_probe_hit probe_answer_spelled)
open Examples.python.sunfish.bound_depth (mateLower mateUpper tpKey entryDefault entryOf)
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

/-! ## §5 THE INDUCTION, DISCHARGED — and rung 8 reduces to ONE arm

**What was blocking rung 8, stated exactly.** `boundRefinesW_zero`
(`basecase_depth0.lean` §8) splits the depth-0 base case four ways and proves
three: the king capture, and the probe hit's two returns. `hfall_cut` then
discharged the fourth arm's CUT half. What was left is the fail-low arm, and the
file's own tail says why it is not a leaf: *"a QS node's children store under the
QS node's OWN key"* — `qs_child_depth_eq` — so the fail-low arm's report consumes
a report from a depth-0 CHILD, which is `BoundRefinesW V 0` itself. **Circular
under an induction on depth**, and the guards measure the circle: `bd_probe
(posH 0) 40 0 = some (4, 34)`. One depth-0 call, thirty-four keys.

**The exit was named three days before it was written, and never written.** F2
built `RefinesAtQ` precisely so the second induction — on the QS rank, not on
depth — would be available, and then `RefinesAtQ` sat with **no consumers at
all**. The chain document recorded rung 8 as `BLOCKED (their ledger)` for
something that needed nobody else.

**So this is the base case's `flagship.lean`.** The induction is discharged once,
here; `BoundRefinesW V 0` becomes a theorem with one genuine hypothesis and no
proof shape, and when that hypothesis lands the base case closes by application.

**Why the budget is a `Nat` and not the pair**: §1's window. Why the induction is
STRONG and not predecessor-step: a QS child's rank falls by the move's own value
(`46` and `42` at the fixture, §4) or by a whole `qsSpan` at a capture, never by
one. -/

/-- **`BoundRefinesW V 0` UNDER A RANK BUDGET.** Character-identical to
`BoundRefinesW V 0` except that its conclusion is `RefinesAtQ` — the same claim,
restricted to positions whose board ranks at or below `k`. -/
def BoundRefinesWQ (V : RVal → Int → Int) (k : Nat) : Prop :=
  ∀ (w : World) (ci : ClassId) (sa ts tm hs : Addr) (n dl sf gamma : Int) (pos : RVal)
    (es : Array (RVal × RVal)) (sv : Nat),
    BoundWF V w ci sa ts tm hs n dl sf es sv →
    IsPosition pos →
    -mateUpper < gamma → gamma ≤ mateUpper →
    RefinesAtQ V k 0 w sa ts gamma pos

/-- **THE BUDGETS EXHAUST THE CLAIM**, which is §3's closure lifted from one
position to the rule. Nothing is restricted away by working at a budget: the
budget can always be taken to BE the rank. -/
theorem boundRefinesW_zero_of_forallQ {V : RVal → Int → Int}
    (h : ∀ k : Nat, BoundRefinesWQ V k) : BoundRefinesW V 0 := by
  intro w ci sa ts tm hs n dl sf gamma pos es sv hwf hpos hlo hup
  exact refinesAt_of_forallQ
    (fun k => h k w ci sa ts tm hs n dl sf gamma pos es sv hwf hpos hlo hup)

/-- **THE QS RECURSION STEP** — the base case's analogue of `RecursionStepW`, and
strong for the same kind of reason: a depth-0 node's children are at depth 0
again, so the recursion is on the RANK and the rank falls by a move's value
rather than by one. -/
def QSRecursionStep (V : RVal → Int → Int) : Prop :=
  ∀ k : Nat, (∀ j : Nat, j < k → BoundRefinesWQ V j) → BoundRefinesWQ V k

/-- **AND IT ASSEMBLES.** The base case follows from the step and nothing else.
The induction is routed through an auxiliary `∀ n, ∀ k ≤ n` exactly as
`flagship.lean` routes its own through `d.toNat`, so that no part of the
difficulty lives in the recursion. -/
theorem boundRefinesW_zero_of_qsStep {V : RVal → Int → Int}
    (hstep : QSRecursionStep V) : BoundRefinesW V 0 := by
  have key : ∀ n : Nat, ∀ k : Nat, k ≤ n → BoundRefinesWQ V k := by
    intro n
    induction n with
    | zero => intro k hk; exact hstep k (fun j hj => absurd hj (by omega))
    | succ n ih => intro k hk; exact hstep k (fun j hj => ih j (by omega))
  exact boundRefinesW_zero_of_forallQ (fun k => key k k (Nat.le_refl k))

/-- **THE INDUCTION HYPOTHESIS IS APPLICABLE AT EVERY QS CHILD** — the theorem
the circularity finding asks for, and the reason the second induction is the
right one. `descendsB` is F1's own QS-child test (the move's value at or above
the `40` floor, and either a capture or a quiet move whose `pst` swing IS that
value), and it is enough: a child that passes it ranks strictly below its parent,
so the parent's budget `k` strictly exceeds the child's rank and the hypothesis
at `qsRank b'` is in hand.

**No interpreter step appears here**, which is the point of doing it at this
altitude: the fail-low arm's remaining work is to show the fold's rounds ARE such
children, not to show that such children are usable. -/
theorem refinesAt_child_of_qsStep {V : RVal → Int → Int} {k : Nat}
    (ih : ∀ j : Nat, j < k → BoundRefinesWQ V j)
    {b b' : String} {v : Int}
    (hb : PstInWindow b) (hb' : PstInWindow b') (hdesc : descendsB b b' v = true)
    (hk : qsRank b ≤ k)
    (w : World) (ci : ClassId) (sa ts tm hs : Addr) (n dl sf gamma : Int)
    (sc' : Int) (wc0 wc1 bc0 bc1 : Bool) (ep kp : Int)
    (es : Array (RVal × RVal)) (sv : Nat)
    (hwf : BoundWF V w ci sa ts tm hs n dl sf es sv)
    (hlo : -mateUpper < gamma) (hup : gamma ≤ mateUpper) :
    RefinesAt V 0 w sa ts gamma (posOf b' sc' wc0 wc1 bc0 bc1 ep kp) := by
  have hfall : qsRank b' < qsRank b :=
    qsRank_lt_of_qsLt b b' hb hb' (qsMeasure_lt_of_descendsB hdesc)
  exact ih (qsRank b') (by omega) w ci sa ts tm hs n dl sf gamma _ es sv hwf
    ⟨b', sc', wc0, wc1, bc0, bc1, ep, kp, rfl⟩ hlo hup
    (Nat.le_of_eq (congrArg qsRank (boardOf_posOf b' sc' wc0 wc1 bc0 bc1 ep kp)))

/-- **THE STEP REDUCES TO THE FAIL-LOW ARM ALONE**, and this theorem is where
that is checked by machine rather than asserted in prose. The four-way split is
`boundRefinesW_zero`'s, re-run at a budget; **three of the four arms take the
induction hypothesis nowhere**, because none of them runs `moves()`:

* the king capture returns before the probe,
* the probe's lower return and its upper return both return before the fold.

Only the fall-through — `lo < gamma ≤ up`, where `moves()` finally runs — is
handed `k` and `ih`. So `hfallQ` is the whole of what rung 8 still owes, and its
shape is `hfall`'s with two additions: the parent's budget, and the hypothesis at
every strictly smaller one.

**The split itself is duplicated from `boundRefinesW_zero` and that is a debt,
not a design.** Both are the same arithmetic on `(pos.score, lo, up, gamma)`;
factoring them apart means editing `basecase_depth0.lean`, which `flagship.lean`
consumes, so it is deliberately not done in the landing that introduces the
second consumer. Recorded on this lane's ledger. -/
theorem qsStep_of_hfallQ {V : RVal → Int → Int}
    (hV : ∀ p q d, keyEq p q = true → V p d = V q d)
    (hmateV : ∀ (b : String) (sc : Int) (wc0 wc1 bc0 bc1 : Bool) (ep kp : Int),
      sc ≤ -mateLower → V (posOf b sc wc0 wc1 bc0 bc1 ep kp) 0 ≤ -mateUpper)
    (hfallQ : ∀ (k : Nat), (∀ j : Nat, j < k → BoundRefinesWQ V j) →
      ∀ (w : World) (ci : ClassId) (sa ts tm hs : Addr) (n dl sf gamma : Int)
        (b : String) (sc : Int) (wc0 wc1 bc0 bc1 : Bool) (ep kp : Int)
        (es : Array (RVal × RVal)) (sv : Nat) (lo up : Int),
      BoundWF V w ci sa ts tm hs n dl sf es sv →
      qsRank b ≤ k →
      -mateUpper < gamma → gamma ≤ mateUpper → -mateLower < sc →
      (dictFind es.toList (tpKey (posOf b sc wc0 wc1 bc0 bc1 ep kp) 0)).getD entryDefault
        = entryOf lo up →
      lo < gamma → gamma ≤ up →
      RefinesAt V 0 w sa ts gamma (posOf b sc wc0 wc1 bc0 bc1 ep kp)) :
    QSRecursionStep V := by
  intro k ih w ci sa ts tm hs n dl sf gamma pos es sv hwf hpos hlo hup hrank
  obtain ⟨b, sc, wc0, wc1, bc0, bc1, ep, kp, rfl⟩ := hpos
  -- `boardOf (posOf b …)` is `b` by `rfl` (`boardOf_posOf`), but the budget is
  -- carried to `hfallQ` explicitly rather than left to the unifier: §L44's rule.
  have hrankb : qsRank b ≤ k := hrank
  by_cases hmate : sc ≤ -mateLower
  · exact refinesAt_king_capture w ci sa ts tm hs n dl sf gamma sc b wc0 wc1 bc0 bc1 ep kp
      hwf.self hwf.table hwf.clock hwf.ml hwf.mu hmate hlo
      (hmateV b sc wc0 wc1 bc0 bc1 ep kp hmate)
  · obtain ⟨lo, up, hfind⟩ :=
      probe_answer_spelled (p := posOf b sc wc0 wc1 bc0 bc1 ep kp) (d := 0) hwf.spelled
    by_cases hA : gamma ≤ lo
    · exact refinesAt_probe_hit hV w ci sa ts tm hs n dl sf gamma sc lo up
        b wc0 wc1 bc0 bc1 ep kp es sv hwf.self hwf.score hwf.table hwf.clock hwf.ml hwf.mu
        (by omega) hlo hup hfind (Or.inl hA)
    · by_cases hB : up < gamma
      · exact refinesAt_probe_hit hV w ci sa ts tm hs n dl sf gamma sc lo up
          b wc0 wc1 bc0 bc1 ep kp es sv hwf.self hwf.score hwf.table hwf.clock hwf.ml hwf.mu
          (by omega) hlo hup hfind (Or.inr hB)
      · exact hfallQ k ih w ci sa ts tm hs n dl sf gamma b sc wc0 wc1 bc0 bc1 ep kp es sv
          lo up hwf hrankb hlo hup (by omega) hfind (by omega) (by omega)

/-! ### The budget really does fall at the fixture's own children

§4 measured the ranks; these say the same thing in the shape the step consumes —
`descendsB`'s premises hold, and the child's rank is a strictly smaller BUDGET,
so `ih` applies. The `39` line is the refusal direction: below the QS floor the
same board pair is not a QS child at all. -/
#guard descendsB board0 d4B 46 && decide (qsRank d4B < qsRank board0)
#guard descendsB board0 e4B 42 && decide (qsRank e4B < qsRank board0)
#guard !descendsB board0 d4B 39

/-! ### The axioms -/

#print axioms pstInWindowB_iff
#print axioms qsRank_lo_lt
#print axioms qsRank_lt_of_qsLt
#print axioms boardOf_posOf
#print axioms refinesAt_of_forallQ
#print axioms forallQ_of_refinesAt
#print axioms refinesAt_iff_forallQ
#print axioms boundRefinesW_zero_of_forallQ
#print axioms boundRefinesW_zero_of_qsStep
#print axioms refinesAt_child_of_qsStep
#print axioms qsStep_of_hfallQ

end Examples.python.sunfish.qs_rank
