import LeanModels.Sv.CombFragE
import LeanModels.Sv.Loop2Slot

/-!
# The slots of one ordinary `always_comb` over E-core-0 (WS3) — *derived from E*

`CombFragE` gives a fragment body's single activation (`Stmt2.sem_run`). The slot theorems of
`Loop2Slot` (`SingleE`) need two more facts about its meaning `F = body.sem d`: it is idempotent,
and a slot that wakes nothing finds the store settled (`quiet`). Both hold when the body is
**written before read** on a write set `W`:

* **`combWbr d W body`** (decidable, structural): along every path, every read of a signal of `W`
  comes after a FULL write of it (a blocking assignment to its whole declared width), and at the end
  every signal of `W` is fully written. An `if` without an `else` and a `case` without a `default`
  write nothing on their empty path, so a latch-style body is refused.
* **Locality** (`Stmt2.sem_rel`): two states that agree on every read outside `W` give the same
  values to every signal of `W`, since the body reads `W` only after writing it.
* `idem`: `F st` agrees with `st` outside `W` (`Stmt2.sem_frame`), so `F (F st)` and `F st` agree.
* `quiet`: E-core-0's sensitivity of an `always_comb` drops only the reads overlapping a window the
  body writes (LRM 9.2.2.2.1, `Elab.sens`), so every read outside `W` is in it (`sens_of_readW`); a
  slot that wakes nothing changed none of them, and the signals of `W` are not inputs.

**`singleE_comb`**: a single-`always_comb` design whose body is in the fragment and passes the check
is a `SingleE`, so every slot of every behaviour closes at `F` of its opening (`SingleE.slot`).
Qualified `case` claims stay a hypothesis (`hcl`), as in `sem_run`.
-/

namespace LeanModels.Sv.Loop2

open Kernel

/-! ## The check -/

/-- The reads `rs` touch a signal of `W` only once it is in `D` (fully written). -/
def rdOk (W D : List String) (rs : List ReadWin) : Bool :=
  rs.all fun r => decide (r.name ∈ W → r.name ∈ D)

mutual
/-- The signals fully written after `s`, from `D` before it; `none`: a read of `W` before its write. -/
def _root_.LeanModels.Sv.Stmt2.wbr (d : Design2) (W : List String) :
    Stmt2 → List String → Option (List String)
  | .blockingAssign t e, D =>
      if rdOk W D e.reads then
        match Lhs2.staticWin d t with
        | some (n, lo, w) => some (if lo = 0 ∧ d.declWidth n = some w then n :: D else D)
        | none => some D
      else none
  | .ifStmt c a b, D =>
      if rdOk W D c.reads then
        match a.wbr d W D, Stmt2.optWbr d W b D with
        | some Da, some Db => some (Da.filter fun x => decide (x ∈ Db))
        | _, _ => none
      else none
  | .block ss, D => Stmt2.listWbr d W ss.toList D
  | .caseStmt subj items dflt _ _, D =>
      if rdOk W D subj.reads then
        match Stmt2.optWbr d W dflt D with
        | some Dd => CaseItem2.listWbr d W D Dd items.toList
        | none => none
      else none
  | _, _ => none
termination_by structural s _ => s

def _root_.LeanModels.Sv.Stmt2.optWbr (d : Design2) (W : List String) :
    Option Stmt2 → List String → Option (List String)
  | none, D => some D
  | some s, D => s.wbr d W D
termination_by structural o _ => o

def _root_.LeanModels.Sv.Stmt2.listWbr (d : Design2) (W : List String) :
    List Stmt2 → List String → Option (List String)
  | [], D => some D
  | s :: ss, D => match s.wbr d W D with
    | some D' => Stmt2.listWbr d W ss D'
    | none => none
termination_by structural l _ => l

def _root_.LeanModels.Sv.CaseItem2.wbr (d : Design2) (W D : List String) :
    CaseItem2 → Option (List String)
  | .mk pats body => if rdOk W D (Expr2.listReads pats.toList) then body.wbr d W D else none
termination_by structural it => it

/-- The arms, from `D`; `acc` is what every path seen so far writes (the default's, at the start). -/
def _root_.LeanModels.Sv.CaseItem2.listWbr (d : Design2) (W D : List String) (acc : List String) :
    List CaseItem2 → Option (List String)
  | [] => some acc
  | it :: rest => match it.wbr d W D with
    | some Di => CaseItem2.listWbr d W D (acc.filter fun x => decide (x ∈ Di)) rest
    | none => none
termination_by structural l => l
end

/-- **The check**: written before read, and every signal of `W` written on every path. -/
def combWbr (d : Design2) (W : List String) (body : Stmt2) : Bool :=
  match body.wbr d W [] with
  | some D => W.all fun x => decide (x ∈ D)
  | none => false

theorem combWbr_spec {d : Design2} {W : List String} {body : Stmt2} (h : combWbr d W body = true) :
    ∃ D, body.wbr d W [] = some D ∧ ∀ x ∈ W, x ∈ D := by
  unfold combWbr at h
  split at h
  · next D hD => exact ⟨D, hD, by simpa [List.all_eq_true] using h⟩
  · simp at h

/-! ## The invariant and the frame -/

/-- What every typed view satisfies: the declared names, each at its declared width. -/
def CombInv (d : Design2) (st : SvState) : Prop :=
  st.map Prod.fst = d.decls.toList.map (·.name) ∧ ∀ n w, d.declWidth n = some w → (sig st n).width = w

theorem CombInv.write {d : Design2} {st : SvState} (h : CombInv d st) {n : String} {dw : Nat}
    (hn : d.declWidth n = some dw) (lo : Nat) (q : LVec) :
    CombInv d (SvState.set st n ((sig st n).insertAt lo q)) := by
  have hm : n ∈ st.map Prod.fst := by
    rw [h.1]
    simp only [Design2.declWidth, Option.map_eq_some_iff] at hn
    obtain ⟨dc, hf, -⟩ := hn
    exact List.mem_map.mpr ⟨dc, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf⟩
  refine ⟨(SvState.keys_set _ hm).trans h.1, fun m w hw => ?_⟩
  by_cases hnm : n = m
  · subst hnm; simpa [sig] using h.2 n w hw
  · simp only [sig, SvState.lookup_set_ne _ _ hnm]; exact h.2 m w hw

section
variable (d : Design2) (Q : SvState → Prop) (T : List Win)
  (hQ : ∀ st t n lo w q, Lhs2.staticWin d t = some (n, lo, w) → (n, lo, w) ∈ T → Q st →
    Q (SvState.set st n ((sig st n).insertAt lo q)))
include hQ

mutual
/-- A property every write of `T` keeps holds after the body. -/
theorem Stmt2.sem_inv : ∀ (s : Stmt2) (st : SvState), (∀ X ∈ s.targetWins d, X ∈ T) → Q st →
    Q (s.sem d st)
  | .blockingAssign t e, st, hT, h => by
      simp only [Stmt2.sem]
      split
      · next n lo w hw => exact hQ st t n lo w _ hw (hT _ (by simp [Stmt2.targetWins, hw])) h
      · exact h
  | .ifStmt c a b, st, hT, h => by
      simp only [Stmt2.sem]
      split
      · exact Stmt2.sem_inv a st (fun X hX => hT X (by simp [Stmt2.targetWins, hX])) h
      · exact Stmt2.optSem_inv b st (fun X hX => hT X (by simp [Stmt2.targetWins, hX])) h
  | .block ss, st, hT, h => Stmt2.listSem_inv ss.toList st hT h
  | .caseStmt subj items dflt mode _, st, hT, h => by
      simp only [Stmt2.sem]
      cases hl : CaseItem2.listSem d (ev st subj) mode items.toList st with
      | none => exact Stmt2.optSem_inv dflt st (fun X hX => hT X (by simp [Stmt2.targetWins, hX])) h
      | some st' =>
          exact CaseItem2.listSem_inv (ev st subj) mode items.toList st
            (fun X hX => hT X (by simp [Stmt2.targetWins, hX])) h st' hl
  | .nbaAssign _ _, st, _, h | .unsupported _ _, st, _, h => by simpa [Stmt2.sem] using h
termination_by structural s => s

theorem Stmt2.optSem_inv : ∀ (b : Option Stmt2) (st : SvState), (∀ X ∈ Stmt2.optTargetWins d b, X ∈ T) →
    Q st → Q (Stmt2.optSem d b st)
  | none, _, _, h => h
  | some s, st, hT, h => Stmt2.sem_inv s st hT h
termination_by structural b => b

theorem Stmt2.listSem_inv : ∀ (l : List Stmt2) (st : SvState), (∀ X ∈ Stmt2.listTargetWins d l, X ∈ T) →
    Q st → Q (Stmt2.listSem d l st)
  | [], _, _, h => h
  | s :: ss, st, hT, h => Stmt2.listSem_inv ss _
      (fun X hX => hT X (by simp [Stmt2.listTargetWins, hX]))
      (Stmt2.sem_inv s st (fun X hX => hT X (by simp [Stmt2.listTargetWins, hX])) h)
termination_by structural l => l

theorem CaseItem2.armSem_inv (sv : LVec) (mode : CaseMode) : ∀ (it : CaseItem2) (st : SvState),
    (∀ X ∈ it.targetWins d, X ∈ T) → Q st → ∀ st', it.armSem d sv mode st = some st' → Q st'
  | .mk pats body, st, hT, h, st', hs => by
      simp only [CaseItem2.armSem] at hs
      split at hs
      · cases hs; exact Stmt2.sem_inv body st hT h
      · cases hs
termination_by structural it => it

theorem CaseItem2.listSem_inv (sv : LVec) (mode : CaseMode) : ∀ (items : List CaseItem2) (st : SvState),
    (∀ X ∈ CaseItem2.listTargetWins d items, X ∈ T) → Q st →
      ∀ st', CaseItem2.listSem d sv mode items st = some st' → Q st'
  | [], _, _, _, _, hs => by simp [CaseItem2.listSem] at hs
  | it :: rest, st, hT, h, st', hs => by
      simp only [CaseItem2.listSem] at hs
      cases h₁ : it.armSem d sv mode st with
      | some st₁ =>
          rw [h₁] at hs; obtain rfl := Option.some.inj hs
          exact CaseItem2.armSem_inv sv mode it st
            (fun X hX => hT X (by simp [CaseItem2.listTargetWins, hX])) h st₁ h₁
      | none =>
          rw [h₁] at hs
          exact CaseItem2.listSem_inv sv mode rest st
            (fun X hX => hT X (by simp [CaseItem2.listTargetWins, hX])) h st' hs
termination_by structural l => l
end
end

theorem Stmt2.sem_combInv {d : Design2} (s : Stmt2) {st : SvState} (h : CombInv d st) :
    CombInv d (s.sem d st) :=
  Stmt2.sem_inv d (CombInv d) (s.targetWins d) (fun _ _ _ _ _ _ hw _ h' =>
    let ⟨_, _, _, hdw, _⟩ := Lhs2.staticWin_spec hw; h'.write hdw _ _) s st (fun _ h => h) h

/-- **The frame**: a body whose writes are all in `W` leaves every other signal. -/
theorem Stmt2.sem_frame {d : Design2} {W : List String} {s : Stmt2}
    (hT : ∀ X ∈ s.targetWins d, X.1 ∈ W) {y : String} (hy : y ∉ W) (st : SvState) :
    SvState.lookup (s.sem d st) y = SvState.lookup st y :=
  Stmt2.sem_inv d (fun u => SvState.lookup u y = SvState.lookup st y) (s.targetWins d)
    (fun _ _ n _ _ _ _ hm h => by
      rw [SvState.lookup_set_ne _ _ fun hn => hy (by subst hn; exact hT _ hm)]; exact h) s st (fun _ h => h) rfl

/-! ## Locality -/

theorem agree_of_rdOk {W D : List String} {rs : List ReadWin} {u u' : SvState}
    (hok : rdOk W D rs = true) (hR : ∀ r ∈ rs, r.name ∉ W → r.agree u u')
    (hD : ∀ x ∈ D, SvState.lookup u x = SvState.lookup u' x) : ∀ r ∈ rs, r.agree u u' := by
  simp only [rdOk, List.all_eq_true, decide_eq_true_eq] at hok
  intro r hr
  by_cases hw : r.name ∈ W
  · exact ReadWin.agree_of_lookup (hD _ (hok r hr hw))
  · exact hR r hr hw

theorem agree_congr {r : ReadWin} {a a' b b' : SvState} (ha : SvState.lookup a r.name = SvState.lookup b r.name)
    (ha' : SvState.lookup a' r.name = SvState.lookup b' r.name) (h : r.agree b b') : r.agree a a' := by
  cases r <;> simp only [ReadWin.agree, ReadWin.name] at * <;> rw [ha, ha'] <;> exact h

section
variable (d : Design2) (W : List String)

mutual
/-- **Locality**: states agreeing outside `W` (on what the body reads) and on the fully written
`D` agree, after the body, on everything it fully writes. -/
theorem Stmt2.sem_rel : ∀ (s : Stmt2) (D D' : List String) (u u' : SvState), s.wbr d W D = some D' →
    (∀ X ∈ s.targetWins d, X.1 ∈ W) → CombInv d u → CombInv d u' →
    (∀ r ∈ s.rawReads, r.name ∉ W → r.agree u u') →
    (∀ x ∈ D, SvState.lookup u x = SvState.lookup u' x) →
    ∀ x ∈ D', SvState.lookup (s.sem d u) x = SvState.lookup (s.sem d u') x
  | .blockingAssign t e, D, D', u, u', hw, _, hI, hI', hR, hD => by
      simp only [Stmt2.wbr] at hw
      split at hw
      · next hok =>
        have he : ev u e = ev u' e := by
          unfold ev; rw [evalPure2_congr_reads (agree_of_rdOk hok (by simpa [Stmt2.rawReads] using hR) hD)]
        simp only [Stmt2.sem]
        split at hw
        · next n lo w hsw =>
          simp only [Option.some.injEq] at hw; subst hw
          simp only [hsw]
          intro x hx
          rw [SvState.lookup_set, SvState.lookup_set]
          by_cases hnx : n = x
          · subst hnx
            simp only [if_true, he]
            by_cases hf : lo = 0 ∧ d.declWidth n = some w
            · obtain ⟨rfl, hdw⟩ := hf
              rw [LVec.insertAt_zero_of_width_eq (by rw [width_resizeU, hI.2 _ _ hdw]),
                LVec.insertAt_zero_of_width_eq (by rw [width_resizeU, hI'.2 _ _ hdw])]
            · rw [if_neg hf] at hx
              simp only [sig, hD _ hx]
          · simp only [hnx, if_false]
            refine hD x ?_
            by_cases hf : lo = 0 ∧ d.declWidth n = some w
            · rw [if_pos hf] at hx; exact (List.mem_cons.mp hx).resolve_left (Ne.symm hnx)
            · rwa [if_neg hf] at hx
        · next hsw =>
          simp only [Option.some.injEq] at hw; subst hw
          simp only [hsw]; exact hD
      · simp at hw
  | .ifStmt c a b, D, D', u, u', hw, hT, hI, hI', hR, hD => by
      simp only [Stmt2.wbr] at hw
      split at hw
      · next hok =>
        split at hw
        · next Da Db ha hb =>
          simp only [Option.some.injEq] at hw; subst hw
          simp only [Stmt2.rawReads, List.mem_append] at hR
          have hc : ev u c = ev u' c := by
            unfold ev
            rw [evalPure2_congr_reads (agree_of_rdOk hok (fun r hr => hR r (.inl (.inl hr))) hD)]
          simp only [Stmt2.sem, hc]
          split
          · intro x hx
            exact Stmt2.sem_rel a D Da u u' ha (fun X hX => hT X (by simp [Stmt2.targetWins, hX])) hI hI'
              (fun r hr => hR r (.inl (.inr hr))) hD x (List.mem_filter.mp hx).1
          · intro x hx
            exact Stmt2.optSem_rel b D Db u u' hb (fun X hX => hT X (by simp [Stmt2.targetWins, hX]))
              hI hI' (fun r hr => hR r (.inr hr)) hD x (by simpa using (List.mem_filter.mp hx).2)
        · simp at hw
      · simp at hw
  | .block ss, D, D', u, u', hw, hT, hI, hI', hR, hD =>
      Stmt2.listSem_rel ss.toList D D' u u' hw hT hI hI' hR hD
  | .caseStmt subj items dflt mode _, D, D', u, u', hw, hT, hI, hI', hR, hD => by
      simp only [Stmt2.wbr] at hw
      split at hw
      · next hok =>
        cases hdw : Stmt2.optWbr d W dflt D with
        | none => simp [hdw] at hw
        | some Dd =>
          simp only [hdw] at hw
          simp only [Stmt2.rawReads, List.mem_append] at hR
          have hsv : ev u subj = ev u' subj := by
            unfold ev
            rw [evalPure2_congr_reads (agree_of_rdOk hok (fun r hr => hR r (.inl (.inl hr))) hD)]
          simp only [Stmt2.sem, hsv]
          obtain ⟨hsub, hl⟩ := CaseItem2.listSem_rel (ev u' subj) mode items.toList D Dd D' u u' hw
            (fun X hX => hT X (by simp [Stmt2.targetWins, hX])) hI hI'
            (fun r hr => hR r (.inl (.inr hr))) hD
          rcases hl with ⟨h1, h2⟩ | ⟨a, a', h1, h2, h3⟩
          · rw [h1, h2]
            intro x hx
            exact Stmt2.optSem_rel dflt D Dd u u' hdw (fun X hX => hT X (by simp [Stmt2.targetWins, hX]))
              hI hI' (fun r hr => hR r (.inr hr)) hD x (hsub x hx)
          · rw [h1, h2]; exact h3
      · simp at hw
  | .nbaAssign _ _, _, _, _, _, hw, _, _, _, _, _ | .unsupported _ _, _, _, _, _, hw, _, _, _, _, _ => by
      simp [Stmt2.wbr] at hw
termination_by structural s => s

theorem Stmt2.optSem_rel : ∀ (b : Option Stmt2) (D D' : List String) (u u' : SvState),
    Stmt2.optWbr d W b D = some D' → (∀ X ∈ Stmt2.optTargetWins d b, X.1 ∈ W) → CombInv d u →
    CombInv d u' → (∀ r ∈ Stmt2.optRawReads b, r.name ∉ W → r.agree u u') →
    (∀ x ∈ D, SvState.lookup u x = SvState.lookup u' x) →
    ∀ x ∈ D', SvState.lookup (Stmt2.optSem d b u) x = SvState.lookup (Stmt2.optSem d b u') x
  | none, D, D', _, _, hw, _, _, _, _, hD => by
      simp only [Stmt2.optWbr, Option.some.injEq] at hw; subst hw; exact hD
  | some s, D, D', u, u', hw, hT, hI, hI', hR, hD => Stmt2.sem_rel s D D' u u' hw hT hI hI' hR hD
termination_by structural b => b

theorem Stmt2.listSem_rel : ∀ (l : List Stmt2) (D D' : List String) (u u' : SvState),
    Stmt2.listWbr d W l D = some D' → (∀ X ∈ Stmt2.listTargetWins d l, X.1 ∈ W) → CombInv d u →
    CombInv d u' → (∀ r ∈ Stmt2.listRawReads l, r.name ∉ W → r.agree u u') →
    (∀ x ∈ D, SvState.lookup u x = SvState.lookup u' x) →
    ∀ x ∈ D', SvState.lookup (Stmt2.listSem d l u) x = SvState.lookup (Stmt2.listSem d l u') x
  | [], D, D', _, _, hw, _, _, _, _, hD => by
      simp only [Stmt2.listWbr, Option.some.injEq] at hw; subst hw; exact hD
  | s :: ss, D, D', u, u', hw, hT, hI, hI', hR, hD => by
      simp only [Stmt2.listWbr] at hw
      cases h1 : s.wbr d W D with
      | none => simp [h1] at hw
      | some D1 =>
        simp only [h1] at hw
        simp only [Stmt2.listRawReads, List.mem_append] at hR
        have hTs : ∀ X ∈ s.targetWins d, X.1 ∈ W := fun X hX => hT X (by simp [Stmt2.listTargetWins, hX])
        exact Stmt2.listSem_rel ss D1 D' _ _ hw (fun X hX => hT X (by simp [Stmt2.listTargetWins, hX]))
          (Stmt2.sem_combInv s hI) (Stmt2.sem_combInv s hI')
          (fun r hr hn => agree_congr (Stmt2.sem_frame hTs hn u) (Stmt2.sem_frame hTs hn u')
            (hR r (.inr hr) hn))
          (Stmt2.sem_rel s D D1 u u' h1 hTs hI hI' (fun r hr => hR r (.inl hr)) hD)
termination_by structural l => l

theorem CaseItem2.armSem_rel (sv : LVec) (mode : CaseMode) : ∀ (it : CaseItem2) (D Di : List String)
    (u u' : SvState), it.wbr d W D = some Di → (∀ X ∈ it.targetWins d, X.1 ∈ W) → CombInv d u →
    CombInv d u' → (∀ r ∈ it.rawReads, r.name ∉ W → r.agree u u') →
    (∀ x ∈ D, SvState.lookup u x = SvState.lookup u' x) →
    (it.armSem d sv mode u = none ∧ it.armSem d sv mode u' = none) ∨
      ∃ a a', it.armSem d sv mode u = some a ∧ it.armSem d sv mode u' = some a' ∧
        ∀ x ∈ Di, SvState.lookup a x = SvState.lookup a' x
  | .mk pats body, D, Di, u, u', hw, hT, hI, hI', hR, hD => by
      simp only [CaseItem2.wbr] at hw
      split at hw
      · next hok =>
        simp only [CaseItem2.rawReads, List.mem_append] at hR
        have hp : evs u pats.toList = evs u' pats.toList := by
          unfold evs; rw [evalPures2_congr_reads (agree_of_rdOk hok (fun r hr => hR r (.inl hr)) hD)]
        simp only [CaseItem2.armSem, armHit, hp]
        by_cases hh : ((evs u' pats.toList).any fun pv => caseHit mode sv pv) = true
        · simp only [hh, ↓reduceIte]
          exact .inr ⟨_, _, rfl, rfl,
            Stmt2.sem_rel body D Di u u' hw hT hI hI' (fun r hr => hR r (.inr hr)) hD⟩
        · simp only [hh]; exact .inl ⟨rfl, rfl⟩
      · simp at hw
termination_by structural it => it

theorem CaseItem2.listSem_rel (sv : LVec) (mode : CaseMode) : ∀ (items : List CaseItem2)
    (D acc D' : List String) (u u' : SvState), CaseItem2.listWbr d W D acc items = some D' →
    (∀ X ∈ CaseItem2.listTargetWins d items, X.1 ∈ W) → CombInv d u → CombInv d u' →
    (∀ r ∈ CaseItem2.listRawReads items, r.name ∉ W → r.agree u u') →
    (∀ x ∈ D, SvState.lookup u x = SvState.lookup u' x) →
    (∀ x ∈ D', x ∈ acc) ∧
      ((CaseItem2.listSem d sv mode items u = none ∧ CaseItem2.listSem d sv mode items u' = none) ∨
        ∃ a a', CaseItem2.listSem d sv mode items u = some a ∧
          CaseItem2.listSem d sv mode items u' = some a' ∧
          ∀ x ∈ D', SvState.lookup a x = SvState.lookup a' x)
  | [], D, acc, D', _, _, hw, _, _, _, _, _ => by
      simp only [CaseItem2.listWbr, Option.some.injEq] at hw; subst hw
      exact ⟨fun _ h => h, .inl ⟨rfl, rfl⟩⟩
  | it :: rest, D, acc, D', u, u', hw, hT, hI, hI', hR, hD => by
      simp only [CaseItem2.listWbr] at hw
      cases h1 : it.wbr d W D with
      | none => simp [h1] at hw
      | some Di =>
        simp only [h1] at hw
        simp only [CaseItem2.listRawReads, List.mem_append] at hR
        obtain ⟨hsub, hl⟩ := CaseItem2.listSem_rel sv mode rest D _ D' u u' hw
          (fun X hX => hT X (by simp [CaseItem2.listTargetWins, hX])) hI hI' (fun r hr => hR r (.inr hr)) hD
        have hsub' : ∀ x ∈ D', x ∈ acc ∧ x ∈ Di := fun x hx => by simpa using hsub x hx
        refine ⟨fun x hx => (hsub' x hx).1, ?_⟩
        simp only [CaseItem2.listSem]
        rcases CaseItem2.armSem_rel sv mode it D Di u u' h1
            (fun X hX => hT X (by simp [CaseItem2.listTargetWins, hX])) hI hI'
            (fun r hr => hR r (.inl hr)) hD with ⟨ha, ha'⟩ | ⟨a, a', ha, ha', h3⟩
        · rw [ha, ha']; exact hl
        · rw [ha, ha']; exact .inr ⟨a, a', rfl, rfl, fun x hx => h3 x (hsub' x hx).2⟩
termination_by structural l => l
end
end

/-! ## The slots -/

/-- A read outside `W` is in E's sensitivity, when every window the body writes is in `W`. -/
theorem sens_of_readW {E : Elab} {body : Stmt2} {W : List String} (hp : E.procs[0]? = some (.comb body))
    (ht : ∀ X ∈ body.targetWins E.toDesign2, X.1 ∈ W) {r : ReadWin} (hr : r ∈ body.rawReads)
    (hn : r.name ∉ W) : r ∈ E.sens 0 := by
  simp only [Elab.sens, hp]
  refine List.mem_append_left _ (List.mem_filter.mpr ⟨hr, ?_⟩)
  simp only [Bool.not_eq_true', List.any_eq_false]
  exact fun X hX hov => hn ((ReadWin.name_of_overlaps hov) ▸ ht X hX)

theorem single_elab {d : Design2} {body : Stmt2} (hp : d.processes = #[.alwaysComb body]) :
    (Elab.ofDesign2 d).toDesign2 = d ∧ (Elab.ofDesign2 d).procs = #[.comb body] :=
  ⟨Elab.toDesign2_ofDesign2 fun p hp' => by
    rw [hp] at hp'; simp only [List.mem_singleton] at hp'; subst hp'; rfl, by simp [Elab.ofDesign2, hp, Proc0.ofProcess2]⟩

theorem combInv_view {d : Design2} (hE : (Elab.ofDesign2 d).toDesign2 = d) {σ : Store}
    (hT : (Elab.ofDesign2 d).Typed σ) : CombInv d ((Elab.ofDesign2 d).view σ) :=
  ⟨(Elab.keys_view _ σ).trans rfl, fun n w hw => by
    obtain ⟨old, hold, hwo⟩ := Elab.lookup_declared hT (n := n) (by rw [hE]; exact hw)
    simp [sig, hold, hwo]⟩

/-- Two invariant states agreeing on the reads outside `W`, and `F u` agreeing with `u'` on `W`:
`u'` is settled. -/
theorem Stmt2.sem_settles {d : Design2} {body : Stmt2} {W : List String}
    (hnd : (d.decls.toList.map (·.name)).Nodup) (hT : ∀ X ∈ body.targetWins d, X.1 ∈ W)
    (hwbr : combWbr d W body = true) {u u' : SvState} (hu : CombInv d u) (hu' : CombInv d u')
    (hR : ∀ r ∈ body.rawReads, r.name ∉ W → r.agree u u')
    (hW' : ∀ x ∈ W, SvState.lookup (body.sem d u) x = SvState.lookup u' x) : body.sem d u' = u' := by
  obtain ⟨Dw, hDw, hWD⟩ := combWbr_spec hwbr
  have hF' := Stmt2.sem_combInv body hu'
  refine SvState.ext (hF'.1.trans hu'.1.symm) (by rw [hF'.1]; exact hnd) fun x => ?_
  by_cases hx : x ∈ W
  · rw [← Stmt2.sem_rel d W body [] Dw u u' hDw hT hu hu' hR (fun _ h => absurd h List.not_mem_nil)
      x (hWD x hx)]
    exact hW' x hx
  · exact Stmt2.sem_frame hT hx u'

theorem Stmt2.sem_idem {d : Design2} {body : Stmt2} {W : List String} (hnd : (d.decls.toList.map (·.name)).Nodup)
    (hT : ∀ X ∈ body.targetWins d, X.1 ∈ W) (hwbr : combWbr d W body = true) {st : SvState}
    (hst : CombInv d st) : body.sem d (body.sem d st) = body.sem d st :=
  Stmt2.sem_settles hnd hT hwbr hst (Stmt2.sem_combInv body hst)
    (fun _ _ hn => ReadWin.agree_of_lookup (Stmt2.sem_frame hT hn st).symm) fun _ _ => rfl

/-- **One ordinary `always_comb`, written before read, is a `SingleE`** (derived from E). -/
theorem singleE_comb {d : Design2} {body : Stmt2} {W : List String}
    (hp : d.processes = #[.alwaysComb body]) (h4 : AllFour (Elab.ofDesign2 d))
    (hnd : (d.decls.toList.map (·.name)).Nodup) (hok : body.combOk d = true)
    (hT : ∀ X ∈ body.targetWins d, X.1 ∈ W) (hwbr : combWbr d W body = true)
    (hin : ∀ x ∈ W, x ∉ d.inputNames.toList) (hcl : ∀ st, CombInv d st → body.claims d st) :
    SingleE (Elab.ofDesign2 d) body (CombInv d) (body.sem d) W := by
  obtain ⟨hE, hpr⟩ := single_elab hp
  refine ⟨hpr, fun σ hTσ hIσ => ?_, fun σ => combInv_view hE, fun st hst => Stmt2.sem_idem hnd hT hwbr hst,
    fun st x hx => Stmt2.sem_frame hT hx st, fun σ entry hTσ hF hq => ?_⟩
  · have := Stmt2.sem_run h4 (by rw [hE]; exact hok) hTσ (by rw [hE]; exact hcl _ hIσ)
    rwa [hE] at this
  · have hag := Elab.not_triggered (by simp [hpr]) hq
    refine Stmt2.sem_settles hnd hT hwbr (combInv_view hE hTσ) (combInv_view hE (hTσ.applyInputs entry))
      (fun r hr hn => hag r (sens_of_readW (by simp [hpr]) (by rw [hE]; exact hT) hr hn)) fun x hx => ?_
    rw [hF]
    exact (Elab.lookup_view_applyInputs_of_not_input σ entry (by rw [hE]; exact hin x hx)).symm

/-- **A slot whose opening keeps the claims** (`SingleE.slot` for a body with a qualified `case`, whose
claim is about inputs a typed view need not keep): the claims are asked only of the states the slot
activates the body on, the opening view and `F` of it. -/
theorem slot_claimed {d : Design2} {body : Stmt2} {W : List String}
    (hp : d.processes = #[.alwaysComb body]) (h4 : AllFour (Elab.ofDesign2 d))
    (hnd : (d.decls.toList.map (·.name)).Nodup) (hok : body.combOk d = true)
    (hT : ∀ X ∈ body.targetWins d, X.1 ∈ W) (hwbr : combWbr d W body = true) (ch : Choice) {c : Config}
    (hTc : (Elab.ofDesign2 d).Typed c.store) (hc : (c.active = [] ∧ body.sem d ((Elab.ofDesign2 d).view
      c.store) = (Elab.ofDesign2 d).view c.store) ∨ c.active = [0])
    (hcl : body.claims d ((Elab.ofDesign2 d).view c.store))
    (hcl' : body.claims d (body.sem d ((Elab.ofDesign2 d).view c.store))) :
    ∃ c', (∀ c'', SlotCloses (Elab.ofDesign2 d) ch c c'' ↔ c'' = c') ∧ c'.active = [] ∧
      (Elab.ofDesign2 d).Typed c'.store ∧
      (Elab.ofDesign2 d).view c'.store = body.sem d ((Elab.ofDesign2 d).view c.store) := by
  obtain ⟨hE, hpr⟩ := single_elab hp
  let E := Elab.ofDesign2 d
  have act : ∀ c₀ : Config, c₀.active = [0] → E.Typed c₀.store → body.claims d (E.view c₀.store) →
      ∃ σ', E.Typed σ' ∧ E.view σ' = body.sem d (E.view c₀.store) ∧
        step E ch c₀ = .next ⟨σ', E.triggered (E.view c₀.store) (E.view σ'), c₀.k + 1⟩ := fun c₀ ha hT0 hc0 => by
    obtain ⟨σ', h1, h2, h3⟩ := activate_single hp h4 hok hT0 hc0
    have hch : ch.choose c₀.k c₀.active = [0] := by rw [ha]; exact List.perm_singleton.mp (ch.choose_perm _ _)
    exact ⟨σ', h2, h3, by simp [E, step, hch, h1]⟩
  rcases hc with ⟨hc, hF⟩ | hc
  · exact ⟨c, SingleE.closes_nil hc, hc, hTc, hF.symm⟩
  obtain ⟨σ₁, hT₁, hv₁, h₁⟩ := act c hc hTc hcl
  have htc : ∀ st st', E.triggered st st' = [] ∨ E.triggered st st' = [0] := by
    intro st st'; unfold Elab.triggered; rw [hpr]
    by_cases h : (E.sens 0).any (fun r => !decide (r.agree st st')) = true <;> simp [h]
  rcases htc _ (E.view σ₁) with h0 | h0
  · exact ⟨_, fun c'' => (SingleE.closes_next h₁ c'').trans (SingleE.closes_nil h0 c''), h0, hT₁, hv₁⟩
  obtain ⟨σ₂, hT₂, hv₂, h₂⟩ := act ⟨σ₁, _, _⟩ h0 hT₁ (by rw [hv₁]; exact hcl')
  have hv : E.view σ₂ = E.view σ₁ := by rw [hv₂, hv₁]; exact Stmt2.sem_idem hnd hT hwbr (combInv_view hE hTc)
  have h00 : E.triggered (E.view σ₁) (E.view σ₂) = [] := by rw [hv]; exact SingleE.triggered_self _ _
  exact ⟨_, fun c'' => (SingleE.closes_next h₁ c'').trans ((SingleE.closes_next h₂ c'').trans
    (SingleE.closes_nil h00 c'')), h00, hT₂, by rw [hv, hv₁]⟩

end LeanModels.Sv.Loop2

#pin_axioms LeanModels.Sv.Loop2.combWbr_spec LeanModels.Sv.Loop2.CombInv.write
  LeanModels.Sv.Loop2.Stmt2.sem_combInv LeanModels.Sv.Loop2.Stmt2.sem_frame
  LeanModels.Sv.Loop2.agree_of_rdOk LeanModels.Sv.Loop2.agree_congr LeanModels.Sv.Loop2.Stmt2.sem_rel
  LeanModels.Sv.Loop2.sens_of_readW LeanModels.Sv.Loop2.singleE_comb LeanModels.Sv.Loop2.Stmt2.sem_settles
  LeanModels.Sv.Loop2.slot_claimed
