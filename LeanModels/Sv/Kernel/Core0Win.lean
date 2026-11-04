import LeanModels.Sv.Kernel.Core0Proc

/-!
# R-COMB-1: the window rank (`LeanModels.Sv.Kernel`)

Queue item R-COMB-1 of `svgolf/design/architecture/EXECUTION-PLAN.md`. **Status: derived from E**
(`Core0.lean`). The same theorems as gates G-A/G-B (every legal schedule closes the slot; the
closed store solves the equations; it is their unique solution, so it is schedule-independent),
with the rank over WRITTEN WINDOWS instead of processes.

## Why

The process rank (`Settles.ranked`, `Acyclic` of the process-level lowering) fails on real
`always_comb` bodies (agent M's X8: 18 of 198): a block that writes `a` and reads `b`, beside
`assign b = f(a)`, is a process-level cycle and a window-level chain (ibex_controller's shape).

## The equation design and the measure

* **Per-window lowering** (`Design2.lowerWin`): every assign is one equation; an `always_comb`
  body in the profile (symbolically executable, self-read free) becomes ONE ASSIGN PER WRITTEN
  WINDOW (`W.lhs = E_W`, the entries of its symbolic state), each tagged with the process it comes
  from. `Design2.winDesign` is the equation design, `winOwn ps p` the equations process `p` owns.
* **`WSettles E d own rank`**: what the settle argument needs. Activating `p` writes every equation
  `p` owns at its pre-state value and nothing else (`WriteRel`); E's sensitivity of `p` covers
  the reads of every equation `p` owns (`complete`); no equation of `p` reads a window of `p`
  (`group`); the rank is a certificate of the EQUATION design (`AcyclicBy d rank`). There is no
  condition relating the rank to E's sensitivity: the rank no longer orders processes.
* **The measure** (`wpotential`): `dirtyW · (P + 1) + |ready|`, where `dirtyW` weighs every
  equation that does not hold by `(M + 1)^(M − rank)`. A step either cleans a dirty equation of
  the lowest rank among those it writes and can only dirty equations of higher rank
  (`WSettles.dirty_source`), or changes nothing and shrinks the ready list.

## Statements

* `WSettles.exec_closes`, `slot_closes`, `slotCloses_combEqs`, `schedule_independent`, `rcomb`:
  R-COMB-0's statements, window rank.
* `WSettles.closed_eq_combSettle2`: E's closed store is what `combSettle2` returns on the DESIGN
  ITSELF whenever it completes (any schedule, any fuel). The settle is carried to the
  process-level lowering by `CombSim` (no rank needed), its equations split per window
  (`combEqs_win_of_lower`), and the window equations have one solution.
* `Settles.toW`: **the process-rank results are the special case** `own p = [p]`. Every `Settles`
  instance (G-A's `Settles.ofProfile0`, G-B's `Settles.ofLower`) is a `WSettles` instance
  (`Core0Smoke.mux1_wsettles`).
* `WSettles.ofLowerWin`: the instance from the per-window lowering (hypotheses static, decided per
  design as for G-B's `Settles.ofLower`, the profile of the equation design by hand: debt D-X1e).
* Fixture (`Core0Smoke.ibex`, an `always_comb` writing `a = x` and `c = b` beside
  `assign b = a + 1`): `ibex_rcomb` (every legal schedule closes at the unique solution),
  `ibex_schedule_independent`, `ibex_closed_eq_combSettle2`, and `ibexLow_not_acyclic` /
  `ibex_no_settles` (the process-level lowering is in the comb profile but fails `Acyclic`, so G-B's
  `Settles` has no instance for it).

## Not proved here

* That `combSettle2` on such a design TERMINATES (the existence half of G-B's `rcomb1`). The
  existing proof (`combSettle2_terminates_of_le`) orders processes; the window version needs a
  pass argument over windows. MEASURED on the fixture: `combSettle2 ibex.toDesign2` completes
  from fuel 8 under both orders.
* MEASURED, not a window-rank issue: `Design2.settleFuel` does not count an `always_comb` body's
  statement fuel. `ibex.toDesign2.settleFuel = 5` (needs 8), and G-B's own `mux1.toDesign2`
  has `settleFuel = 6` (needs 10 under source order, 8 under reverse). Trusted statements quantify
  fuel existentially (`Runs2`), and `svgolf-eval` runs at fuel 100000, so nothing trusted depends
  on it. The explicit-fuel lemmas that use it are stated for assign-only designs.
-/

namespace LeanModels.Sv

/-! ## The per-window lowering -/

/-- Lower one process to one equation per written window: an assign is itself; an `always_comb`
body in the profile becomes one assign per entry of its symbolic state. -/
def Process2.lowerWin (d : Design2) : Process2 → Option (List Process2)
  | .assign t e => some [.assign t e]
  | .alwaysComb body =>
      (body.symExec d []).bind fun S =>
        if S.selfReadFree then some (S.map fun x => .assign x.1.lhs x.2) else none
  | _ => none

/-- `Process2.lowerWin` over a process list (all or nothing). -/
def Design2.lowerWinGroups (d : Design2) : List Process2 → Option (List (List Process2))
  | [] => some []
  | p :: ps => (p.lowerWin d).bind fun g => (Design2.lowerWinGroups d ps).map (g :: ·)

/-- Tag every element of every group with its group's index. -/
def tagFrom {α : Type} : Nat → List (List α) → List (Nat × α)
  | _, [] => []
  | i, g :: gs => g.map (fun q => (i, q)) ++ tagFrom (i + 1) gs

/-- **The per-window lowering**: every equation, with the index of the process it comes from. -/
def Design2.lowerWin (d : Design2) : Option (List (Nat × Process2)) :=
  (d.lowerWinGroups d.processes.toList).map (tagFrom 0)

/-- The equation design of a per-window lowering: same name and declarations. -/
def Design2.winDesign (d : Design2) (ps : List (Nat × Process2)) : Design2 :=
  { d with processes := (ps.map Prod.snd).toArray }

/-- The equations process `p` owns. -/
def winOwn (ps : List (Nat × Process2)) (p : Nat) : List Nat :=
  (List.range ps.length).filter fun j => (ps[j]?.map Prod.fst) == some p

theorem mem_tagFrom {α : Type} {p : Nat} {q : α} : ∀ {i : Nat} {gs : List (List α)},
    (p, q) ∈ tagFrom i gs ↔ i ≤ p ∧ ∃ g, gs[p - i]? = some g ∧ q ∈ g
  | i, [] => by simp [tagFrom]
  | i, g :: gs => by
      rw [tagFrom, List.mem_append, mem_tagFrom]
      simp only [List.mem_map, Prod.mk.injEq]
      constructor
      · rintro (⟨q', hq', h1, h2⟩ | ⟨hle, g', hg', hq⟩)
        · subst h1; subst h2
          exact ⟨Nat.le_refl _, g, by simp, hq'⟩
        · refine ⟨by omega, g', ?_, hq⟩
          have : p - i = (p - (i + 1)) + 1 := by omega
          rw [this]; simpa using hg'
      · rintro ⟨hle, g', hg', hq⟩
        by_cases hpi : p = i
        · subst hpi
          simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hg'
          subst hg'
          exact Or.inl ⟨q, hq, rfl, rfl⟩
        · right
          refine ⟨by omega, g', ?_, hq⟩
          have : p - i = (p - (i + 1)) + 1 := by omega
          rw [this] at hg'; simpa using hg'

theorem Design2.lowerWinGroups_spec {d : Design2} : ∀ {ps : List Process2} {gs : List (List Process2)},
    d.lowerWinGroups ps = some gs → gs.length = ps.length ∧
      ∀ k : Nat, gs[k]? = ps[k]?.bind (Process2.lowerWin d)
  | [], gs, h => by
      simp only [Design2.lowerWinGroups, Option.some.injEq] at h
      subst h
      exact ⟨rfl, fun _ => rfl⟩
  | p :: ps, gs, h => by
      simp only [Design2.lowerWinGroups, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨g, hg, gs', hgs', rfl⟩ := h
      obtain ⟨hlen, hget⟩ := Design2.lowerWinGroups_spec hgs'
      refine ⟨by simp [hlen], fun k => ?_⟩
      cases k with
      | zero => simp [hg]
      | succ k => simp [hget k]

/-- **What the per-window lowering produces**: `(p, q)` is an equation of it exactly when `q` is in
the lowering of process `p`. -/
theorem Design2.mem_lowerWin {d : Design2} {ps : List (Nat × Process2)} (h : d.lowerWin = some ps)
    {p : Nat} {q : Process2} :
    (p, q) ∈ ps ↔ ∃ pr g, d.processes[p]? = some pr ∧ pr.lowerWin d = some g ∧ q ∈ g := by
  simp only [Design2.lowerWin, Option.map_eq_some_iff] at h
  obtain ⟨gs, hgs, rfl⟩ := h
  obtain ⟨-, hget⟩ := Design2.lowerWinGroups_spec hgs
  rw [mem_tagFrom]
  constructor
  · rintro ⟨-, g, hg, hq⟩
    rw [Nat.sub_zero, hget p, Array.getElem?_toList] at hg
    cases hp : d.processes[p]? with
    | none => rw [hp] at hg; cases hg
    | some pr => rw [hp, Option.bind_some] at hg; exact ⟨pr, g, rfl, hg, hq⟩
  · rintro ⟨pr, g, hp, hg, hq⟩
    refine ⟨Nat.zero_le _, g, ?_, hq⟩
    rw [Nat.sub_zero, hget p, Array.getElem?_toList, hp, Option.bind_some, hg]

theorem mem_winOwn {ps : List (Nat × Process2)} {p j : Nat} :
    j ∈ winOwn ps p ↔ ∃ q, ps[j]? = some (p, q) := by
  simp only [winOwn, List.mem_filter, List.mem_range, beq_iff_eq]
  constructor
  · rintro ⟨-, h⟩
    cases hj : ps[j]? with
    | none => rw [hj] at h; cases h
    | some x =>
        rw [hj, Option.map_some, Option.some.injEq] at h
        exact ⟨x.2, by rw [← h]⟩
  · rintro ⟨q, hq⟩
    exact ⟨(List.getElem?_eq_some_iff.mp hq).1, by rw [hq]; rfl⟩

theorem Design2.winDesign_proc (d : Design2) (ps : List (Nat × Process2)) (j : Nat) :
    (d.winDesign ps).processes[j]? = (ps[j]?).map Prod.snd := by
  simp [Design2.winDesign]

/-- A window as a target is that one window. -/
theorem Win.lhs_wins (d : Design2) (W : Win) : W.lhs.wins d = [W] :=
  Lhs2.wins_of_window? rfl

/-- A lowering that succeeds lowers every process. -/
theorem Design2.lowerWin_total {d : Design2} {ps : List (Nat × Process2)} (h : d.lowerWin = some ps)
    {p : Nat} {pr : Process2} (hp : d.processes[p]? = some pr) : ∃ g, pr.lowerWin d = some g := by
  simp only [Design2.lowerWin, Option.map_eq_some_iff] at h
  obtain ⟨gs, hgs, -⟩ := h
  obtain ⟨hlen, hget⟩ := Design2.lowerWinGroups_spec hgs
  have hplt : p < gs.length := by
    rw [hlen, Array.length_toList]; exact (Array.getElem?_eq_some_iff.mp hp).1
  have hg := hget p
  rw [List.getElem?_eq_getElem hplt, Array.getElem?_toList, hp, Option.bind_some] at hg
  exact ⟨_, hg.symm⟩

/-- An `always_comb` the per-window lowering accepts: one assign per entry of its symbolic state. -/
theorem Process2.lowerWin_alwaysComb {d : Design2} {body : Stmt2} {g : List Process2}
    (h : (Process2.alwaysComb body).lowerWin d = some g) :
    ∃ S, body.symExec d [] = some S ∧ S.selfReadFree = true ∧
      g = S.map fun x => .assign x.1.lhs x.2 := by
  simp only [Process2.lowerWin, Option.bind_eq_some_iff] at h
  obtain ⟨S, hS, h⟩ := h
  split at h
  · simp only [Option.some.injEq] at h
    exact ⟨S, hS, by assumption, h.symm⟩
  · cases h

theorem mem_of_getElem?' {α : Type} {l : List α} {i : Nat} {a : α} (h : l[i]? = some a) : a ∈ l := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp h
  exact List.getElem_mem hi

theorem Expr2.mem_listReads {r : ReadWin} : ∀ {es : List Expr2} {e : Expr2}, e ∈ es → r ∈ e.reads →
    r ∈ Expr2.listReads es
  | [], _, h, _ => absurd h List.not_mem_nil
  | e' :: es, e, h, hr => by
      simp only [Expr2.listReads, List.mem_append]
      rcases List.mem_cons.mp h with rfl | h
      · exact Or.inl hr
      · exact Or.inr (Expr2.mem_listReads h hr)

end LeanModels.Sv

namespace LeanModels.Sv.Kernel

set_option autoImplicit false

open LeanModels.Sv.Comb2Term

/-! ## One activation, per equation (`WriteRel`) -/

/-- Equation `i` with its right-hand side read in `st₀` and its windows in `st`
(`ProcEq d st i` is `ProcEqAt d st st i`). -/
def ProcEqAt (d : Design2) (st₀ st : SvState) (i : Nat) : Prop :=
  ∀ (t : Lhs2) (e : Expr2) (n : String) (lo w off : Nat),
    d.processes[i]? = some (.assign t e) → ((n, lo, w), off) ∈ Win.placed (t.wins d) →
      ∃ old v, SvState.lookup st n = some old ∧ evalPure2 st₀ e = .ok v ∧
        old.extract lo w = (v.resizeU (Win.sumWidth (t.wins d))).extract off w

/-- **One activation writes the equations `js`**: every window of every `j ∈ js` takes the value of
its right-hand side BEFORE the write; every other bit and every width is unchanged. -/
structure WriteRel (d : Design2) (js : List Nat) (st₀ st : SvState) : Prop where
  width : ∀ x, (SvState.lookup st₀ x).map LVec.width = (SvState.lookup st x).map LVec.width
  eqs : ∀ j ∈ js, ProcEqAt d st₀ st j
  out : ∀ n b, (∀ j ∈ js, ∀ wn, d.Writes j wn → (ReadWin.win n b 1).overlaps wn = false) →
    (ReadWin.win n b 1).agree st₀ st

/-- A read that observes a bit of a window overlaps the window. -/
theorem ReadWin.overlaps_of_bit {r : ReadWin} {n : String} {i : Nat} {wn : Win}
    (hr : r.overlaps (n, i, 1) = true) (hw : (ReadWin.win n i 1).overlaps wn = true) :
    r.overlaps wn = true := by
  obtain ⟨m, lo, w⟩ := wn
  simp only [ReadWin.overlaps, Win.overlaps_eq_true] at hw
  obtain ⟨hnm, h1, h2⟩ := hw
  subst hnm
  cases r with
  | whole k => simpa [ReadWin.overlaps] using hr
  | win k lo' w' =>
      simp only [ReadWin.overlaps, Win.overlaps_eq_true] at hr ⊢
      obtain ⟨hk, h3, h4⟩ := hr
      exact ⟨hk, by omega, by omega⟩

/-- A read agrees when the widths and every bit it observes agree. -/
theorem ReadWin.agree_of_bits {st st' : SvState} {r : ReadWin}
    (hw : ∀ x, (SvState.lookup st x).map LVec.width = (SvState.lookup st' x).map LVec.width)
    (h : ∀ n i, r.overlaps (n, i, 1) = true → (ReadWin.win n i 1).agree st st') : r.agree st st' := by
  cases r with
  | whole m => exact ReadWin.lookup_eq_of_agree_bits fun i => h m i (by simp [ReadWin.overlaps])
  | win m lo w =>
      exact ReadWin.agree_win_of_bits (hw m) fun k hk =>
        h m (lo + k) (by
          rw [ReadWin.overlaps, Win.overlaps_eq_true]
          exact ⟨rfl, by omega, by omega⟩)

namespace WriteRel

variable {d : Design2} {js : List Nat} {st₀ st : SvState}

/-- A bit of a window of an equation that held before is unchanged. -/
theorem bit_of_clean (hR : WriteRel d js st₀ st) {j : Nat} (hj : j ∈ js) (hc : ProcEq d st₀ j)
    {n : String} {i : Nat} {wn : Win} (hW : d.Writes j wn)
    (hov : (ReadWin.win n i 1).overlaps wn = true) : (ReadWin.win n i 1).agree st₀ st := by
  obtain ⟨t, e, hp, hwn⟩ := hW
  obtain ⟨m, lo, w⟩ := wn
  obtain ⟨off, hoff⟩ := Win.exists_mem_placed hwn
  simp only [ReadWin.overlaps, Win.overlaps_eq_true] at hov
  obtain ⟨hnm, h1, h2⟩ := hov
  subst hnm
  obtain ⟨u, v, hu, hv, hue⟩ := hc t e n lo w off hp hoff
  obtain ⟨u', v', hu', hv', hue'⟩ := hR.eqs j hj t e n lo w off hp hoff
  rw [hv] at hv'
  cases hv'
  have huw : u.width = u'.width := by
    have := hR.width n
    rw [hu, hu'] at this
    simpa using this
  exact agree_bit_of_extract hu hu' huw (hue.trans hue'.symm) (by omega) (by omega)

/-- A bit is unchanged unless it lies in a window of an equation of `js` that did not hold. -/
theorem bit (hR : WriteRel d js st₀ st) (n : String) (i : Nat)
    (h : ∀ j ∈ js, ∀ wn, d.Writes j wn → (ReadWin.win n i 1).overlaps wn = true → ProcEq d st₀ j) :
    (ReadWin.win n i 1).agree st₀ st := by
  by_cases hx : ∃ j ∈ js, ∃ wn, d.Writes j wn ∧ (ReadWin.win n i 1).overlaps wn = true
  · obtain ⟨j, hj, wn, hW, hov⟩ := hx
    exact hR.bit_of_clean hj (h j hj wn hW hov) hW hov
  · exact hR.out n i fun j hj wn hW => Bool.eq_false_iff.mpr fun hov => hx ⟨j, hj, wn, hW, hov⟩

/-- **A read is unchanged** unless it overlaps a window of an equation of `js` that did not hold. -/
theorem agree (hR : WriteRel d js st₀ st) (r : ReadWin)
    (h : ∀ j ∈ js, ∀ wn, d.Writes j wn → r.overlaps wn = true → ProcEq d st₀ j) : r.agree st₀ st :=
  ReadWin.agree_of_bits hR.width fun n i hri => hR.bit n i fun j hj wn hW hov =>
    h j hj wn hW (ReadWin.overlaps_of_bit hri hov)

/-- Every step is a frame step: undriven bits and widths are unchanged. -/
theorem frame (hR : WriteRel d js st₀ st) : Frame d st₀ st :=
  ⟨hR.width, fun x b hu => hR.out x b fun j _ wn hW => Bool.eq_false_iff.mpr fun hov =>
    hu ⟨j, wn, hW, hov⟩⟩

/-- An assign's write is `WriteRel` of every equation that is that assign. -/
theorem ofCombWrite (hd : CombDesign d) {t : Lhs2} {e : Expr2} {s : SvState}
    (hs : StateShape d s) {v : LVec} (hv : evalPure2 s e = .ok v)
    (hjs : ∀ j ∈ js, d.processes[j]? = some (.assign t e)) {j₀ : Nat} (hj₀ : j₀ ∈ js) :
    WriteRel d js s (combWrite d s t v) where
  width x := (SvState.writeWins_width x).symm
  eqs j hj := by
    intro t' e' n lo w off hp hm
    rw [hjs j hj, Option.some.injEq, Process2.assign.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    obtain ⟨u, hu, hue⟩ := hd.combWrite_readBack hs (hjs j hj) v hm
    exact ⟨u, v, hu, hv, hue⟩
  out n b h := ReadWin.agree_combWrite fun wn hwn => h j₀ hj₀ wn ⟨t, e, hjs j₀ hj₀, hwn⟩

/-- **An `always_comb` activation, per window**: a symbolic state's description of the write is
`WriteRel` of the equations that are its entries. -/
theorem ofSymRel (hd : CombDesign d) {S : SymState} (hR : SymRel st₀ S st)
    (hs₀ : StateShape d st₀)
    (hjs : ∀ j ∈ js, ∃ x ∈ S, d.processes[j]? = some (.assign x.1.lhs x.2))
    (hcov : ∀ x ∈ S, ∃ j ∈ js, d.processes[j]? = some (.assign x.1.lhs x.2)) :
    WriteRel d js st₀ st where
  width x := (hR.width x).symm
  eqs j hj := by
    obtain ⟨⟨W, Ex⟩, hx, hp⟩ := hjs j hj
    intro t e n lo w off hpt hm
    rw [hp, Option.some.injEq, Process2.assign.injEq] at hpt
    obtain ⟨rfl, rfl⟩ := hpt
    rw [Win.lhs_wins] at hm ⊢
    simp only [Win.placed, Win.sumWidth, List.mem_cons, List.not_mem_nil, or_false,
      Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    obtain ⟨v, hv⟩ := hd.evalPure2_ok hs₀ hp
    obtain ⟨u, hu, hue⟩ := hR.entry _ _ hx v hv
    simp only at hu hue
    refine ⟨u, v, hu, hv, ?_⟩
    have hvw : v.width = w := by rw [← hue, LVec.width_extract]
    simp only [Win.sumWidth, Nat.add_zero]
    rw [LVec.resizeU_of_width hvw, LVec.extract_zero_of_width hvw]
    exact hue
  out n b h := by
    refine ReadWin.agree_symm (hR.frame n b fun W hW => ?_)
    obtain ⟨⟨W', Ex⟩, hx, rfl⟩ := List.mem_map.mp hW
    obtain ⟨j, hj, hp⟩ := hcov _ hx
    exact h j hj W' ⟨_, _, hp, by rw [Win.lhs_wins]; exact List.mem_singleton_self _⟩

end WriteRel

/-- Every read agreeing carries every equation over. -/
theorem ProcEq.transfer {d : Design2} {st st' : SvState} {j : Nat}
    (h : ∀ r : ReadWin, r.agree st st') (hc : ProcEq d st j) : ProcEq d st' j := by
  intro t e n lo w off hp hm
  obtain ⟨old, v, hlo, hv, hext⟩ := hc t e n lo w off hp hm
  refine ⟨old, v, ?_, ?_, hext⟩
  · have := h (.whole n)
    simp only [ReadWin.agree] at this
    rw [← this]; exact hlo
  · rw [← hv]; exact (evalPure2_congr_reads fun r _ => h r).symm

/-- An equation that does not hold exists. -/
theorem lt_of_not_procEq {d : Design2} {st : SvState} {j : Nat} (h : ¬ ProcEq d st j) :
    j < d.processes.size :=
  Classical.byContradiction fun hj => h fun t e n lo w off hp _ => by
    rw [Array.getElem?_eq_none (by omega)] at hp
    cases hp

/-! ## The equation design (`WSettles`) -/

/-- **What the settle argument needs of an equation design `d`, window rank.** Each process `p`
of E owns the equations `own p`; every equation is owned by exactly one process (`disj`,
`cover`). Activating `p` on a typed store succeeds and writes exactly its equations at their
pre-state values (`act`). E's sensitivity of `p` covers the reads of every equation it owns
(`complete`); no equation of `p` reads a window of `p` (`group`: an `always_comb` block is not
woken by its own writes). The rank is a certificate of the EQUATION design (`ranked`), bounded by
the number of equations (`bound`). -/
structure WSettles (E : Elab) (d : Design2) (own : ProcId → List Nat) (rank : Nat → Nat) :
    Prop where
  comb : CombDesign d
  decls : d.decls = E.decls
  four : AllFour E
  disj : ∀ p q j, j ∈ own p → j ∈ own q → p = q
  cover : ∀ j, j < d.processes.size → ∃ p, p < E.procs.size ∧ j ∈ own p
  act : ∀ (s : Store) (p : ProcId), E.Typed s → p < E.procs.size →
    ∃ s', activate E p s = .ok (.ok (), s') ∧ E.Typed s' ∧
      WriteRel d (own p) (E.view s) (E.view s')
  complete : ∀ (q : ProcId) (j : Nat) (t : Lhs2) (e : Expr2), j ∈ own q →
    d.processes[j]? = some (.assign t e) → ∀ r ∈ e.reads, r ∈ E.sens q
  group : ∀ (p : ProcId) (j j' : Nat) (t : Lhs2) (e : Expr2), j ∈ own p → j' ∈ own p →
    d.processes[j]? = some (.assign t e) → ∀ r ∈ e.reads, ∀ wn, d.Writes j' wn →
      r.overlaps wn = false
  ranked : AcyclicBy d rank
  bound : ∀ j, j < d.processes.size → rank j < d.processes.size

/-- **The settle invariant, window rank**: typed store, a duplicate-free ready set of processes,
and every equation of every process NOT ready holds. -/
structure WSettleInv (E : Elab) (d : Design2) (own : ProcId → List Nat) (c : Config) : Prop where
  typed : E.Typed c.store
  nodup : c.active.Nodup
  range : ∀ q ∈ c.active, q < E.procs.size
  eqs : ∀ q, q < E.procs.size → q ∉ c.active → ∀ j ∈ own q, ProcEq d (E.view c.store) j

/-- With every process ready, the invariant holds of any typed store. -/
theorem WSettleInv.init {E : Elab} {d : Design2} {own : ProcId → List Nat} {s : Store}
    (hT : E.Typed s) : WSettleInv E d own (Config.init E s) where
  typed := hT
  nodup := List.nodup_range
  range := fun _ hq => List.mem_range.mp hq
  eqs := fun _ hq hna => absurd (List.mem_range.mpr hq) hna

namespace WSettles

variable {E : Elab} {d : Design2} {own : ProcId → List Nat} {rank : Nat → Nat}

theorem shape (hS : WSettles E d own rank) {s : Store} (hT : E.Typed s) :
    StateShape d (E.view s) :=
  Elab.shape_view_of hS.comb hS.decls hT

theorem acyclic (hS : WSettles E d own rank) : Acyclic d := ⟨rank, hS.ranked⟩

/-- The equations a process just wrote hold. -/
theorem own_clean (hS : WSettles E d own rank) {p : ProcId} {st₀ st : SvState}
    (hW : WriteRel d (own p) st₀ st) {j : Nat} (hj : j ∈ own p) : ProcEq d st j := by
  intro t e n lo w off hp hm
  obtain ⟨u, v, hu, hv, hue⟩ := hW.eqs j hj t e n lo w off hp hm
  refine ⟨u, v, hu, ?_, hue⟩
  rw [← hv]
  refine (evalPure2_congr_reads fun r hr => hW.agree r fun j' hj' wn hW' hov => ?_).symm
  rw [hS.group p j j' t e hj hj' hp r hr wn hW'] at hov
  cases hov

/-- An equation of another process whose reads did not change keeps holding. -/
theorem keep_clean (hS : WSettles E d own rank) {p : ProcId} {st₀ st : SvState}
    (hW : WriteRel d (own p) st₀ st) {j : Nat} (hj : j ∉ own p) (hc : ProcEq d st₀ j)
    (hreads : ∀ t e, d.processes[j]? = some (.assign t e) → ∀ r ∈ e.reads, r.agree st₀ st) :
    ProcEq d st j := by
  intro t e n lo w off hp hm
  obtain ⟨old, v, hlo, hv, hext⟩ := hc t e n lo w off hp hm
  have hwin : (ReadWin.win n lo w).agree st₀ st := hW.agree _ fun j' hj' wn hW' hov => by
    have hne : j ≠ j' := fun h => hj (h ▸ hj')
    have := hS.comb.disjoint j j' (n, lo, w) wn hne ⟨t, e, hp, Win.mem_of_mem_placed hm⟩ hW'
    simp only [ReadWin.overlaps] at hov
    rw [this] at hov
    cases hov
  simp only [ReadWin.agree, hlo, Option.map_some] at hwin
  cases hlo' : SvState.lookup st n with
  | none => rw [hlo'] at hwin; cases hwin
  | some old' =>
      rw [hlo'] at hwin
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hwin
      refine ⟨old', v, rfl, ?_, hwin.2.symm.trans hext⟩
      rw [← hv]
      exact (evalPure2_congr_reads (hreads t e hp)).symm

/-- **Where a new violation comes from.** An equation of another process that held before the
write and fails after it reads a window of an equation of `p` that did not hold before, so that
equation ranks strictly lower. -/
theorem dirty_source (hS : WSettles E d own rank) {p : ProcId} {st₀ st : SvState}
    (hW : WriteRel d (own p) st₀ st) {j : Nat} (hj : j ∉ own p) (hc : ProcEq d st₀ j)
    (hd : ¬ ProcEq d st j) : ∃ j' ∈ own p, ¬ ProcEq d st₀ j' ∧ rank j' < rank j :=
  Classical.byContradiction fun hno => hd (hS.keep_clean hW hj hc fun t e hp r hr =>
    hW.agree r fun j' hj' wn hW' hov => Classical.byContradiction fun hc' => by
      obtain ⟨tj, ej, hpj, hwn⟩ := hW'
      exact hno ⟨j', hj', hc', hS.ranked j j' t e tj ej wn hp hpj hwn ⟨r, hr, hov⟩⟩)

/-- **One step activates the chosen process and writes its equations.** -/
theorem step_cons (hS : WSettles E d own rank) {ch : Choice} {c : Config}
    (hI : WSettleInv E d own c) {p : ProcId} {rest : List ProcId}
    (hch : ch.choose c.k c.active = p :: rest) :
    ∃ s', E.Typed s' ∧ WriteRel d (own p) (E.view c.store) (E.view s') ∧
      step E ch c = .next { store := s'
                            active := rest ++ (E.triggered (E.view c.store) (E.view s')).filter
                              (fun q => decide (q ∉ rest))
                            k := c.k + 1 } := by
  have hpa : p ∈ c.active := by
    have : p ∈ ch.choose c.k c.active := by rw [hch]; exact List.mem_cons_self ..
    exact (ch.choose_perm c.k c.active).mem_iff.mp this
  obtain ⟨s', ha, hT, hW⟩ := hS.act c.store p hI.typed (hI.range p hpa)
  refine ⟨s', hT, hW, ?_⟩
  unfold step
  rw [hch]
  simp only [ha]

theorem step_next_spec (hS : WSettles E d own rank) {ch : Choice} {c c' : Config}
    (hI : WSettleInv E d own c) (h : step E ch c = .next c') :
    ∃ p rest, ch.choose c.k c.active = p :: rest ∧ E.Typed c'.store ∧
      WriteRel d (own p) (E.view c.store) (E.view c'.store) ∧
      c'.active = rest ++ (E.triggered (E.view c.store) (E.view c'.store)).filter
        (fun q => decide (q ∉ rest)) := by
  cases hch : ch.choose c.k c.active with
  | nil => simp [step, hch] at h
  | cons p rest =>
      obtain ⟨s', hT, hW, hstep⟩ := hS.step_cons hI hch
      rw [hstep, StepResult.next.injEq] at h
      subst h
      exact ⟨p, rest, rfl, hT, hW, rfl⟩

/-- **The settle invariant is preserved by every step.** -/
theorem step_inv (hS : WSettles E d own rank) {ch : Choice} {c c' : Config}
    (hI : WSettleInv E d own c) (h : step E ch c = .next c') : WSettleInv E d own c' := by
  obtain ⟨p, rest, hch, hT, hW, hact⟩ := hS.step_next_spec hI h
  have hperm := ch.choose_perm c.k c.active
  rw [hch] at hperm
  obtain ⟨_, _, _, _, hnd'⟩ := step_legal hI.nodup h
  refine ⟨hT, hnd', ?_, ?_⟩
  · intro q hq
    rw [hact] at hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hI.range q (hperm.mem_iff.mp (List.mem_cons_of_mem _ hq))
    · exact (Elab.mem_triggered (List.mem_filter.mp hq).1).1
  · intro q hqn hq j hj
    have hq_rest : q ∉ rest := fun h' => hq (by rw [hact]; exact List.mem_append_left _ h')
    by_cases hqp : q = p
    · subst hqp
      exact hS.own_clean hW hj
    · have hqa : q ∉ c.active := fun h' => by
        rcases List.mem_cons.mp (hperm.mem_iff.mpr h') with h'' | h''
        · exact hqp h''
        · exact hq_rest h''
      have hnt : q ∉ E.triggered (E.view c.store) (E.view c'.store) := fun h' => hq (by
        rw [hact]
        exact List.mem_append_right _ (List.mem_filter.mpr ⟨h', by simpa using hq_rest⟩))
      have hreads := Elab.not_triggered hqn hnt
      exact hS.keep_clean hW (fun h' => hqp (hS.disj q p j hj h')) (hI.eqs q hqn hqa j hj)
        fun t e hp r hr => hreads r (hS.complete q j t e hj hp r hr)

theorem step_frame (hS : WSettles E d own rank) {ch : Choice} {c c' : Config}
    (hI : WSettleInv E d own c) (h : step E ch c = .next c') :
    Frame d (E.view c.store) (E.view c'.store) := by
  obtain ⟨p, rest, -, -, hW, -⟩ := hS.step_next_spec hI h
  exact hW.frame

theorem steps_inv (hS : WSettles E d own rank) {ch : Choice} {c c' : Config}
    (h : Steps E ch c c') : WSettleInv E d own c → WSettleInv E d own c' := by
  induction h with
  | refl => exact id
  | head hs _ ih => exact fun hI => ih (hS.step_inv hI hs)

theorem steps_frame (hS : WSettles E d own rank) {ch : Choice} {c c' : Config}
    (h : Steps E ch c c') : WSettleInv E d own c → Frame d (E.view c.store) (E.view c'.store) := by
  induction h with
  | refl c => exact fun _ => Frame.refl _
  | head hs _ ih => exact fun hI => (hS.step_frame hI hs).trans (ih (hS.step_inv hI hs))

end WSettles

/-! ## The dirty-window measure -/

theorem wsum_mono {f g : ProcId → Nat} : ∀ {l : List ProcId}, (∀ j ∈ l, f j ≤ g j) →
    wsum f l ≤ wsum g l
  | [], _ => Nat.le_refl _
  | q :: _, h => Nat.add_le_add (h q (List.mem_cons_self ..))
      (wsum_mono fun j hj => h j (List.mem_cons_of_mem _ hj))

theorem wsum_add (f g : ProcId → Nat) : ∀ l, wsum (fun j => f j + g j) l = wsum f l + wsum g l
  | [] => rfl
  | q :: qs => by simp only [wsum, wsum_add f g qs]; omega

theorem wsum_zero {f : ProcId → Nat} : ∀ {l : List ProcId}, (∀ j ∈ l, f j = 0) → wsum f l = 0
  | [], _ => rfl
  | q :: qs, h => by
      simp only [wsum, h q (List.mem_cons_self ..), wsum_zero fun j hj => h j (List.mem_cons_of_mem _ hj)]

theorem wsum_single (c : Nat) {j₀ : ProcId} : ∀ {l : List ProcId}, l.Nodup → j₀ ∈ l →
    wsum (fun j => if j = j₀ then c else 0) l = c
  | [], _, h => absurd h List.not_mem_nil
  | q :: qs, hnd, h => by
      rw [List.nodup_cons] at hnd
      simp only [wsum]
      rcases List.mem_cons.mp h with h | h
      · subst h
        rw [if_pos rfl, wsum_zero fun j hj => if_neg fun (hj' : j = j₀) => hnd.1 (hj' ▸ hj),
          Nat.add_zero]
      · rw [if_neg fun (h' : q = j₀) => hnd.1 (h' ▸ h), wsum_single c hnd.2 h, Nat.zero_add]

theorem wsum_ite_filter (w : ProcId → Nat) (P : ProcId → Prop) [DecidablePred P] :
    ∀ l, wsum (fun j => if P j then w j else 0) l = wsum w (l.filter fun j => decide (P j))
  | [] => rfl
  | q :: qs => by
      by_cases hq : P q
      · simp [wsum, hq, wsum_ite_filter w P qs]
      · simp [wsum, hq, wsum_ite_filter w P qs]

/-- A rank-minimal member of a non-empty list. -/
theorem exists_min_mem (f : Nat → Nat) : ∀ {L : List Nat}, L ≠ [] →
    ∃ j ∈ L, ∀ j' ∈ L, f j ≤ f j'
  | [], h => absurd rfl h
  | a :: l, _ => by
      by_cases hl : l = []
      · subst hl
        exact ⟨a, List.mem_singleton_self a, fun j' hj' => by
          rw [List.mem_singleton.mp hj']; exact Nat.le_refl _⟩
      · obtain ⟨m, hm, hmin⟩ := exists_min_mem f hl
        by_cases hle : f a ≤ f m
        · refine ⟨a, List.mem_cons_self .., fun j' hj' => ?_⟩
          rcases List.mem_cons.mp hj' with rfl | hj'
          · exact Nat.le_refl _
          · exact Nat.le_trans hle (hmin j' hj')
        · refine ⟨m, List.mem_cons_of_mem _ hm, fun j' hj' => ?_⟩
          rcases List.mem_cons.mp hj' with rfl | hj'
          · omega
          · exact hmin j' hj'

open Classical in
/-- **The weight of the violated equations**: equation `j` that does not hold weighs
`(M + 1)^(M − rank j)` (`M` equations), so one of rank `r` outweighs all those of higher rank. -/
noncomputable def dirtyW (d : Design2) (rank : Nat → Nat) (st : SvState) : Nat :=
  wsum (fun j => if ProcEq d st j then 0 else (d.processes.size + 1) ^ (d.processes.size - rank j))
    (List.range d.processes.size)

/-- **The window measure**: violated equations first, then the ready list. -/
noncomputable def wpotential (E : Elab) (d : Design2) (rank : Nat → Nat) (c : Config) : Nat :=
  dirtyW d rank (E.view c.store) * (E.procs.size + 1) + c.active.length

theorem WSettleInv.length_le {E : Elab} {d : Design2} {own : ProcId → List Nat} {c : Config}
    (hI : WSettleInv E d own c) : c.active.length ≤ E.procs.size := by
  have := hI.nodup.length_le_of_subset (l₂ := List.range E.procs.size)
    fun q hq => List.mem_range.mpr (hI.range q hq)
  rwa [List.length_range] at this

/-- **Every step strictly decreases the window measure** and keeps the invariant. -/
theorem WSettles.step_decreases {E : Elab} {d : Design2} {own : ProcId → List Nat}
    {rank : Nat → Nat} (hS : WSettles E d own rank) {ch : Choice} {c : Config}
    (hI : WSettleInv E d own c) {p : ProcId} {rest : List ProcId}
    (hch : ch.choose c.k c.active = p :: rest) :
    ∃ c', step E ch c = .next c' ∧ WSettleInv E d own c' ∧
      wpotential E d rank c' < wpotential E d rank c := by
  classical
  obtain ⟨s', hT, hW, hstep⟩ := hS.step_cons hI hch
  have hI' := hS.step_inv hI hstep
  refine ⟨_, hstep, hI', ?_⟩
  have hperm := ch.choose_perm c.k c.active
  rw [hch] at hperm
  have hlen : c.active.length = rest.length + 1 := by rw [← hperm.length_eq]; rfl
  have hlen' := hI'.length_le
  simp only [wpotential] at hlen' ⊢
  generalize E.view c.store = pre at hW hlen' ⊢
  generalize E.view s' = post at hW hlen' ⊢
  by_cases hD : ∃ j ∈ own p, ¬ ProcEq d pre j
  · -- a violated equation of `p` is cleaned; new violations rank strictly higher
    obtain ⟨j₀, hj₀m, hmin⟩ := exists_min_mem rank (L := (own p).filter fun j => ¬ ProcEq d pre j)
      (by
        obtain ⟨j, hj, hc⟩ := hD
        exact List.ne_nil_of_mem (List.mem_filter.mpr ⟨hj, by simpa using hc⟩))
    obtain ⟨hj₀, hc₀⟩ := List.mem_filter.mp hj₀m
    simp only [decide_eq_true_eq] at hc₀
    have hj₀M := lt_of_not_procEq hc₀
    have hr₀ := hS.bound j₀ hj₀M
    have hmin' : ∀ j' ∈ own p, ¬ ProcEq d pre j' → rank j₀ ≤ rank j' := fun j' hj' hc' =>
      hmin j' (List.mem_filter.mpr ⟨hj', by simpa using hc'⟩)
    let M := d.processes.size
    let w : Nat → Nat := fun j => (M + 1) ^ (M - rank j)
    let g : Nat → Nat := fun j => if rank j₀ < rank j ∧ ¬ ProcEq d post j then w j else 0
    have hpt : ∀ j ∈ List.range M,
        (if ProcEq d post j then 0 else w j) + (if j = j₀ then w j₀ else 0) ≤
          (if ProcEq d pre j then 0 else w j) + g j := by
      intro j _
      by_cases hjj : j = j₀
      · subst hjj
        rw [if_pos (hS.own_clean hW hj₀), if_pos rfl, if_neg hc₀]
        omega
      · rw [if_neg hjj, Nat.add_zero]
        by_cases hpo : ProcEq d post j
        · rw [if_pos hpo]; exact Nat.zero_le _
        · rw [if_neg hpo]
          by_cases hpr : ProcEq d pre j
          · have hjo : j ∉ own p := fun h => hpo (hS.own_clean hW h)
            obtain ⟨j', hj', hc', hlt⟩ := hS.dirty_source hW hjo hpr hpo
            have : rank j₀ < rank j := Nat.lt_of_le_of_lt (hmin' j' hj' hc') hlt
            rw [if_pos hpr, show g j = w j from if_pos ⟨this, hpo⟩]
            omega
          · rw [if_neg hpr]; omega
    have hsum := wsum_mono hpt
    rw [wsum_add, wsum_add, wsum_single _ List.nodup_range (List.mem_range.mpr hj₀M)] at hsum
    have hg : wsum g (List.range M) < w j₀ := by
      simp only [g]
      rw [wsum_ite_filter]
      exact wsum_higher_lt hr₀ ((List.nodup_range).filter _)
        (fun q hq => List.mem_range.mp (List.mem_filter.mp hq).1)
        (fun q hq => (by simpa using (List.mem_filter.mp hq).2 : rank j₀ < rank q ∧ _).1)
    have hdw : dirtyW d rank post + 1 ≤ dirtyW d rank pre := by
      show wsum (fun j => if ProcEq d post j then 0 else w j) (List.range M) + 1 ≤
        wsum (fun j => if ProcEq d pre j then 0 else w j) (List.range M)
      omega
    have hmul := Nat.mul_le_mul_right (E.procs.size + 1) hdw
    rw [Nat.succ_mul] at hmul
    generalize dirtyW d rank post * (E.procs.size + 1) = X at hmul ⊢
    generalize dirtyW d rank pre * (E.procs.size + 1) = Y at hmul ⊢
    omega
  · -- every equation of `p` held: nothing changes, and the ready list shrinks
    have hc : ∀ j ∈ own p, ProcEq d pre j := fun j hj =>
      Classical.byContradiction fun h => hD ⟨j, hj, h⟩
    have hall : ∀ r : ReadWin, ReadWin.agree pre post r := fun r =>
      hW.agree r fun j hj _ _ _ => hc j hj
    have htr : E.triggered pre post = [] :=
      List.eq_nil_iff_forall_not_mem.mpr fun q hq => by
        obtain ⟨-, r, -, hna⟩ := Elab.mem_triggered hq
        exact hna (hall r)
    have hact : rest.length = (rest ++ (E.triggered pre post).filter
        fun q => decide (q ∉ rest)).length := by
      rw [htr]; simp
    have hdw : dirtyW d rank post ≤ dirtyW d rank pre := by
      simp only [dirtyW]
      refine wsum_mono fun j _ => ?_
      by_cases hpr : ProcEq d pre j
      · rw [if_pos hpr, if_pos (ProcEq.transfer hall hpr)]; exact Nat.le_refl 0
      · rw [if_neg hpr]; split <;> omega
    have hmul := Nat.mul_le_mul_right (E.procs.size + 1) hdw
    rw [← hact, hlen]
    generalize dirtyW d rank post * (E.procs.size + 1) = X at hmul ⊢
    generalize dirtyW d rank pre * (E.procs.size + 1) = Y at hmul ⊢
    omega

/-! ## The slot closes, under every legal schedule -/

theorem WSettles.exec_closes_of_lt {E : Elab} {d : Design2} {own : ProcId → List Nat}
    {rank : Nat → Nat} (hS : WSettles E d own rank) (ch : Choice) : ∀ (m : Nat) (c : Config),
      wpotential E d rank c < m → WSettleInv E d own c → ∃ c', exec E ch m c = .closed c'
  | 0, _, h, _ => absurd h (Nat.not_lt_zero _)
  | m + 1, c, hm, hI => by
      cases hch : ch.choose c.k c.active with
      | nil =>
          refine ⟨c, ?_⟩
          simp only [exec, step, hch]
      | cons p rest =>
          obtain ⟨c₁, hstep, hI₁, hlt⟩ := hS.step_decreases hI hch
          obtain ⟨c', hc'⟩ := hS.exec_closes_of_lt ch m c₁ (by omega) hI₁
          exact ⟨c', by simp only [exec, hstep]; exact hc'⟩

/-- **Every legal schedule closes the slot within `wpotential + 1` steps.** -/
theorem WSettles.exec_closes {E : Elab} {d : Design2} {own : ProcId → List Nat}
    {rank : Nat → Nat} (hS : WSettles E d own rank) (ch : Choice) {c : Config}
    (hI : WSettleInv E d own c) :
    ∃ c', exec E ch (wpotential E d rank c + 1) c = .closed c' :=
  hS.exec_closes_of_lt ch _ c (Nat.lt_succ_self _) hI

/-- **The slot closes** under every legal schedule, and the invariant holds there. -/
theorem WSettles.slot_closes {E : Elab} {d : Design2} {own : ProcId → List Nat}
    {rank : Nat → Nat} (hS : WSettles E d own rank) (ch : Choice) {c : Config}
    (hI : WSettleInv E d own c) : ∃ c', SlotCloses E ch c c' ∧ WSettleInv E d own c' := by
  obtain ⟨c', hc'⟩ := hS.exec_closes ch hI
  have hcl := exec_sound hc'
  exact ⟨c', hcl, hS.steps_inv hcl.1 hI⟩

/-- **The closed store solves every window equation** and keeps every undriven bit. -/
theorem WSettles.slotCloses_combEqs {E : Elab} {d : Design2} {own : ProcId → List Nat}
    {rank : Nat → Nat} (hS : WSettles E d own rank) {ch : Choice} {c c' : Config}
    (hI : WSettleInv E d own c) (h : SlotCloses E ch c c') :
    CombEqs d (E.view c'.store) ∧ StateShape d (E.view c'.store) ∧
      Frame d (E.view c.store) (E.view c'.store) := by
  have hI' := hS.steps_inv h.1 hI
  have hnil := active_nil_of_closed h.2
  refine ⟨?_, hS.shape hI'.typed, hS.steps_frame h.1 hI⟩
  intro i t e n lo w off hp hm
  have hin : i < d.processes.size := (Array.getElem?_eq_some_iff.mp hp).1
  obtain ⟨q, hq, hiq⟩ := hS.cover i hin
  exact hI'.eqs q hq (by rw [hnil]; exact List.not_mem_nil) i hiq t e n lo w off hp hm

/-- **Schedule independence**, window rank. -/
theorem WSettles.schedule_independent {E : Elab} {d : Design2} {own : ProcId → List Nat}
    {rank : Nat → Nat} (hS : WSettles E d own rank) {c c₁ c₂ : Config} {ch₁ ch₂ : Choice}
    (hI : WSettleInv E d own c) (h₁ : SlotCloses E ch₁ c c₁) (h₂ : SlotCloses E ch₂ c c₂) :
    E.view c₁.store = E.view c₂.store := by
  obtain ⟨he₁, hs₁, hf₁⟩ := hS.slotCloses_combEqs hI h₁
  obtain ⟨he₂, hs₂, hf₂⟩ := hS.slotCloses_combEqs hI h₂
  exact combEqs_unique hS.comb hS.acyclic hs₁ hs₂ he₁ he₂ (hf₁.symm.trans hf₂)

/-- **R-COMB-1, generic** (derived from E): from every configuration satisfying the invariant,
under every legal schedule, the slot closes; the closed store solves the window equations, keeps
the undriven bits, and is the ONLY shaped solution that does. -/
theorem WSettles.rcomb {E : Elab} {d : Design2} {own : ProcId → List Nat} {rank : Nat → Nat}
    (hS : WSettles E d own rank) (ch : Choice) {c : Config} (hI : WSettleInv E d own c) :
    ∃ c', SlotCloses E ch c c' ∧ CombEqs d (E.view c'.store) ∧
      Frame d (E.view c.store) (E.view c'.store) ∧
      ∀ st, StateShape d st → CombEqs d st → Frame d (E.view c.store) st → st = E.view c'.store := by
  obtain ⟨c', hcl, -⟩ := hS.slot_closes ch hI
  obtain ⟨he, hs, hf⟩ := hS.slotCloses_combEqs hI hcl
  exact ⟨c', hcl, he, hf, fun st hst hest hfst =>
    combEqs_unique hS.comb hS.acyclic hst hs hest he (hfst.symm.trans hf)⟩

/-! ## The process rank is the special case `own p = [p]` -/

/-- **Every process-rank equation design is a window-rank one**, each process owning its own
equation. G-A's `Settles.ofProfile0` and G-B's `Settles.ofLower` instances are therefore
`WSettles` instances, and every theorem above holds of them. -/
theorem Settles.toW {E : Elab} {d : Design2} {rank : Nat → Nat} (hS : Settles E d rank) :
    WSettles E d (fun p => [p]) rank where
  comb := hS.comb
  decls := hS.decls
  four := hS.four
  disj := fun p q j hp hq => by
    rw [List.mem_singleton] at hp hq
    rw [← hp, ← hq]
  cover := fun j hj => ⟨j, by rwa [← hS.size], List.mem_singleton_self j⟩
  act := fun s p hT hpn => by
    obtain ⟨t, e, v, s', hp, hv, ha, hview, hT'⟩ := hS.act s p hT hpn
    refine ⟨s', ha, hT', ?_⟩
    rw [hview]
    exact WriteRel.ofCombWrite hS.comb (hS.shape hT) hv
      (fun j hj => by rw [List.mem_singleton.mp hj]; exact hp) (List.mem_singleton_self p)
  complete := fun q j t e hj hp r hr => by
    rw [List.mem_singleton.mp hj] at hp
    exact hS.complete q t e hp r hr
  group := fun p j j' t e hj hj' hp r hr wn hW => by
    rw [List.mem_singleton.mp hj] at hp
    rw [List.mem_singleton.mp hj'] at hW
    obtain ⟨t', e', hp', hwn⟩ := hW
    rw [hp, Option.some.injEq, Process2.assign.injEq] at hp'
    obtain ⟨rfl, rfl⟩ := hp'
    exact reads_not_own hS.acyclicBy hp r hr wn hwn
  ranked := hS.acyclicBy
  bound := fun j hj => by
    rw [hS.size] at hj ⊢
    exact hS.bound j hj

/-! ## The instance from the per-window lowering -/

/-- A typed store's view binds every declared name at its declared width. -/
theorem Elab.lookup_view_width {E : Elab} {s : Store} (hT : E.Typed s) {n : String} {dw : Nat}
    (hw : E.toDesign2.declWidth n = some dw) :
    (SvState.lookup (E.view s) n).map LVec.width = some dw := by
  rw [E.lookup_view]
  cases hx : E.resolve n with
  | none => rw [Elab.resolve_none hx] at hw; cases hw
  | some x =>
      obtain ⟨dc, hdecl, -, -, hdw⟩ := Elab.resolve_some hx
      rw [hdw, Option.some.injEq] at hw
      subst hw
      simp only [Option.map_some, Option.some.injEq]
      rw [(s x).width_eq, hT x dc hdecl]
      rfl

/-- **R-BODY-0, per window.** An `always_comb` activation on a typed store succeeds, and its
symbolic state describes the write on the view: every entry window holds its expression's
pre-state value, every other bit is unchanged. -/
theorem activate_comb_symRel {E : Elab} (h4 : AllFour E) {p : ProcId} {body : Stmt2}
    {S : SymState} (hp : E.procs[p]? = some (.comb body))
    (hsym : body.symExec E.toDesign2 [] = some S) (hq : body.qualFree = true) {s : Store}
    (hT : E.Typed s) :
    ∃ s', activate E p s = .ok (.ok (), s') ∧ E.Typed s' ∧ SymRel (E.view s) S (E.view s') := by
  have hb : ∀ x ∈ E.toDesign2.symNames, ∃ v, SvState.lookup (E.view s) x = some v := by
    intro x hx
    refine SvState.exists_lookup_of_mem ?_
    rw [E.keys_view]
    simpa [Design2.symNames, Elab.toDesign2] using hx
  have hok : SymOk E.toDesign2 (E.view s) S := fun _ _ _ hdw => Elab.lookup_view_width hT hdw
  obtain ⟨⟨st', nba⟩, hrun⟩ := (symExec_total hb body.fuelB).1 body [] S (E.view s) [] hsym hok
    (SymRel.init _) (Nat.le_refl _)
  obtain ⟨rfl, hR⟩ := (symExec_sound body.fuelB).1 body [] S (E.view s) [] st' nba hsym hok
    (SymRel.init _) hrun
  obtain ⟨-, s', hs', hv', hT'⟩ := (execBody_of_execStmt2 h4 body.fuelB).1 body s [] st' [] hT
    (Stmt2.staticB_of_symExec body hsym hq) hrun
  refine ⟨s', ?_, hT', by rw [hv']; exact hR⟩
  simp only [activate, hp]
  exact hs'

/-- Sensitivity-completeness of the equations, decided: every read of every equation is in E's
sensitivity of the process it comes from. -/
def completeWB (E : Elab) (ps : List (Nat × Process2)) : Bool :=
  ps.all fun x => match x with
    | (p, .assign _ e) => e.reads.all fun r => decide (r ∈ E.sens p)
    | _ => true

theorem complete_of_completeWB {E : Elab} {ps : List (Nat × Process2)} (h : completeWB E ps = true)
    {p : Nat} {t : Lhs2} {e : Expr2} (hm : (p, Process2.assign t e) ∈ ps) :
    ∀ r ∈ e.reads, r ∈ E.sens p := by
  simp only [completeWB, List.all_eq_true] at h
  have := h _ hm
  simp only [List.all_eq_true, decide_eq_true_eq] at this
  exact this

/-- The rank certificate of an equation design, decided. -/
def acyclicB (d : Design2) (rank : Nat → Nat) : Bool :=
  (List.range d.processes.size).all fun i => (List.range d.processes.size).all fun j =>
    match d.processes[i]?, d.processes[j]? with
    | some (.assign _ ei), some (.assign tj _) =>
        ei.reads.all fun r => (tj.wins d).all fun w => !(r.overlaps w) || decide (rank j < rank i)
    | _, _ => true

theorem acyclicBy_of_acyclicB {d : Design2} {rank : Nat → Nat} (h : acyclicB d rank = true) :
    AcyclicBy d rank := by
  intro i j ti ei tj ej wj hi hj hw ⟨r, hr, hov⟩
  have hin : i < d.processes.size := (Array.getElem?_eq_some_iff.mp hi).1
  have hjn : j < d.processes.size := (Array.getElem?_eq_some_iff.mp hj).1
  simp only [acyclicB, List.all_eq_true, List.mem_range] at h
  have h' := h i hin j hjn
  rw [hi, hj] at h'
  simp only [List.all_eq_true] at h'
  have h2 := h' r hr wj hw
  rw [hov] at h2
  simpa using h2

/-- The equations `p` owns are `p`'s lowering. -/
theorem winOwn_spec {E : Elab} {ps : List (Nat × Process2)} (hl : E.toDesign2.lowerWin = some ps)
    {p : ProcId} {pr : Process2} {g : List Process2} (hpr : E.toDesign2.processes[p]? = some pr)
    (hg : pr.lowerWin E.toDesign2 = some g) :
    (∀ j ∈ winOwn ps p, ∃ q ∈ g, (E.toDesign2.winDesign ps).processes[j]? = some q) ∧
      ∀ q ∈ g, ∃ j ∈ winOwn ps p, (E.toDesign2.winDesign ps).processes[j]? = some q := by
  constructor
  · intro j hj
    obtain ⟨q, hq⟩ := mem_winOwn.mp hj
    obtain ⟨pr', g', hpr', hg', hqg⟩ := (Design2.mem_lowerWin hl).mp (mem_of_getElem?' hq)
    rw [hpr, Option.some.injEq] at hpr'
    subst hpr'
    rw [hg, Option.some.injEq] at hg'
    subst hg'
    exact ⟨q, hqg, by rw [Design2.winDesign_proc, hq]; rfl⟩
  · intro q hq
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp ((Design2.mem_lowerWin hl).mpr ⟨pr, g, hpr, hg, hq⟩)
    exact ⟨j, mem_winOwn.mpr ⟨q, hj⟩, by rw [Design2.winDesign_proc, hj]; rfl⟩

theorem Elab.toDesign2_proc (E : Elab) (p : ProcId) :
    E.toDesign2.processes[p]? = (E.procs[p]?).map Proc0.toProcess2 := by
  simp [Elab.toDesign2]

/-- **The per-window lowering is an equation design for E** (window rank). Hypotheses, all static
and decided on a concrete design: the lowering succeeds; its equation design is in the comb
profile (debt D-X1e: by hand for now); `AllFour E`; sensitivity-completeness of the equations
(`completeWB`); a rank certificate OF THE EQUATIONS, bounded. -/
theorem WSettles.ofLowerWin {E : Elab} {ps : List (Nat × Process2)} {rank : Nat → Nat}
    (hl : E.toDesign2.lowerWin = some ps) (hd : CombDesign (E.toDesign2.winDesign ps))
    (h4 : AllFour E) (hqf : E.qualFreeB = true) (hc : completeWB E ps = true)
    (ha : AcyclicBy (E.toDesign2.winDesign ps) rank)
    (hb : ∀ j, j < ps.length → rank j < ps.length) :
    WSettles E (E.toDesign2.winDesign ps) (winOwn ps) rank := by
  have hsize : (E.toDesign2.winDesign ps).processes.size = ps.length := by
    simp [Design2.winDesign]
  have hdecls : (E.toDesign2.winDesign ps).decls = E.decls := rfl
  refine ⟨hd, hdecls, h4, ?_, ?_, ?_, ?_, ?_, ha, ?_⟩
  · -- disj
    intro p q j hp hq
    obtain ⟨_, h1⟩ := mem_winOwn.mp hp
    obtain ⟨_, h2⟩ := mem_winOwn.mp hq
    rw [h1, Option.some.injEq, Prod.mk.injEq] at h2
    exact h2.1
  · -- cover
    intro j hj
    rw [hsize] at hj
    have hj' : ps[j]? = some ps[j] := List.getElem?_eq_getElem hj
    obtain ⟨pr, g, hpr, -, -⟩ := (Design2.mem_lowerWin hl).mp (mem_of_getElem?' hj')
    refine ⟨ps[j].1, ?_, mem_winOwn.mpr ⟨ps[j].2, by rw [hj']⟩⟩
    have := (Array.getElem?_eq_some_iff.mp hpr).1
    rwa [Elab.size_toDesign2] at this
  · -- act
    intro s p hT hpn
    have hs : StateShape (E.toDesign2.winDesign ps) (E.view s) := Elab.shape_view_of hd hdecls hT
    cases hpp : E.procs[p]? with
    | none => rw [Array.getElem?_eq_getElem hpn] at hpp; cases hpp
    | some pr =>
        have hpr : E.toDesign2.processes[p]? = some pr.toProcess2 := by
          rw [Elab.toDesign2_proc, hpp]; rfl
        obtain ⟨g, hg⟩ := Design2.lowerWin_total hl hpr
        obtain ⟨hown, hcov⟩ := winOwn_spec hl hpr hg
        cases pr with
        | assign t e =>
            simp only [Proc0.toProcess2, Process2.lowerWin, Option.some.injEq] at hg
            subst hg
            have hjs : ∀ j ∈ winOwn ps p,
                (E.toDesign2.winDesign ps).processes[j]? = some (.assign t e) := by
              intro j hj
              obtain ⟨q, hq, hpq⟩ := hown j hj
              rw [List.mem_singleton.mp hq] at hpq
              exact hpq
            obtain ⟨j₀, hj₀, hp₀⟩ := hcov _ (List.mem_singleton_self _)
            obtain ⟨v, hv⟩ := hd.evalPure2_ok hs hp₀
            have hws : t.windows? E.toDesign2 = some (t.wins (E.toDesign2.winDesign ps)) := by
              rw [← hd.windows?_of_proc hp₀]
              exact Lhs2.windows?_congr (d := E.toDesign2.winDesign ps) (d' := E.toDesign2) rfl t
            refine ⟨_, activate_assign hpp hws hv, hT.writeWins _ _, ?_⟩
            rw [Elab.view_writeWins h4 _ _ hT]
            exact WriteRel.ofCombWrite hd hs hv hjs hj₀
        | comb body =>
            obtain ⟨S, hsym, -, rfl⟩ := Process2.lowerWin_alwaysComb hg
            obtain ⟨s', ha', hT', hR⟩ :=
              activate_comb_symRel h4 hpp hsym (Elab.qualFree_of_qualFreeB hqf hpp) hT
            refine ⟨s', ha', hT', WriteRel.ofSymRel hd hR hs (fun j hj => ?_) (fun x hx => ?_)⟩
            · obtain ⟨q, hq, hpq⟩ := hown j hj
              obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hq
              exact ⟨x, hx, hpq⟩
            · exact hcov _ (List.mem_map_of_mem hx)
  · -- complete
    intro q j t e hj hp r hr
    obtain ⟨q', hq'⟩ := mem_winOwn.mp hj
    have hqe : q' = .assign t e := by
      rw [Design2.winDesign_proc, hq'] at hp
      simpa using hp
    subst hqe
    exact complete_of_completeWB hc (mem_of_getElem?' hq') r hr
  · -- group
    intro p j j' t e hj hj' hp r hr wn hW
    obtain ⟨qj, hqj⟩ := mem_winOwn.mp hj
    obtain ⟨qj', hqj'⟩ := mem_winOwn.mp hj'
    obtain ⟨pr, g, hpr, hg, hqg⟩ := (Design2.mem_lowerWin hl).mp (mem_of_getElem?' hqj)
    obtain ⟨pr', g', hpr', hg', hqg'⟩ := (Design2.mem_lowerWin hl).mp (mem_of_getElem?' hqj')
    rw [hpr, Option.some.injEq] at hpr'
    subst hpr'
    rw [hg, Option.some.injEq] at hg'
    subst hg'
    have hqe : qj = .assign t e := by
      rw [Design2.winDesign_proc, hqj] at hp
      simpa using hp
    subst hqe
    obtain ⟨t', e', hp', hwn⟩ := hW
    have hqe' : qj' = .assign t' e' := by
      rw [Design2.winDesign_proc, hqj'] at hp'
      simpa using hp'
    subst hqe'
    cases pr with
    | assign t0 e0 =>
        simp only [Process2.lowerWin, Option.some.injEq] at hg
        subst hg
        rw [List.mem_singleton] at hqg hqg'
        simp only [Process2.assign.injEq] at hqg hqg'
        obtain ⟨rfl, rfl⟩ := hqg
        obtain ⟨rfl, rfl⟩ := hqg'
        exact Bool.eq_false_iff.mpr fun hov => Nat.lt_irrefl (rank j)
          (ha j j _ _ _ _ wn hp hp hwn ⟨r, hr, hov⟩)
    | alwaysComb body =>
        obtain ⟨S, -, hsrf, rfl⟩ := Process2.lowerWin_alwaysComb hg
        obtain ⟨x, hx, hxe⟩ := List.mem_map.mp hqg
        obtain ⟨x', hx', hxe'⟩ := List.mem_map.mp hqg'
        simp only [Process2.assign.injEq] at hxe hxe'
        obtain ⟨rfl, rfl⟩ := hxe
        obtain ⟨rfl, rfl⟩ := hxe'
        rw [Win.lhs_wins, List.mem_singleton] at hwn
        subst hwn
        refine SymState.selfReadFree_iff.mp hsrf r ?_ x'.1 (List.mem_map_of_mem hx')
        rw [SymState.rhs_reads]
        exact Expr2.mem_listReads (List.mem_map_of_mem (f := Prod.snd) hx) hr
    | _ => simp [Process2.lowerWin] at hg
  · -- bound
    intro j hj
    rw [hsize] at hj ⊢
    exact hb j hj

/-! ## Agreement with `combSettle2` on the design itself (fuel-free form) -/

theorem wins_congr_decls {d d' : Design2} (h : d'.decls = d.decls) (t : Lhs2) :
    t.wins d' = t.wins d := by
  simp only [Lhs2.wins, Lhs2.windows?_congr h t]

/-- **Where a window equation comes from** in the process-level lowering (G-B's
`Design2.lowerComb`): the same assign, or one entry of the symbolic state an `always_comb` body
lowers to. -/
theorem winEq_origin {E : Elab} {d' : Design2} {ps : List (Nat × Process2)}
    (hl : E.toDesign2.lowerComb = some d') (hw : E.toDesign2.lowerWin = some ps) {j : Nat}
    {t : Lhs2} {e : Expr2} (hj : (E.toDesign2.winDesign ps).processes[j]? = some (.assign t e)) :
    ∃ p : Nat, d'.processes[p]? = some (.assign t e) ∨
      ∃ (body : Stmt2) (S : SymState) (x : Win × Expr2), body.symExec E.toDesign2 [] = some S ∧
        d'.processes[p]? = some S.toAssign ∧ x ∈ S ∧ t = x.1.lhs ∧ e = x.2 := by
  rw [Design2.winDesign_proc] at hj
  cases hpj : ps[j]? with
  | none => rw [hpj] at hj; cases hj
  | some y =>
      obtain ⟨p, q⟩ := y
      rw [hpj] at hj
      simp only [Option.map_some, Option.some.injEq] at hj
      subst hj
      obtain ⟨pr, g, hpr, hg, hqg⟩ := (Design2.mem_lowerWin hw).mp (mem_of_getElem?' hpj)
      obtain ⟨q', hq', hpq'⟩ := Design2.lowerComb_proc hl hpr
      refine ⟨p, ?_⟩
      cases pr with
      | assign t0 e0 =>
          simp only [Process2.lowerWin, Option.some.injEq] at hg
          subst hg
          simp only [Process2.lowerComb, Option.some.injEq] at hq'
          subst hq'
          rw [List.mem_singleton] at hqg
          rw [← hqg] at hpq'
          exact Or.inl hpq'
      | alwaysComb body =>
          obtain ⟨S, hsym, -, rfl⟩ := Process2.lowerWin_alwaysComb hg
          obtain ⟨S', hsym', -, rfl⟩ := Process2.lowerComb_alwaysComb hq'
          rw [hsym, Option.some.injEq] at hsym'
          subst hsym'
          obtain ⟨x, hx, hxe⟩ := List.mem_map.mp hqg
          simp only [Process2.assign.injEq] at hxe
          exact Or.inr ⟨body, S, x, hsym, hpq', hx, hxe.1.symm, hxe.2.symm⟩
      | _ => simp [Process2.lowerWin] at hg

/-- A window of the per-window lowering is a window of the process-level lowering. -/
theorem win_writes_lower {E : Elab} {d' : Design2} {ps : List (Nat × Process2)}
    (hl : E.toDesign2.lowerComb = some d') (hw : E.toDesign2.lowerWin = some ps) {j : Nat}
    {wn : Win} (h : (E.toDesign2.winDesign ps).Writes j wn) : ∃ p, d'.Writes p wn := by
  have hdecls : d'.decls = (E.toDesign2.winDesign ps).decls := (Design2.lowerComb_spec hl).2.1
  obtain ⟨t, e, hj, hwn⟩ := h
  obtain ⟨p, hA | ⟨body, S, x, -, hp, hx, rfl, rfl⟩⟩ := winEq_origin hl hw hj
  · exact ⟨p, t, e, hA, by rw [wins_congr_decls hdecls t]; exact hwn⟩
  · rw [Win.lhs_wins, List.mem_singleton] at hwn
    subst hwn
    exact ⟨p, _, _, hp, by rw [SymState.target_wins]; exact List.mem_map_of_mem hx⟩

/-- A window of the process-level lowering is a window of the per-window lowering. -/
theorem lower_writes_win {E : Elab} {d' : Design2} {ps : List (Nat × Process2)}
    (hl : E.toDesign2.lowerComb = some d') (hw : E.toDesign2.lowerWin = some ps) {p : Nat}
    {wn : Win} (h : d'.Writes p wn) : ∃ j, (E.toDesign2.winDesign ps).Writes j wn := by
  have hdecls : d'.decls = (E.toDesign2.winDesign ps).decls := (Design2.lowerComb_spec hl).2.1
  obtain ⟨t, e, hp, hwn⟩ := h
  obtain ⟨pr, hpr, hq⟩ := Design2.lowerComb_proc' hl hp
  obtain ⟨g, hg⟩ := Design2.lowerWin_total hw hpr
  have hmem : ∀ q ∈ g, ∃ j, (E.toDesign2.winDesign ps).processes[j]? = some q := fun q hq' => by
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp ((Design2.mem_lowerWin hw).mpr ⟨pr, g, hpr, hg, hq'⟩)
    exact ⟨j, by rw [Design2.winDesign_proc, hj]; rfl⟩
  rcases Process2.lowerComb_eq_some hq with ⟨t0, e0, rfl, h⟩ | ⟨body, S, rfl, hsym, h⟩
  · simp only [Process2.assign.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Process2.lowerWin, Option.some.injEq] at hg
    subst hg
    obtain ⟨j, hj⟩ := hmem _ (List.mem_singleton_self _)
    exact ⟨j, t, e, hj, by rw [← wins_congr_decls hdecls t]; exact hwn⟩
  · simp only [SymState.toAssign, Process2.assign.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [SymState.target_wins] at hwn
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hwn
    obtain ⟨S', hsym', -, rfl⟩ := Process2.lowerWin_alwaysComb hg
    rw [hsym, Option.some.injEq] at hsym'
    subst hsym'
    obtain ⟨j, hj⟩ := hmem _ (List.mem_map_of_mem (f := fun x : Win × Expr2 => Process2.assign x.1.lhs x.2) hx)
    exact ⟨j, _, _, hj, by rw [Win.lhs_wins]; exact List.mem_singleton_self _⟩

/-- **The process-level equations split per window**: a shaped solution of the process-level
lowering's equations solves the per-window equations. -/
theorem combEqs_win_of_lower {E : Elab} {d' : Design2} {ps : List (Nat × Process2)}
    (hl : E.toDesign2.lowerComb = some d') (hd' : CombDesign d') (hw : E.toDesign2.lowerWin = some ps)
    {S : SvState} (hs : StateShape d' S) (he : CombEqs d' S) :
    CombEqs (E.toDesign2.winDesign ps) S := by
  have hdecls : d'.decls = (E.toDesign2.winDesign ps).decls := (Design2.lowerComb_spec hl).2.1
  intro j t e n lo w off hj hm
  obtain ⟨p, hA | ⟨body, S0, ⟨⟨xn, xlo, xw⟩, Ex⟩, hsym, hp, hx, rfl, rfl⟩⟩ := winEq_origin hl hw hj
  · rw [← wins_congr_decls hdecls t] at hm ⊢
    exact he p t e n lo w off hA hm
  · rw [Win.lhs_wins] at hm ⊢
    simp only [Win.placed, Win.sumWidth, List.mem_cons, List.not_mem_nil, or_false,
      Prod.mk.injEq] at hm
    obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := hm
    -- the entries' widths, from a run of the body at `S`
    have hb : ∀ y ∈ E.toDesign2.symNames, ∃ v, SvState.lookup S y = some v := fun y hy =>
      hs.lookup_of_mem (by rw [hdecls]; simpa [Design2.symNames, Design2.winDesign] using hy)
    have hok : SymOk E.toDesign2 S S0 := SymOk.of_shape (Design2.lowerComb_spec hl).2.1 hp hs
    obtain ⟨⟨st'', nba⟩, hrun⟩ := (symExec_total hb body.fuelB).1 body [] S0 S [] hsym hok
      (SymRel.init S) (Nat.le_refl _)
    obtain ⟨-, hR⟩ := (symExec_sound body.fuelB).1 body [] S0 S [] st'' nba hsym hok
      (SymRel.init S) hrun
    have hwidth : ∀ W E', (W, E') ∈ S0 → ∀ v, evalPure2 S E' = .ok v → v.width = W.2.2 := by
      intro W E' hm v hv
      obtain ⟨u, -, hue⟩ := hR.entry W E' hm v hv
      rw [← hue, LVec.width_extract]
    obtain ⟨v, hv⟩ := hd'.evalPure2_ok hs hp
    obtain ⟨vs, hvs, rfl⟩ := SymState.evalPure2_rhs hv
    obtain ⟨hvw, hplace⟩ := SymState.rhs_placed hvs hwidth
    obtain ⟨vx, hvx⟩ := evalPures2_ok_mem hvs _ (List.mem_map_of_mem (f := Prod.snd) hx)
    obtain ⟨off', hoff', hext'⟩ := hplace _ _ hx vx hvx
    obtain ⟨old, v', hlo, hv', hext⟩ := he p _ _ n lo w off' hp
      (by rw [SymState.target_wins]; exact hoff')
    rw [hv, Res.ok.injEq] at hv'
    subst hv'
    rw [SymState.target_wins, LVec.resizeU_of_width hvw] at hext
    have hvxw : vx.width = w := by rw [← hext']; simp
    refine ⟨old, vx, hlo, hvx, ?_⟩
    simp only [Win.sumWidth, Nat.add_zero]
    rw [LVec.resizeU_of_width hvxw, LVec.extract_zero_of_width hvxw]
    exact hext.trans hext'

theorem shape_win_of_lower {E : Elab} {d' : Design2} {ps : List (Nat × Process2)}
    (hl : E.toDesign2.lowerComb = some d') (hw : E.toDesign2.lowerWin = some ps) {S : SvState}
    (hs : StateShape d' S) : StateShape (E.toDesign2.winDesign ps) S := by
  have hdecls : d'.decls = (E.toDesign2.winDesign ps).decls := (Design2.lowerComb_spec hl).2.1
  refine ⟨by rw [hs.keys, hdecls], fun n hn => ?_⟩
  obtain ⟨j, lo, w, hW⟩ := hn
  obtain ⟨p, hW'⟩ := win_writes_lower hl hw hW
  obtain ⟨v, hv, hvw⟩ := hs.driven n ⟨p, lo, w, hW'⟩
  exact ⟨v, hv, by rw [← Design2.declWidth_congr hdecls]; exact hvw⟩

theorem frame_win_of_lower {E : Elab} {d' : Design2} {ps : List (Nat × Process2)}
    (hl : E.toDesign2.lowerComb = some d') (hw : E.toDesign2.lowerWin = some ps) {a b : SvState}
    (hF : Frame d' a b) : Frame (E.toDesign2.winDesign ps) a b :=
  ⟨hF.width, fun x i hu => hF.undriven x i fun ⟨_, wn, hW, hov⟩ => by
    obtain ⟨j, hW'⟩ := lower_writes_win hl hw hW
    exact hu ⟨j, wn, hW', hov⟩⟩

/-- **E's closed store is `combSettle2`'s result on the design itself, window rank** (fuel-free
form; transport). Whenever `combSettle2` on the design (not a lowering) returns from the view of
the slot's start, under any schedule and at any fuel, it returns E's closed view. Route: `CombSim`
carries the settle to the process-level lowering (its equations need no rank), the equations
split per window, and the window equations have one solution (`combEqs_unique` under the window
rank). -/
theorem WSettles.closed_eq_combSettle2 {E : Elab} {d' : Design2} {ps : List (Nat × Process2)}
    {rank : Nat → Nat} (hl : E.toDesign2.lowerComb = some d') (hd' : CombDesign d')
    (hw : E.toDesign2.lowerWin = some ps) (hS : WSettles E (E.toDesign2.winDesign ps) (winOwn ps) rank)
    {ch : Choice} {c c' : Config} (hI : WSettleInv E (E.toDesign2.winDesign ps) (winOwn ps) c)
    (h : SlotCloses E ch c c') {σ : ScheduleOracle} {fuel k : Nat} {S : SvState} {k' : Nat}
    (hS2 : combSettle2 E.toDesign2 σ fuel (E.view c.store) k = .ok (S, k')) :
    E.view c'.store = S := by
  have hdecls' : d'.decls = E.decls := (Design2.lowerComb_spec hl).2.1
  have hs0 : StateShape d' (E.view c.store) := Elab.shape_view_of hd' hdecls' hI.typed
  obtain ⟨hsS, f', hf'⟩ := (CombSim.of_lowerComb hl hd').combSettle2 σ fuel _ k S k' hs0 hS2
  obtain ⟨heq', -, -⟩ := combSettle2_eqs hd' hs0 hf'
  have hF' := combSettle2_frame hd' hs0 hf'
  obtain ⟨he, hs, hf⟩ := hS.slotCloses_combEqs hI h
  exact combEqs_unique hS.comb hS.acyclic hs (shape_win_of_lower hl hw hsS) he
    (combEqs_win_of_lower hl hd' hw hsS heq') (hf.symm.trans (frame_win_of_lower hl hw hF'))

/-! ## The fixture: the ibex_controller shape -/

namespace Core0Smoke

/-- **The ibex_controller shape**: an `always_comb` that writes `a` (from the input `x`) and `c`
(from `b`), beside `assign b = a + 1`. The two processes read each other's windows (a
process-level cycle); the windows form the chain `x → a → b → c`. -/
def ibex : Elab where
  decls := #[{ name := "x", width := 4, isInput := true }, { name := "a", width := 4 },
             { name := "b", width := 4 }, { name := "c", width := 4 }]
  procs := #[.comb (.block #[.blockingAssign (.ident "a") (.ident "x"),
                             .blockingAssign (.ident "c") (.ident "b")]),
             .assign (.ident "b") (.binary .add (.ident "a") (.lit (.ofNat 4 1)))]

/-- The three window equations: `a = x` and `c = b` (from the block), `b = a + 1`. -/
def ibexP0 : Process2 := .assign (.slice "a" 0 4) (.resize 4 (.ident "x"))
def ibexP1 : Process2 := .assign (.slice "c" 0 4) (.resize 4 (.ident "b"))
def ibexP2 : Process2 := .assign (.ident "b") (.binary .add (.ident "a") (.lit (.ofNat 4 1)))

def ibexW : List (Nat × Process2) := [(0, ibexP0), (0, ibexP1), (1, ibexP2)]

/-- The per-window lowering, by `rfl`. -/
theorem ibex_lowerWin : ibex.toDesign2.lowerWin = some ibexW := rfl

/-- The equation design. -/
def ibexEq : Design2 := ibex.toDesign2.winDesign ibexW

theorem ibexEq_proc {i : Nat} {p : Process2} : ibexEq.processes[i]? = some p ↔
    (i = 0 ∧ p = ibexP0) ∨ (i = 1 ∧ p = ibexP1) ∨ (i = 2 ∧ p = ibexP2) := by
  match i with
  | 0 | 1 | 2 => simp [ibexEq, Design2.winDesign, ibexW, eq_comm]
  | i + 3 => simp [ibexEq, Design2.winDesign, ibexW]

theorem ibexEq_writes {i : Nat} {wn : Win} : ibexEq.Writes i wn ↔
    (i = 0 ∧ wn = ("a", 0, 4)) ∨ (i = 1 ∧ wn = ("c", 0, 4)) ∨ (i = 2 ∧ wn = ("b", 0, 4)) := by
  constructor
  · rintro ⟨t, e, hp, hw⟩
    rcases ibexEq_proc.mp hp with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ <;>
      simp only [ibexP0, ibexP1, ibexP2, Process2.assign.injEq] at h <;>
      obtain ⟨rfl, rfl⟩ := h
    · rw [Lhs2.wins_of_window? rfl, List.mem_singleton] at hw; simp [hw]
    · rw [Lhs2.wins_of_window? rfl, List.mem_singleton] at hw; simp [hw]
    · simp [Design2.declWidth, ibexEq, Design2.winDesign, ibex, Elab.toDesign2] at hw; simp [hw]
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨_, _, rfl, by rw [Lhs2.wins_of_window? rfl]; exact List.mem_singleton_self _⟩
    · exact ⟨_, _, rfl, by rw [Lhs2.wins_of_window? rfl]; exact List.mem_singleton_self _⟩
    · exact ⟨_, _, rfl, by simp [Design2.declWidth, ibexEq, Design2.winDesign, ibex, Elab.toDesign2]⟩

theorem ibexEq_driven {n : String} : Driven ibexEq n ↔ n = "a" ∨ n = "c" ∨ n = "b" := by
  constructor
  · rintro ⟨i, lo, w, h⟩
    rcases ibexEq_writes.mp h with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;>
      simp only [Prod.mk.injEq] at h <;> simp [h.1]
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, 0, 4, ibexEq_writes.mpr (by simp)⟩
    · exact ⟨1, 0, 4, ibexEq_writes.mpr (by simp)⟩
    · exact ⟨2, 0, 4, ibexEq_writes.mpr (by simp)⟩

/-- The equation design is in the comb profile. -/
theorem ibexEq_comb : CombDesign ibexEq where
  nodup := by decide
  assign := by
    intro i p hp
    rcases ibexEq_proc.mp hp with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact ⟨_, _, [("a", 0, 4)], rfl, rfl⟩
    · exact ⟨_, _, [("c", 0, 4)], rfl, rfl⟩
    · exact ⟨_, _, [("b", 0, 4)], rfl,
        by simp [Design2.declWidth, ibexEq, Design2.winDesign, ibex, Elab.toDesign2]⟩
  inWidth := by
    intro i n lo w h
    rcases ibexEq_writes.mp h with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;>
      simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl, rfl⟩ := h <;>
      simp [Design2.declWidth, ibexEq, Design2.winDesign, ibex, Elab.toDesign2]
  notInput := by
    intro n hn
    rcases ibexEq_driven.mp hn with rfl | rfl | rfl <;>
      simp [Design2.inputNames, ibexEq, Design2.winDesign, ibex, Elab.toDesign2]
  disjoint := by
    intro i j wi wj hij hi hj
    rcases ibexEq_writes.mp hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases ibexEq_writes.mp hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      first | exact absurd rfl hij | decide
  selfDisjoint := by
    intro i t e hp
    rcases ibexEq_proc.mp hp with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;>
      simp only [ibexP0, ibexP1, ibexP2, Process2.assign.injEq] at h <;>
      obtain ⟨rfl, -⟩ := h <;>
      exact Lhs2.wins_pairwise_of_leaf (fun _ h => by cases h) _
  rhsFree := by
    intro i t e hp
    rcases ibexEq_proc.mp hp with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;>
      simp only [ibexP0, ibexP1, ibexP2, Process2.assign.injEq] at h <;>
      obtain ⟨-, rfl⟩ := h <;> rfl
  rhsDeclared := by
    intro i t e hp
    rcases ibexEq_proc.mp hp with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;>
      simp only [ibexP0, ibexP1, ibexP2, Process2.assign.injEq] at h <;>
      obtain ⟨-, rfl⟩ := h <;> decide
  initWidth := by
    intro n _ dc hdc _ v hv
    simp [ibexEq, Design2.winDesign, ibex, Elab.toDesign2] at hdc
    rcases hdc with rfl | rfl | rfl | rfl <;> cases hv
  inFourState := by
    intro dc hdc _
    simp [ibexEq, Design2.winDesign, ibex, Elab.toDesign2] at hdc
    rcases hdc with rfl | rfl | rfl | rfl <;> rfl

/-- The window rank: `a = x` reads only an input (0), `b = a + 1` reads `a` (1), `c = b` reads
`b` (2). -/
def ibexRank (j : Nat) : Nat := if j = 1 then 2 else if j = 2 then 1 else 0

/-- **The hypotheses hold**: the per-window lowering is an equation design for E. -/
theorem ibex_wsettles : WSettles ibex ibexEq (winOwn ibexW) ibexRank :=
  WSettles.ofLowerWin ibex_lowerWin ibexEq_comb (by unfold AllFour; decide) rfl rfl
    (acyclicBy_of_acyclicB rfl) (by decide)

/-- **R-COMB-1 on the ibex_controller shape** (acceptance): from every typed store with every
process ready, under every legal schedule, the slot closes at a store that solves the window
equations and is their unique shaped solution with the start's undriven bits. -/
theorem ibex_rcomb (ch : Choice) {s : Store} (hT : ibex.Typed s) :
    ∃ c', SlotCloses ibex ch (Config.init ibex s) c' ∧ CombEqs ibexEq (ibex.view c'.store) ∧
      ∀ st, StateShape ibexEq st → CombEqs ibexEq st → Frame ibexEq (ibex.view s) st →
        st = ibex.view c'.store := by
  obtain ⟨c', hcl, he, -, huniq⟩ := ibex_wsettles.rcomb ch (WSettleInv.init hT)
  exact ⟨c', hcl, he, huniq⟩

/-- **Schedule independence on the ibex shape**: any two legal schedules close at the same store. -/
theorem ibex_schedule_independent {s : Store} (hT : ibex.Typed s) {c₁ c₂ : Config}
    {ch₁ ch₂ : Choice} (h₁ : SlotCloses ibex ch₁ (Config.init ibex s) c₁)
    (h₂ : SlotCloses ibex ch₂ (Config.init ibex s) c₂) : ibex.view c₁.store = ibex.view c₂.store :=
  ibex_wsettles.schedule_independent (WSettleInv.init hT) h₁ h₂

/-- The process-level lowering (G-B's `Design2.lowerComb`): `assign {a, c} = {x, b}` beside
`assign b = a + 1`. -/
def ibexS : SymState := [(("a", 0, 4), .resize 4 (.ident "x")), (("c", 0, 4), .resize 4 (.ident "b"))]

def ibexLow : Design2 := { ibex.toDesign2 with processes := #[ibexS.toAssign, ibexP2] }

theorem ibex_lower : ibex.toDesign2.lowerComb = some ibexLow := rfl

/-- **The process rank fails on the ibex shape**: the block reads `b`, which the assign writes,
and the assign reads `a`, which the block writes, so no rank orders the two processes. -/
theorem ibexLow_not_acyclic : ¬ Acyclic ibexLow := by
  rintro ⟨rank, hr⟩
  have h01 : rank 1 < rank 0 := hr 0 1 _ _ _ _ ("b", 0, 4) rfl rfl
    (by simp [Design2.declWidth, ibexLow, ibex, Elab.toDesign2, ibexP2, Lhs2.wins, Lhs2.windows?,
      Lhs2.window?])
    ⟨.whole "b", by simp [ibexS, SymState.rhs_reads, Expr2.listReads, Expr2.reads], rfl⟩
  have h10 : rank 0 < rank 1 := hr 1 0 _ _ _ _ ("a", 0, 4) rfl rfl
    (by rw [SymState.target_wins]; simp [ibexS])
    ⟨.whole "a", by simp [Expr2.reads], rfl⟩
  omega

/-- So G-B's process-rank interface has no instance for it: no `Settles` exists. -/
theorem ibex_no_settles : ¬ ∃ rank, Settles ibex ibexLow rank :=
  fun ⟨_, hS⟩ => ibexLow_not_acyclic hS.acyclic

/-! The executable rows (MEASURED): from `x = 5`, both source and reverse order close at
`a = 5, b = 6, c = 6`, and `combSettle2` on the design itself returns the same values. -/

def ibexStart (x : Nat) : Config := Config.init ibex (ibex.setName ibex.initStore "x" (.ofNat 4 x))

def ibexSettle (σ : ScheduleOracle) : Option (List String) :=
  ((combSettle2 ibex.toDesign2 σ 20 (ibex.view (ibexStart 5).store) 0).toOption).map
    fun (st, _) => ["x", "a", "b", "c"].map (SvState.showSignal st)

#guard showClosed ibex ["x", "a", "b", "c"] (exec ibex σ_src 20 (ibexStart 5))
  == some ["0101", "0101", "0110", "0110"]
#guard showClosed ibex ["x", "a", "b", "c"] (exec ibex σ_rev 20 (ibexStart 5))
  == some ["0101", "0101", "0110", "0110"]
#guard ibexSettle σ_src == some ["0101", "0101", "0110", "0110"]
#guard ibexSettle σ_rev == some ["0101", "0101", "0110", "0110"]

theorem ibexLow_proc {i : Nat} {p : Process2} : ibexLow.processes[i]? = some p ↔
    (i = 0 ∧ p = ibexS.toAssign) ∨ (i = 1 ∧ p = ibexP2) := by
  match i with
  | 0 | 1 => simp [ibexLow, eq_comm]
  | i + 2 => simp [ibexLow]

theorem ibexLow_writes {i : Nat} {wn : Win} : ibexLow.Writes i wn ↔
    (i = 0 ∧ (wn = ("a", 0, 4) ∨ wn = ("c", 0, 4))) ∨ (i = 1 ∧ wn = ("b", 0, 4)) := by
  constructor
  · rintro ⟨t, e, hp, hw⟩
    rcases ibexLow_proc.mp hp with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;>
      simp only [ibexP2, SymState.toAssign, Process2.assign.injEq] at h <;>
      obtain ⟨rfl, rfl⟩ := h
    · rw [SymState.target_wins] at hw
      simp [ibexS] at hw
      simp [hw]
    · simp [Design2.declWidth, ibexLow, ibex, Elab.toDesign2] at hw; simp [hw]
  · rintro (⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨_, _, rfl, by rw [SymState.target_wins]; simp [ibexS]⟩
    · exact ⟨_, _, rfl, by rw [SymState.target_wins]; simp [ibexS]⟩
    · exact ⟨_, _, rfl, by simp [Design2.declWidth, ibexLow, ibex, Elab.toDesign2]⟩

theorem ibexLow_driven {n : String} : Driven ibexLow n ↔ n = "a" ∨ n = "c" ∨ n = "b" := by
  constructor
  · rintro ⟨i, lo, w, h⟩
    rcases ibexLow_writes.mp h with ⟨-, h | h⟩ | ⟨-, h⟩ <;>
      simp only [Prod.mk.injEq] at h <;> simp [h.1]
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, 0, 4, ibexLow_writes.mpr (by simp)⟩
    · exact ⟨0, 0, 4, ibexLow_writes.mpr (by simp)⟩
    · exact ⟨1, 0, 4, ibexLow_writes.mpr (by simp)⟩

/-- The process-level lowering is in the comb profile (its failure is the RANK, not the profile). -/
theorem ibexLow_comb : CombDesign ibexLow where
  nodup := by decide
  assign := by
    intro i p hp
    rcases ibexLow_proc.mp hp with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact ⟨_, _, _, rfl, SymState.target_windows _ _⟩
    · exact ⟨_, _, [("b", 0, 4)], rfl, by simp [Design2.declWidth, ibexLow, ibex, Elab.toDesign2]⟩
  inWidth := by
    intro i n lo w h
    rcases ibexLow_writes.mp h with ⟨-, h | h⟩ | ⟨-, h⟩ <;>
      simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl, rfl⟩ := h <;>
      simp [Design2.declWidth, ibexLow, ibex, Elab.toDesign2]
  notInput := by
    intro n hn
    rcases ibexLow_driven.mp hn with rfl | rfl | rfl <;>
      simp [Design2.inputNames, ibexLow, ibex, Elab.toDesign2]
  disjoint := by
    intro i j wi wj hij hi hj
    rcases ibexLow_writes.mp hi with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases ibexLow_writes.mp hj with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩ <;>
      first | exact absurd rfl hij | decide
  selfDisjoint := by
    intro i t e hp
    rcases ibexLow_proc.mp hp with ⟨-, h⟩ | ⟨-, h⟩ <;>
      simp only [ibexP2, SymState.toAssign, Process2.assign.injEq] at h <;>
      obtain ⟨rfl, -⟩ := h
    · rw [SymState.target_wins]; decide
    · exact Lhs2.wins_pairwise_of_leaf (fun _ h => by cases h) _
  rhsFree := by
    intro i t e hp
    rcases ibexLow_proc.mp hp with ⟨-, h⟩ | ⟨-, h⟩ <;>
      simp only [ibexP2, SymState.toAssign, Process2.assign.injEq] at h <;>
      obtain ⟨-, rfl⟩ := h <;> rfl
  rhsDeclared := by
    intro i t e hp
    rcases ibexLow_proc.mp hp with ⟨-, h⟩ | ⟨-, h⟩ <;>
      simp only [ibexP2, SymState.toAssign, Process2.assign.injEq] at h <;>
      obtain ⟨-, rfl⟩ := h <;> decide
  initWidth := by
    intro n _ dc hdc _ v hv
    simp [ibexLow, ibex, Elab.toDesign2] at hdc
    rcases hdc with rfl | rfl | rfl | rfl <;> cases hv
  inFourState := by
    intro dc hdc _
    simp [ibexLow, ibex, Elab.toDesign2] at hdc
    rcases hdc with rfl | rfl | rfl | rfl <;> rfl

/-- **`combSettle2` on the ibex design returns E's closed store** whenever it completes (any
schedule, any fuel): the fuel-free link, under the window rank. -/
theorem ibex_closed_eq_combSettle2 {ch : Choice} {s : Store} (hT : ibex.Typed s) {c' : Config}
    (h : SlotCloses ibex ch (Config.init ibex s) c') {σ : ScheduleOracle} {fuel k : Nat}
    {S : SvState} {k' : Nat} (hS2 : combSettle2 ibex.toDesign2 σ fuel (ibex.view s) k = .ok (S, k')) :
    ibex.view c'.store = S :=
  WSettles.closed_eq_combSettle2 ibex_lower ibexLow_comb ibex_lowerWin ibex_wsettles
    (WSettleInv.init hT) h hS2

/-- **The process rank, as the special case** (non-vacuity of `Settles.toW`): G-B's fixture is a
window-rank instance with each process owning its own equation. -/
theorem mux1_wsettles : WSettles mux1 mux1Low (fun p => [p]) mux1Rank := mux1_settles.toW

end Core0Smoke

/-! ## Axioms -/

#print axioms WSettles.step_decreases
#print axioms WSettles.rcomb
#print axioms Settles.toW
#print axioms activate_comb_symRel
#print axioms WSettles.ofLowerWin
#print axioms Core0Smoke.ibexEq_comb
#print axioms Core0Smoke.ibex_wsettles
#print axioms Core0Smoke.ibex_rcomb
#print axioms Core0Smoke.ibex_schedule_independent
#print axioms Core0Smoke.ibexLow_not_acyclic
#print axioms Core0Smoke.ibex_no_settles
#print axioms Core0Smoke.mux1_wsettles
#print axioms WSettles.closed_eq_combSettle2
#print axioms Core0Smoke.ibexLow_comb
#print axioms Core0Smoke.ibex_closed_eq_combSettle2

end LeanModels.Sv.Kernel
