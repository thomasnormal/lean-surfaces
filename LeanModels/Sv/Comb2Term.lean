import LeanModels.Sv.Comb2Base

/-!
# Combinational settle terminates under acyclicity (`LeanModels.Sv` — Design2)

The TERMINATION direction of the combinational settle theorem (the
`Comb2Base`/`Comb2Sound`/`Comb2Term`/`Comb2` layer): on a comb design
(`CombDesign`) with an acyclicity certificate (`Acyclic`), `combSettle2`
returns `.ok` from every shaped state, under every schedule, at every fuel
from the explicit bound
`Design2.settleFuel d = d.combFuel + d.processes.size + 1` on. What it
returns is `Comb2Sound.lean`'s question; that it returns at all is this
file's.

## API index

* Main theorems: `combSettle2_terminates` (the headline statement, `∃ F`) and
  `combSettle2_terminates_of_le` (the same at the explicit bound
  `Design2.settleFuel`); their shape-carrying corollaries
  `combSettle2_terminates_shape` / `combSettle2_terminates_shape_of_le` (the
  returned state also has the comb shape — proved here from the settle
  sequence, without `Comb2Sound`).
* The stabilization theorem behind it, schedule- and fuel-free:
  `CombPassSeq` (an abstract run of passes: each order lists every process
  exactly once, each pass a successful `combPass2` at any fuel) and
  `CombPassSeq.stable` — under a rank certificate bounded by `R`, the state
  after `R` passes is a fixpoint (`s p = s R` for `p ≥ R`). Its inductive core
  is `CombPassSeq.combAgreeLow`.
* Rank certificates: `AcyclicBy d rank` (the body of `Acyclic`, with the rank
  named), `Acyclic.exists_rank_lt` (every certificate compresses to one
  bounded by the number of processes — the source of the rank-free bound).
* Rank-level agreement: `CombLowBit` (a bit driven only below rank `r`,
  vacuously true of undriven bits), `CombAgreeLow` (two states share all
  widths and all such bits; `CombAgreeLow.mono` weakens the rank),
  `evalPure2_eq_of_combAgreeLow` (a rank-`r` process cannot tell two such
  states apart).
* The settle as a pass sequence: `combSettleSeq` (states a settle visits,
  pass by pass), `combSettleSeq_shape`, `combSettleSeq_pass`,
  `CombPassSeq.of_combSettleSeq`, and `combSettle2_ok_of_stable` (a settle
  whose pass sequence is stable from pass `p + j` on returns a shaped state,
  given fuel for `j + 1` more passes).
* Pass algebra (namespace `Comb2Term`, general facts that belong next to
  `Comb2Base`'s pass lemmas): `combPass2_append`, `combPass2_det` (a
  successful pass result does not depend on the fuel), `combPass2_mid` (the
  state at which a given process runs inside a pass: per bit equal to the
  pass's start or its end; the process's window in the end state is what it
  wrote there), window/bit overlap facts `overlaps_of_bit`,
  `overlaps_whole_of_bit`, `overlaps_win_of_bit`, `driver_unique`,
  `agree_bit_of_extract`, `lt_of_writes`, and the filter-length facts
  `length_filter_le`/`length_filter_lt` used by rank compression.

## The argument

Let `s p` be the state after `p` passes. Passes run in arbitrary orders
(`σ.choose`), so a process may run before or after the processes it reads;
the induction never looks at the orders beyond "each process runs exactly
once per pass".

* **Every mid-pass state is a bit-wise mix of the pass's endpoints.** When
  process `j` runs inside pass `p`, the state `m` it sees agrees on every bit
  with `s p` (the bit's driver has not run yet in this pass, or the bit is
  undriven) or with `s (p+1)` (its driver has run, and nothing writes the bit
  again — `CombDesign.disjoint` + `Nodup`). And every window of `j` in
  `s (p+1)` holds exactly its slice of what `j` computed at `m`
  (`combPass2_mid`; a concatenated target has several windows, each with its
  `Win.placed` offset, and `CombDesign.selfDisjoint` keeps them apart).
* **Rank induction (`CombPassSeq.combAgreeLow`).** For every `r`, the states
  `s p` with `p ≥ r` all agree on every bit driven only below rank `r`
  (`CombAgreeLow`). `r = 0`: such bits are undriven, and no pass touches them
  (`combPass2_frame`). `r → r + 1`: a bit driven by `j` (rank `≤ r`) holds, in
  `s p` (`p ≥ r + 1`), what `j` wrote during pass `p - 1 ≥ r`, evaluated at a
  mid-pass state; every bit `j` reads is driven below `rank j ≤ r` (the
  certificate), and at mid-pass states of passes `≥ r` those bits are
  those of `s q`, `q ≥ r` — all equal by the induction hypothesis. So `j`
  computes the same value in every pass `≥ r`
  (`evalPure2_eq_of_combAgreeLow`, via `evalPure2_congr_reads`).
* **Fixpoint.** With every rank `< R`, every bit is driven below `R`, so
  `s R = s (R+1)` (`StateShape.eq_of_agree_bits`), and the settle's
  `st' == st` test fires (`LawfulBEq`) at the latest on pass `R`.
* **Rank compression.** Replacing `rank i` by the number of processes of
  strictly lower rank keeps the certificate (strict monotonicity of a
  filter's length) and bounds every rank by the process count, so `R` can be
  taken to be `d.processes.size` whatever certificate was given.
* **Fuel.** `combSettle2` spends one fuel unit per pass and hands the rest
  to the pass as expression fuel; `combPass2` succeeds at any expression fuel
  `≥ d.combFuel` (`combPass2_ok_of_combFuel`) and its result does not depend
  on the fuel (`combPass2_det`). `R + 1` passes at expression fuel
  `≥ d.combFuel` need total fuel `d.combFuel + R + 1`.

## Design laws

* **Fuel never appears in the stabilization theorem.** `CombPassSeq` takes
  each pass at its own existential fuel; fuel enters only in the settle loop
  (`combSettle2_ok_of_stable`) and the main theorems.
* **No known values.** Like `Comb2Base`, everything is 4-state and
  value-agnostic: no `BitVec`, no `Known2`.
* **Prefixed vocabulary.** The helper definitions live in the shared
  `LeanModels.Sv` namespace, so they carry the `comb`/`Comb` prefix
  (`combSettleSeq`, `CombLowBit`, `CombAgreeLow`) instead of generic names.

## Deviations from the original statement

* (2026-10-27, concatenation targets) `AcyclicBy` (like `Acyclic`) quantifies
  over the windows `wj ∈ tj.wins d` of a target, and `combPass2_mid` concludes
  for every placed window of the process (`Comb2Base.lean`, deviations); the
  main theorems keep their statements.
* None in the main theorem's statement. The originally planned bound
  "`R + 2` settle iterations with `R = 1 + max rank`" is replaced by `R + 1`
  iterations with `R = d.processes.size` (after rank compression), giving
  the explicit, certificate-independent `Design2.settleFuel`.

The smoke section at the end instantiates the theorem at `Comb2Base`'s
hand-built full adder (`Comb2Smoke.faDesign`).
-/

namespace LeanModels.Sv

/-! ## Pass algebra -/

namespace Comb2Term

/-- A pass over a concatenated order is the two passes in sequence. -/
theorem combPass2_append (d : Design2) (fuel : Nat) :
    ∀ (st : SvState) (l₁ l₂ : List Nat),
      combPass2 d fuel st (l₁ ++ l₂) =
        (combPass2 d fuel st l₁ >>= fun m => combPass2 d fuel m l₂)
  | _, [], _ => rfl
  | st, i :: l₁, l₂ => by
      cases hpi : d.processes[i]? with
      | none =>
          rw [List.cons_append, combPass2_cons_none hpi, combPass2_cons_none hpi]
          exact combPass2_append d fuel st l₁ l₂
      | some p =>
          rw [List.cons_append, combPass2_cons_some hpi, combPass2_cons_some hpi]
          cases runCombProcess2 fuel st p with
          | ok m => simp only [Res.ok_bind]; exact combPass2_append d fuel m l₁ l₂
          | timeout => rfl
          | unsupported msg => rfl

/-- **A pass's result does not depend on the fuel**: two successful passes
from the same shaped state over the same order (at any two fuels) agree. -/
theorem combPass2_det {d : Design2} (hd : CombDesign d) {f f' : Nat} :
    ∀ {is : List Nat} {st x y : SvState}, StateShape d st →
      combPass2 d f st is = .ok x → combPass2 d f' st is = .ok y → x = y
  | [], _, _, _, _, hx, hy => by cases hx; cases hy; rfl
  | _ :: _, _, _, _, hs, hx, hy => by
      rcases combPass2_cons_ok hd hs hx with ⟨hn, hx⟩ | ⟨t, e, v, hp, hv, hx⟩ <;>
      rcases combPass2_cons_ok hd hs hy with ⟨hn', hy⟩ | ⟨t', e', v', hp', hv', hy⟩
      · exact combPass2_det hd hs hx hy
      · rw [hn] at hp'; cases hp'
      · rw [hn'] at hp; cases hp
      · rw [hp] at hp'; cases hp'
        rw [hv] at hv'; cases hv'
        exact combPass2_det hd (hs.combWrite t v) hx hy

/-- Two windows that both contain one bit overlap. -/
theorem overlaps_of_bit {n : String} {b : Nat} {w₁ w₂ : Win}
    (h₁ : (ReadWin.win n b 1).overlaps w₁ = true) (h₂ : (ReadWin.win n b 1).overlaps w₂ = true) :
    Win.overlaps w₁ w₂ = true := by
  obtain ⟨m₁, lo₁, v₁⟩ := w₁
  obtain ⟨m₂, lo₂, v₂⟩ := w₂
  rw [ReadWin.overlaps_win_one] at h₁ h₂
  rw [Win.overlaps_eq_true]
  obtain ⟨rfl, _, _⟩ := h₁
  obtain ⟨rfl, _, _⟩ := h₂
  exact ⟨rfl, by omega, by omega⟩

/-- The whole signal overlaps every window that one of its 1-bit reads
overlaps. -/
theorem overlaps_whole_of_bit {n : String} {b : Nat} {wn : Win}
    (h : (ReadWin.win n b 1).overlaps wn = true) : (ReadWin.whole n).overlaps wn = true := by
  obtain ⟨m, lo, w⟩ := wn
  rw [ReadWin.overlaps_win_one] at h
  obtain ⟨rfl, _, _⟩ := h
  simp [ReadWin.overlaps]

/-- A bit of a window read that overlaps a write window makes the window read
overlap it. -/
theorem overlaps_win_of_bit {n : String} {lo w k : Nat} {wn : Win} (hk : k < w)
    (h : (ReadWin.win n (lo + k) 1).overlaps wn = true) :
    (ReadWin.win n lo w).overlaps wn = true := by
  obtain ⟨m, lo', w'⟩ := wn
  rw [ReadWin.overlaps_win_one] at h
  obtain ⟨rfl, _, _⟩ := h
  simp only [ReadWin.overlaps, Win.overlaps_eq_true, true_and]
  exact ⟨by omega, by omega⟩

/-- **One driver per bit**: two processes whose windows contain the same bit
are the same process. -/
theorem driver_unique {d : Design2} (hd : CombDesign d) {n : String} {b j k : Nat}
    {wj wk : Win} (hj : d.Writes j wj) (hk : d.Writes k wk)
    (h₁ : (ReadWin.win n b 1).overlaps wj = true) (h₂ : (ReadWin.win n b 1).overlaps wk = true) :
    j = k := by
  refine Classical.byContradiction fun hne => ?_
  have := hd.disjoint j k wj wk hne hj hk
  rw [overlaps_of_bit h₁ h₂] at this
  cases this

/-- Bit agreement from equal windows: a bit inside a window on which two
bindings of equal width agree. -/
theorem agree_bit_of_extract {st st' : SvState} {n : String} {lo w b : Nat} {u u' : LVec}
    (hu : SvState.lookup st n = some u) (hu' : SvState.lookup st' n = some u')
    (hw : u.width = u'.width) (he : u.extract lo w = u'.extract lo w)
    (hb₁ : lo ≤ b) (hb₂ : b < lo + w) : (ReadWin.win n b 1).agree st st' := by
  apply ReadWin.agree_win_of_lookup hu hu' hw
  have h₁ := LVec.extract_extract u (lo := lo) (w := w) (lo' := b - lo) (w' := 1) (by omega)
  have h₂ := LVec.extract_extract u' (lo := lo) (w := w) (lo' := b - lo) (w' := 1) (by omega)
  rw [Nat.add_sub_cancel' hb₁] at h₁ h₂
  rw [← h₁, ← h₂, he]

/-- A process index with a write window is in range. -/
theorem lt_of_writes {d : Design2} {j : Nat} {wn : Win} (h : d.Writes j wn) :
    j < d.processes.size := by
  obtain ⟨t, e, hp, -⟩ := h
  exact (Array.getElem?_eq_some_iff.mp hp).1

/-- **The state a process sees inside a pass.** In a successful pass over a
duplicate-free order from a shaped state `st` to `st'`, the process `j` (an
assign `t := e`, listed in the order) runs at a shaped state `m` with the
widths of `st`, which agrees on EVERY bit with `st` or with `st'`; and every
placed window of `t` holds, in `st'`, its slice of the value `j` computed at
`m` (resized to the target's total width). -/
theorem combPass2_mid {d : Design2} (hd : CombDesign d) {f : Nat} {is : List Nat}
    {st st' : SvState} (hs : StateShape d st) (hnd : is.Nodup)
    (h : combPass2 d f st is = .ok st') {j : Nat} (hj : j ∈ is) {t : Lhs2} {e : Expr2}
    (hp : d.processes[j]? = some (.assign t e)) :
    ∃ m v, StateShape d m ∧
      (∀ x, (SvState.lookup m x).map LVec.width = (SvState.lookup st x).map LVec.width) ∧
      (∀ x b, (ReadWin.win x b 1).agree m st ∨ (ReadWin.win x b 1).agree m st') ∧
      evalPure2 m e = .ok v ∧
      ∀ (n : String) (lo w off : Nat), ((n, lo, w), off) ∈ Win.placed (t.wins d) →
        ∃ u, SvState.lookup st' n = some u ∧
          u.extract lo w = (v.resizeU (Win.sumWidth (t.wins d))).extract off w := by
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hj
  rw [combPass2_append] at h
  obtain ⟨m, hm, hrest⟩ := Res.bind_eq_ok.mp h
  obtain ⟨hsm, hfpre⟩ := combPass2_frame hd hs hm
  obtain ⟨-, hnd₂, hdisj⟩ := List.nodup_append.mp hnd
  have hjpost : j ∉ post := (List.nodup_cons.mp hnd₂).1
  have hfrest := (combPass2_frame hd hsm hrest).2
  rcases combPass2_cons_ok hd hsm hrest with ⟨hn, -⟩ | ⟨t', e', v, hp', hv, hpost⟩
  · rw [hp] at hn; cases hn
  rw [hp] at hp'; cases hp'
  have hfpost := (combPass2_frame hd (hsm.combWrite t v) hpost).2
  refine ⟨m, v, hsm, fun x => (combPass2_width hd hs hm x).symm, fun x b => ?_, hv, ?_⟩
  · -- per bit: the bit's driver (if any) has run before `m` or not
    by_cases hdrv : ∃ k wk, d.Writes k wk ∧ (ReadWin.win x b 1).overlaps wk = true
    · obtain ⟨k, wk, hWk, hov⟩ := hdrv
      by_cases hk : k ∈ pre
      · right
        refine hfrest _ fun i hi wn hWn => Bool.eq_false_iff.mpr fun hov' => ?_
        have hik := driver_unique hd hWn hWk hov' hov
        exact hdisj k hk i hi hik.symm
      · left
        refine ReadWin.agree_symm
          (hfpre _ fun i hi wn hWn => Bool.eq_false_iff.mpr fun hov' => ?_)
        have hik := driver_unique hd hWn hWk hov' hov
        exact hk (hik ▸ hi)
    · left
      refine ReadWin.agree_symm (hfpre _ fun i _ wn hWn => Bool.eq_false_iff.mpr fun hov => ?_)
      exact hdrv ⟨i, wn, hWn, hov⟩
  · -- each window of `j`: written at `m`, then untouched through `post`
    intro n lo w off hmem
    obtain ⟨u0, hu0, hue0⟩ := hd.combWrite_readBack hsm hp v hmem
    have hW : d.Writes j (n, lo, w) := ⟨t, e, hp, Win.mem_of_mem_placed hmem⟩
    have hwin := hfpost (.win n lo w) fun k hk wn hWn => by
      have hkj : j ≠ k := fun h => hjpost (h ▸ hk)
      exact hd.disjoint j k _ wn hkj hW hWn
    simp only [ReadWin.agree, hu0, Option.map_some] at hwin
    cases hu : SvState.lookup st' n with
    | none => rw [hu] at hwin; cases hwin
    | some u =>
        rw [hu] at hwin
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hwin
        exact ⟨u, rfl, hwin.2.symm.trans hue0⟩

/-- Filtering by a weaker predicate keeps at least as many elements. -/
theorem length_filter_le {α : Type} {p q : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, p x = true → q x = true) →
      (l.filter p).length ≤ (l.filter q).length
  | [], _ => Nat.le_refl _
  | a :: l, h => by
      have ih := length_filter_le (l := l) fun y hy => h y (List.mem_cons_of_mem _ hy)
      by_cases hpa : p a = true
      · simp [hpa, h a (List.mem_cons_self ..) hpa]; omega
      · by_cases hqa : q a = true <;> simp [hpa, hqa] <;> omega

/-- Filtering by a weaker predicate that admits one more element keeps
strictly more elements. -/
theorem length_filter_lt {α : Type} {p q : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, p x = true → q x = true) →
      (∃ x ∈ l, q x = true ∧ p x = false) → (l.filter p).length < (l.filter q).length
  | [], _, ⟨_, hx, _⟩ => absurd hx List.not_mem_nil
  | a :: l, h, ⟨x, hx, hqx, hpx⟩ => by
      have hle := length_filter_le (l := l) fun y hy => h y (List.mem_cons_of_mem _ hy)
      rcases List.mem_cons.mp hx with rfl | hx
      · simp [hqx, hpx]; omega
      · have ih := length_filter_lt (l := l) (fun y hy => h y (List.mem_cons_of_mem _ hy))
          ⟨x, hx, hqx, hpx⟩
        by_cases hpa : p a = true
        · simp [hpa, h a (List.mem_cons_self ..) hpa]; omega
        · by_cases hqa : q a = true <;> simp [hpa, hqa] <;> omega

end Comb2Term

open Comb2Term

/-! ## Rank certificates -/

/-- The body of `Acyclic` with the rank named: every process reads only
windows written by strictly lower-ranked processes. `Acyclic d` is
definitionally `∃ rank, AcyclicBy d rank`. -/
def AcyclicBy (d : Design2) (rank : Nat → Nat) : Prop :=
  ∀ (i j : Nat) (ti : Lhs2) (ei : Expr2) (tj : Lhs2) (ej : Expr2) (wj : Win),
    d.processes[i]? = some (.assign ti ei) →
    d.processes[j]? = some (.assign tj ej) → wj ∈ tj.wins d →
    (∃ r ∈ ei.reads, r.overlaps wj = true) → rank j < rank i

/-- `Acyclic` is a named rank certificate. -/
theorem acyclic_iff_exists_acyclicBy {d : Design2} : Acyclic d ↔ ∃ rank, AcyclicBy d rank :=
  Iff.rfl

/-- **Rank compression.** Every acyclicity certificate can be replaced by one
whose ranks on process indices are below the number of processes: rank `i`
becomes the number of processes of strictly lower rank. -/
theorem Acyclic.exists_rank_lt {d : Design2} (ha : Acyclic d) :
    ∃ rank, AcyclicBy d rank ∧ ∀ i, i < d.processes.size → rank i < d.processes.size := by
  obtain ⟨rank, hr⟩ := ha
  refine ⟨fun i => ((List.range d.processes.size).filter fun j => decide (rank j < rank i)).length,
    ?_, ?_⟩
  · intro i j ti ei tj ej wj hi hj hwj hov
    have hlt := hr i j ti ei tj ej wj hi hj hwj hov
    have hjn : j < d.processes.size := (Array.getElem?_eq_some_iff.mp hj).1
    refine length_filter_lt (fun x _ hx => ?_) ⟨j, List.mem_range.mpr hjn, ?_, ?_⟩
    · simp only [decide_eq_true_eq] at hx ⊢; omega
    · simpa using hlt
    · simp
  · intro i hi
    calc _ < (List.range d.processes.size).length :=
          List.length_filter_lt_length_iff_exists.mpr ⟨i, List.mem_range.mpr hi, by simp⟩
      _ = d.processes.size := List.length_range ..

/-! ## Rank-level agreement -/

/-- Bit `b` of `n` is driven, if at all, only by processes of rank below `r`
(vacuously true of an undriven bit). -/
def CombLowBit (d : Design2) (rank : Nat → Nat) (r : Nat) (n : String) (b : Nat) : Prop :=
  ∀ j wn, d.Writes j wn → (ReadWin.win n b 1).overlaps wn = true → rank j < r

/-- Two states agree on every width and on every bit driven only below
rank `r`. -/
def CombAgreeLow (d : Design2) (rank : Nat → Nat) (r : Nat) (s s' : SvState) : Prop :=
  (∀ x, (SvState.lookup s x).map LVec.width = (SvState.lookup s' x).map LVec.width) ∧
  ∀ x b, CombLowBit d rank r x b → (ReadWin.win x b 1).agree s s'

/-- Agreement below rank `r` weakens to any lower rank. -/
theorem CombAgreeLow.mono {d : Design2} {rank : Nat → Nat} {r r' : Nat} {s s' : SvState}
    (h : CombAgreeLow d rank r s s') (hle : r' ≤ r) : CombAgreeLow d rank r' s s' :=
  ⟨h.1, fun x b hlow => h.2 x b fun j wn hW hov => Nat.lt_of_lt_of_le (hlow j wn hW hov) hle⟩

/-- **A process of rank `r` cannot tell apart two states that agree below
rank `r`**: its right-hand side reads only bits driven below its rank (the
certificate) or undriven bits. -/
theorem evalPure2_eq_of_combAgreeLow {d : Design2} {rank : Nat → Nat}
    (hr : AcyclicBy d rank) {i : Nat} {t : Lhs2} {e : Expr2}
    (hp : d.processes[i]? = some (.assign t e)) {s s' : SvState}
    (h : CombAgreeLow d rank (rank i) s s') : evalPure2 s e = evalPure2 s' e := by
  apply evalPure2_congr_reads
  intro rd hrd
  cases rd with
  | whole x =>
      show SvState.lookup s x = SvState.lookup s' x
      refine ReadWin.lookup_eq_of_agree_bits fun b => h.2 x b fun j wn hWj hov => ?_
      obtain ⟨tj, ej, hpj, hwj⟩ := hWj
      exact hr i j t e tj ej wn hp hpj hwj ⟨.whole x, hrd, overlaps_whole_of_bit hov⟩
  | win x lo w =>
      refine ReadWin.agree_win_of_bits (h.1 x) fun k hk => h.2 x (lo + k) fun j wn hWj hov => ?_
      obtain ⟨tj, ej, hpj, hwj⟩ := hWj
      exact hr i j t e tj ej wn hp hpj hwj ⟨.win x lo w, hrd, overlaps_win_of_bit hk hov⟩

/-! ## Abstract pass sequences and the stabilization theorem -/

/-- An abstract run of comb passes: states `s p` (the state after `p` passes)
and pass orders `os p`, each order listing every process exactly once, each
pass a successful `combPass2` at some fuel. The settle's own pass sequence is
one (`CombPassSeq.of_combSettleSeq`). -/
structure CombPassSeq (d : Design2) (s : Nat → SvState) (os : Nat → List Nat) : Prop where
  /-- The run starts from a shaped state. -/
  shape0 : StateShape d (s 0)
  /-- No order lists a process twice. -/
  nodup : ∀ p, (os p).Nodup
  /-- Every order lists every process. -/
  mem : ∀ p i, i < d.processes.size → i ∈ os p
  /-- Pass `p` maps `s p` to `s (p + 1)`. -/
  pass : ∀ p, ∃ f, combPass2 d f (s p) (os p) = .ok (s (p + 1))

namespace CombPassSeq

variable {d : Design2} {s : Nat → SvState} {os : Nat → List Nat}

/-- Every state of the run is shaped. -/
theorem shape (hd : CombDesign d) (hq : CombPassSeq d s os) : ∀ p, StateShape d (s p)
  | 0 => hq.shape0
  | p + 1 => by
      obtain ⟨f, hf⟩ := hq.pass p
      exact (combPass2_frame hd (hq.shape hd p) hf).1

/-- Widths never change along the run. -/
theorem width (hd : CombDesign d) (hq : CombPassSeq d s os) :
    ∀ p x, (SvState.lookup (s p) x).map LVec.width = (SvState.lookup (s 0) x).map LVec.width
  | 0, _ => rfl
  | p + 1, x => by
      obtain ⟨f, hf⟩ := hq.pass p
      rw [← combPass2_width hd (hq.shape hd p) hf x, hq.width hd p x]

/-- An undriven bit never changes along the run. -/
theorem undriven (hd : CombDesign d) (hq : CombPassSeq d s os) {x : String} {b : Nat}
    (hn : ¬∃ j wn, d.Writes j wn ∧ (ReadWin.win x b 1).overlaps wn = true) :
    ∀ p, (ReadWin.win x b 1).agree (s 0) (s p)
  | 0 => ReadWin.agree_refl _ _
  | p + 1 => by
      obtain ⟨f, hf⟩ := hq.pass p
      refine ReadWin.agree_trans (hq.undriven hd hn p)
        ((combPass2_frame hd (hq.shape hd p) hf).2 _ fun i _ wn hWn =>
          Bool.eq_false_iff.mpr fun hov => hn ⟨i, wn, hWn, hov⟩)

/-- **The inductive core.** All states after at least `r` passes agree on
every width and on every bit driven only below rank `r`. -/
theorem combAgreeLow (hd : CombDesign d) {rank : Nat → Nat} (hr : AcyclicBy d rank)
    (hq : CombPassSeq d s os) :
    ∀ r p p', r ≤ p → r ≤ p' → CombAgreeLow d rank r (s p) (s p') := by
  have hwid : ∀ p p' x, (SvState.lookup (s p) x).map LVec.width =
      (SvState.lookup (s p') x).map LVec.width := fun p p' x =>
    (hq.width hd p x).trans (hq.width hd p' x).symm
  intro r
  induction r with
  | zero =>
      intro p p' _ _
      refine ⟨hwid p p', fun x b hlow => ?_⟩
      have hn : ¬∃ j wn, d.Writes j wn ∧ (ReadWin.win x b 1).overlaps wn = true :=
        fun ⟨j, wn, hW, hov⟩ => Nat.not_lt_zero _ (hlow j wn hW hov)
      exact ReadWin.agree_trans (ReadWin.agree_symm (hq.undriven hd hn p)) (hq.undriven hd hn p')
  | succ r ih =>
      intro p p' hp hp'
      refine ⟨hwid p p', fun x b hlow => ?_⟩
      by_cases hdrv : ∃ j wn, d.Writes j wn ∧ (ReadWin.win x b 1).overlaps wn = true
      · obtain ⟨j, ⟨nj, loj, wj⟩, hWj, hov⟩ := hdrv
        have hrj : rank j < r + 1 := hlow j _ hWj hov
        obtain ⟨tj, ej, hpj, hwj⟩ := hWj
        have hjn : j < d.processes.size := (Array.getElem?_eq_some_iff.mp hpj).1
        obtain ⟨offj, hoff⟩ := Win.exists_mem_placed hwj
        rw [ReadWin.overlaps_win_one] at hov
        obtain ⟨rfl, hb₁, hb₂⟩ := hov
        obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
        obtain ⟨q', rfl⟩ : ∃ q', p' = q' + 1 := ⟨p' - 1, by omega⟩
        obtain ⟨f, hf⟩ := hq.pass q
        obtain ⟨f', hf'⟩ := hq.pass q'
        obtain ⟨m, v, -, hmw, hmb, hv, hU⟩ :=
          combPass2_mid hd (hq.shape hd q) (hq.nodup q) hf (hq.mem q j hjn) hpj
        obtain ⟨u, hu, hue⟩ := hU _ _ _ _ hoff
        obtain ⟨m', v', -, hmw', hmb', hv', hU'⟩ :=
          combPass2_mid hd (hq.shape hd q') (hq.nodup q') hf' (hq.mem q' j hjn) hpj
        obtain ⟨u', hu', hue'⟩ := hU' _ _ _ _ hoff
        -- the two mid-pass states agree below `rank j`
        have hmm : CombAgreeLow d rank (rank j) m m' := by
          refine ⟨fun y => (hmw y).trans ((hwid q q' y).trans (hmw' y).symm), fun y c hlow' => ?_⟩
          have hlowr : CombLowBit d rank r y c := fun i wn hW hov =>
            Nat.lt_of_lt_of_le (hlow' i wn hW hov) (Nat.le_of_lt_succ hrj)
          have hsame : ∀ a a', r ≤ a → r ≤ a' → (ReadWin.win y c 1).agree (s a) (s a') :=
            fun a a' ha ha' => (ih a a' ha ha').2 y c hlowr
          have hq₁ : r ≤ q := by omega
          have hq₂ : r ≤ q' := by omega
          rcases hmb y c with h₁ | h₁ <;> rcases hmb' y c with h₂ | h₂
          · exact ReadWin.agree_trans h₁
              (ReadWin.agree_trans (hsame q q' hq₁ hq₂) (ReadWin.agree_symm h₂))
          · exact ReadWin.agree_trans h₁
              (ReadWin.agree_trans (hsame q (q' + 1) hq₁ (by omega)) (ReadWin.agree_symm h₂))
          · exact ReadWin.agree_trans h₁
              (ReadWin.agree_trans (hsame (q + 1) q' (by omega) hq₂) (ReadWin.agree_symm h₂))
          · exact ReadWin.agree_trans h₁
              (ReadWin.agree_trans (hsame (q + 1) (q' + 1) (by omega) (by omega))
                (ReadWin.agree_symm h₂))
        have hvv : v = v' := by
          have := evalPure2_eq_of_combAgreeLow hr hpj hmm
          rw [hv, hv'] at this
          cases this; rfl
        subst hvv
        have huw : u.width = u'.width := by
          have := hwid (q + 1) (q' + 1) x
          rw [hu, hu'] at this
          simpa using this
        exact agree_bit_of_extract hu hu' huw (hue.trans hue'.symm) hb₁ hb₂
      · exact ReadWin.agree_trans (ReadWin.agree_symm (hq.undriven hd hdrv p))
          (hq.undriven hd hdrv p')

/-- **Stabilization.** Under a rank certificate bounded by `R` on the process
indices, the run is constant from pass `R` on. -/
theorem stable (hd : CombDesign d) {rank : Nat → Nat} (hr : AcyclicBy d rank) {R : Nat}
    (hR : ∀ i, i < d.processes.size → rank i < R) (hq : CombPassSeq d s os) :
    ∀ p, R ≤ p → s p = s R := by
  intro p hp
  refine StateShape.eq_of_agree_bits hd (hq.shape hd p) (hq.shape hd R) fun x b => ?_
  exact (hq.combAgreeLow hd hr R p R hp (Nat.le_refl R)).2 x b fun j _ hW _ =>
    hR j (lt_of_writes hW)

end CombPassSeq

/-! ## The settle as a pass sequence -/

/-- The states a settle from `st` (schedule counter `k`) visits, pass by
pass: pass `p` runs the order `σ.choose (k + p) d.combIndices` at expression
fuel `d.combFuel` (enough, and the result does not depend on it:
`Comb2Term.combPass2_det`). -/
def combSettleSeq (d : Design2) (σ : ScheduleOracle) (k : Nat) (st : SvState) :
    Nat → SvState
  | 0 => st
  | p + 1 =>
      match combPass2 d d.combFuel (combSettleSeq d σ k st p)
          (σ.choose (k + p) d.combIndices) with
      | .ok s => s
      | _ => combSettleSeq d σ k st p

private theorem combSettleSeq_succ_of_ok {d : Design2} {σ : ScheduleOracle} {k : Nat}
    {st : SvState} {p : Nat} {x : SvState}
    (h : combPass2 d d.combFuel (combSettleSeq d σ k st p)
      (σ.choose (k + p) d.combIndices) = .ok x) :
    combSettleSeq d σ k st (p + 1) = x := by
  simp only [combSettleSeq, h]

/-- The settle sequence of a shaped state is shaped, and each of its steps is
a successful pass. -/
theorem combSettleSeq_spec {d : Design2} (hd : CombDesign d) (σ : ScheduleOracle) (k : Nat)
    {st : SvState} (hs : StateShape d st) :
    ∀ p, StateShape d (combSettleSeq d σ k st p) ∧
      combPass2 d d.combFuel (combSettleSeq d σ k st p) (σ.choose (k + p) d.combIndices) =
        .ok (combSettleSeq d σ k st (p + 1))
  | p => by
      have hsp : StateShape d (combSettleSeq d σ k st p) := by
        cases p with
        | zero => exact hs
        | succ p =>
            obtain ⟨hs', hpass⟩ := combSettleSeq_spec hd σ k hs p
            exact (combPass2_frame hd hs' hpass).1
      obtain ⟨x, hx⟩ := combPass2_ok_of_combFuel hd (Nat.le_refl _)
        (σ.choose (k + p) d.combIndices) hsp
      exact ⟨hsp, by rw [combSettleSeq_succ_of_ok hx]; exact hx⟩

/-- Every state of the settle sequence is shaped. -/
theorem combSettleSeq_shape {d : Design2} (hd : CombDesign d) (σ : ScheduleOracle) (k : Nat)
    {st : SvState} (hs : StateShape d st) (p : Nat) :
    StateShape d (combSettleSeq d σ k st p) :=
  (combSettleSeq_spec hd σ k hs p).1

/-- Pass `p` of a settle (at ANY fuel at which it succeeds) produces the next
state of the settle sequence. -/
theorem combSettleSeq_pass {d : Design2} (hd : CombDesign d) (σ : ScheduleOracle) (k : Nat)
    {st : SvState} (hs : StateShape d st) {p f : Nat} {x : SvState}
    (h : combPass2 d f (combSettleSeq d σ k st p) (σ.choose (k + p) d.combIndices) = .ok x) :
    x = combSettleSeq d σ k st (p + 1) :=
  combPass2_det hd (combSettleSeq_shape hd σ k hs p) h (combSettleSeq_spec hd σ k hs p).2

/-- The settle sequence is an abstract pass sequence. -/
theorem CombPassSeq.of_combSettleSeq {d : Design2} (hd : CombDesign d) (σ : ScheduleOracle)
    (k : Nat) {st : SvState} (hs : StateShape d st) :
    CombPassSeq d (combSettleSeq d σ k st) (fun p => σ.choose (k + p) d.combIndices) where
  shape0 := hs
  nodup p := hd.nodup_choose σ (k + p)
  mem p i hi := (hd.mem_choose σ (k + p) i).mpr hi
  pass p := ⟨d.combFuel, (combSettleSeq_spec hd σ k hs p).2⟩

/-- **The settle loop.** If the settle sequence is stable at pass `p + j`
(`s (p+j) = s (p+j+1)`), a settle entered at pass `p` with fuel for `j + 1`
more passes above `d.combFuel` returns — a state of the settle sequence, so
a shaped one (`combSettleSeq_shape`). -/
theorem combSettle2_ok_of_stable {d : Design2} (hd : CombDesign d) {σ : ScheduleOracle}
    {k : Nat} {st : SvState} (hs : StateShape d st) :
    ∀ (j p fuel : Nat),
      combSettleSeq d σ k st (p + j) = combSettleSeq d σ k st (p + j + 1) →
      d.combFuel + j + 1 ≤ fuel →
      ∃ S k', combSettle2 d σ fuel (combSettleSeq d σ k st p) (k + p) = .ok (S, k') ∧
        StateShape d S
  | _, _, 0, _, hf => absurd hf (by omega)
  | j, p, f + 1, hstab, hf => by
      obtain ⟨x, hx⟩ := combPass2_ok_of_combFuel hd (by omega : d.combFuel ≤ f)
        (σ.choose (k + p) d.combIndices) (combSettleSeq_shape hd σ k hs p)
      have hxe := combSettleSeq_pass hd σ k hs hx
      subst hxe
      simp only [combSettle2, hx, Res.ok_bind]
      by_cases heq : (combSettleSeq d σ k st (p + 1) == combSettleSeq d σ k st p) = true
      · rw [if_pos heq]
        exact ⟨combSettleSeq d σ k st (p + 1), _, rfl, combSettleSeq_shape hd σ k hs (p + 1)⟩
      · rw [if_neg heq]
        cases j with
        | zero =>
            exfalso; apply heq
            rw [Nat.add_zero] at hstab
            rw [← hstab]
            exact beq_self_eq_true _
        | succ j =>
            have h := combSettle2_ok_of_stable hd hs j (p + 1) f
              (by rw [show p + 1 + j = p + (j + 1) by omega]; exact hstab) (by omega)
            rwa [show k + (p + 1) = k + p + 1 by omega] at h

/-! ## Termination -/

/-- **Explicit settle fuel** of a comb design: expression fuel for every
right-hand side (`Design2.combFuel`) plus one settle iteration per process
plus the final, confirming pass. -/
def Design2.settleFuel (d : Design2) : Nat := d.combFuel + d.processes.size + 1

/-- **Settle terminates in a shaped state, explicit bound.** On a comb design
with an acyclicity certificate, `combSettle2` returns `.ok` from every shaped
state, under every schedule, at every fuel from `Design2.settleFuel d` on, and
the returned state has the comb shape (it is a state of the settle sequence). -/
theorem combSettle2_terminates_shape_of_le {d : Design2} (hd : CombDesign d)
    (ha : Acyclic d) {fuel : Nat} (hf : d.settleFuel ≤ fuel) (σ : ScheduleOracle)
    (st : SvState) (k : Nat) (hs : StateShape d st) :
    ∃ S k', combSettle2 d σ fuel st k = .ok (S, k') ∧ StateShape d S := by
  obtain ⟨rank, hr, hlt⟩ := ha.exists_rank_lt
  have hstab := (CombPassSeq.of_combSettleSeq hd σ k hs).stable hd hr hlt
    (d.processes.size + 1) (Nat.le_succ _)
  have h := combSettle2_ok_of_stable hd hs d.processes.size 0 fuel
    (by rw [Nat.zero_add, hstab]) (by unfold Design2.settleFuel at hf; omega)
  simpa [combSettleSeq] using h

/-- **Settle terminates, explicit bound.** On a comb design with an
acyclicity certificate, `combSettle2` returns `.ok` from every shaped state,
under every schedule, at every fuel from `Design2.settleFuel d` on. -/
theorem combSettle2_terminates_of_le {d : Design2} (hd : CombDesign d) (ha : Acyclic d)
    {fuel : Nat} (hf : d.settleFuel ≤ fuel) (σ : ScheduleOracle) (st : SvState) (k : Nat)
    (hs : StateShape d st) : ∃ S k', combSettle2 d σ fuel st k = .ok (S, k') := by
  obtain ⟨S, k', h, -⟩ := combSettle2_terminates_shape_of_le hd ha hf σ st k hs
  exact ⟨S, k', h⟩

/-- **Settle terminates** (the headline statement): on a comb design with an
acyclicity certificate there is a fuel bound above which `combSettle2`
returns `.ok` from every shaped state, under every schedule and schedule
counter. The bound is `Design2.settleFuel d` (`combSettle2_terminates_of_le`). -/
theorem combSettle2_terminates {d : Design2} (hd : CombDesign d) (ha : Acyclic d) :
    ∃ F, ∀ fuel, F ≤ fuel → ∀ σ st k, StateShape d st →
      ∃ S k', combSettle2 d σ fuel st k = .ok (S, k') :=
  ⟨d.settleFuel, fun _ hf σ st k hs => combSettle2_terminates_of_le hd ha hf σ st k hs⟩

/-- **Settle terminates in a shaped state** (`combSettle2_terminates` with
the shape of the result): same hypotheses, and the returned state also has
the comb shape. The bound is `Design2.settleFuel d`
(`combSettle2_terminates_shape_of_le`). -/
theorem combSettle2_terminates_shape {d : Design2} (hd : CombDesign d) (ha : Acyclic d) :
    ∃ F, ∀ fuel, F ≤ fuel → ∀ σ st k, StateShape d st →
      ∃ S k', combSettle2 d σ fuel st k = .ok (S, k') ∧ StateShape d S :=
  ⟨d.settleFuel, fun _ hf σ st k hs =>
    combSettle2_terminates_shape_of_le hd ha hf σ st k hs⟩

/-! ## Smoke test: the full adder settles -/

namespace Comb2Smoke

/-- The full adder's explicit settle fuel. -/
example : faDesign.settleFuel = faDesign.combFuel + 5 := rfl

/-- The full adder's settle from its startup state returns under every
schedule, at the explicit bound. -/
example (σ : ScheduleOracle) (k : Nat) :
    ∃ S k', combSettle2 faDesign σ faDesign.settleFuel (initState2 faDesign) k = .ok (S, k') :=
  combSettle2_terminates_of_le fa_comb fa_acyclic (Nat.le_refl _) σ _ k
    (StateShape.of_initState2 fa_comb)

#guard (combSettle2 faDesign σ_rev faDesign.settleFuel (initState2 faDesign) 0).toOption.isSome

end Comb2Smoke

end LeanModels.Sv
