import LeanModels.Sv.CombViewSound

/-!
# `sv_structure`, stage 4: `CombDesign` and `Acyclic` of `name.sem N` from the obligations

The list-level half: from a design that REALIZES a summary (`Summary.sound`) and the obligations
(`InRangeObl`, `DisjObl`, `RankObl`/`LexObl`) to the comb profile and the rank certificate.
Everything is proved on the closed-form list `Summary.pairs`.

* `ids_pairwise`      : the instances of a summary have pairwise distinct identities (the
  enumeration lists each instance once), from the structural check's key uniqueness;
* `insts_disj`        : the one-driver rule on instances, from the obligation `DisjObl`;
* `comb_of_summary`   : `CombDesign (d.instantiateGD2 args)`;
* `acyclic_of_summary`, `acyclic_of_lex`: `Acyclic (d.instantiateGD2 args)` from a `Nat`-valued rank
  over site identities, or from a LEXICOGRAPHIC key (`LexObl`): the rank of an instance is then the
  number of instances with a strictly smaller key (`countRank`), so key decrease along every read IS
  rank decrease and no arithmetic injection of the key into `Nat` is ever stated.
-/

namespace LeanModels.Sv
namespace CombView


theorem pairwise_intRange {P : Int → Int → Prop} : ∀ (n : Nat) (c0 : Int),
    (∀ i k, c0 ≤ i → i < k → k < c0 + n → P i k) → (intRange c0 n).Pairwise P
  | 0, c0, _ => by simp [intRange]
  | n + 1, c0, h => by
      rw [intRange, List.pairwise_cons]
      refine ⟨fun k hk => ?_, pairwise_intRange n (c0 + 1) (fun i k hi hik hk => h i k (by omega) hik (by omega))⟩
      rw [mem_intRange] at hk
      exact h c0 k (Int.le_refl c0) (by omega) (by omega)

/-- The identity of a located site determines its static key. -/
def idKey : SiteId → String × Nat × Nat
  | .plain p => ("plain", p, 0)
  | .fam b p idx => (b, p, idx.length)

theorem idKey_id (ls : LSite) (σ : String → Int) : idKey (ls.id σ) = ls.key := by
  unfold LSite.id LSite.key
  rcases hh : ls.hdrs with _ | ⟨h, hs⟩
  · simp [idKey]
  · simp [idKey]

theorem key_eq_of_id_eq {a b : LSite} {σ1 σ2 : String → Int} (h : a.id σ1 = b.id σ2) :
    a.key = b.key := by
  rw [← idKey_id a σ1, ← idKey_id b σ2, h]

theorem itemEnum_mem {β : Type} {b : LSite → (String → Int) → IEnv → β} {σ : String → Int}
    {E : IEnv} {f : TFam} {i : Int} {it : TItem} {x : β} (h : x ∈ f.itemEnum b σ E i it) :
    ∃ ls ∈ f.itemLs it, ∃ σ' E', x = b ls σ' E' := by
  cases it with
  | site st =>
      simp only [TFam.itemEnum, List.mem_singleton] at h
      exact ⟨_, by simp [TFam.itemLs], _, _, h⟩
  | loop l =>
      simp only [TFam.itemEnum, List.mem_flatMap, List.mem_map] at h
      obtain ⟨j, hj, st, hst, rfl⟩ := h
      exact ⟨_, by simp only [TFam.itemLs, List.mem_map]; exact ⟨st, hst, rfl⟩, _, _, rfl⟩

theorem famEnum_mem {β : Type} {b : LSite → (String → Int) → IEnv → β} {σ : String → Int}
    {E : IEnv} {f : TFam} {x : β} (h : x ∈ TFam.enum b σ E f) :
    ∃ ls ∈ f.lsites, ∃ σ' E', x = b ls σ' E' := by
  simp only [TFam.enum, List.mem_flatMap] at h
  obtain ⟨i, hi, it, hit, hx⟩ := h
  obtain ⟨ls, hls, σ', E', rfl⟩ := itemEnum_mem hx
  exact ⟨ls, by simp only [TFam.lsites, List.mem_flatMap]; exact ⟨it, hit, hls⟩, σ', E', rfl⟩

theorem site_id_form (f : TFam) (st : TSite) (σ : String → Int) (i : Int) :
    (LSite.mk [f.hdr] f.hdr.name st).id (bindσ f.hdr.g i σ) = SiteId.fam f.hdr.name st.pos [i] := by
  simp [LSite.id]

theorem loop_id_form {f : TFam} {l : TInner} (hg : f.hdr.g ≠ l.hdr.g) (st : TSite)
    (σ : String → Int) (i j : Int) :
    (LSite.mk [f.hdr, l.hdr] l.hdr.name st).id (bindσ l.hdr.g j (bindσ f.hdr.g i σ)) =
      SiteId.fam l.hdr.name st.pos [i, j] := by
  simp [LSite.id, bindσ_ne hg]

/-- Every identifier an item contributes at iteration `i` starts with `i`. -/
theorem itemEnum_head {σ : String → Int} {E : IEnv} {f : TFam} {i : Int} {it : TItem}
    (hg : ∀ l, it = .loop l → f.hdr.g ≠ l.hdr.g) {x : SiteId}
    (h : x ∈ f.itemEnum (fun ls σ' _ => ls.id σ') σ E i it) :
    ∃ b p r, x = SiteId.fam b p (i :: r) := by
  cases it with
  | site st =>
      simp only [TFam.itemEnum, List.mem_singleton] at h
      subst h
      exact ⟨f.hdr.name, st.pos, [], site_id_form f st σ i⟩
  | loop l =>
      simp only [TFam.itemEnum, List.mem_flatMap, List.mem_map] at h
      obtain ⟨j, hj, st, hst, rfl⟩ := h
      have hne := hg l rfl
      exact ⟨l.hdr.name, st.pos, [j], loop_id_form hne st σ i j⟩

theorem itemEnum_loop_form {σ : String → Int} {E : IEnv} {f : TFam} {i : Int} {l : TInner}
    (hg : f.hdr.g ≠ l.hdr.g) {x : SiteId}
    (h : x ∈ f.itemEnum (fun ls σ' _ => ls.id σ') σ E i (.loop l)) :
    ∃ j ∈ l.hdr.range (bindσ f.hdr.g i σ), ∃ st ∈ l.body,
      x = SiteId.fam l.hdr.name st.pos [i, j] := by
  simp only [TFam.itemEnum, List.mem_flatMap, List.mem_map] at h
  obtain ⟨j, hj, st, hst, rfl⟩ := h
  exact ⟨j, hj, st, hst, loop_id_form hg st σ i j⟩

/-- **The identifiers of one top-level loop are pairwise distinct.** -/
theorem fam_ids_pairwise {σ : String → Int} {E : IEnv} {f : TFam}
    (hk : f.lsites.Pairwise (fun a b => a.key ≠ b.key))
    (hg : ∀ l, TItem.loop l ∈ f.body → f.hdr.g ≠ l.hdr.g) :
    (TFam.enum (fun ls σ' _ => ls.id σ') σ E f).Pairwise (· ≠ ·) := by
  unfold TFam.enum
  rw [List.pairwise_flatMap]
  refine ⟨fun i hi => ?_, ?_⟩
  · -- within one iteration
    rw [List.pairwise_flatMap]
    unfold TFam.lsites at hk
    rw [List.pairwise_flatMap] at hk
    obtain ⟨hk1, hk2⟩ := hk
    refine ⟨fun it hit => ?_, ?_⟩
    · cases it with
      | site st => simp [TFam.itemEnum]
      | loop l =>
          simp only [TFam.itemEnum]
          rw [List.pairwise_flatMap]
          have hk1' := hk1 (TItem.loop l) hit
          simp only [TFam.itemLs] at hk1'
          rw [List.pairwise_map] at hk1'
          refine ⟨fun j hj => ?_, ?_⟩
          · rw [List.pairwise_map]
            exact hk1'.imp (fun hab hid => hab (key_eq_of_id_eq hid))
          · apply pairwise_intRange
            intro j j' hj hjj hj' x hx y hy
            simp only [List.mem_map] at hx hy
            obtain ⟨st, hst, rfl⟩ := hx
            obtain ⟨st', hst', rfl⟩ := hy
            have hne := hg l hit
            show (LSite.mk [f.hdr, l.hdr] l.hdr.name st).id _ ≠ (LSite.mk [f.hdr, l.hdr] l.hdr.name st').id _
            rw [loop_id_form hne, loop_id_form hne]
            simp only [ne_eq, SiteId.fam.injEq, List.cons.injEq, and_true, not_and]
            intro _ _ hjj'
            omega
    · refine hk2.imp (fun {a b} hab x hx y hy hxy => ?_)
      obtain ⟨ls1, hl1, σ1, E1, rfl⟩ := itemEnum_mem hx
      obtain ⟨ls2, hl2, σ2, E2, rfl⟩ := itemEnum_mem hy
      exact hab ls1 hl1 ls2 hl2 (key_eq_of_id_eq hxy)
  · -- across iterations
    unfold Hdr.range
    apply pairwise_intRange
    intro i k hi hik hk x hx y hy hxy
    simp only [List.mem_flatMap] at hx hy
    obtain ⟨it, hit, hx⟩ := hx
    obtain ⟨it', hit', hy⟩ := hy
    obtain ⟨b, p, r, rfl⟩ := itemEnum_head (fun l hl => hg l (hl ▸ hit)) hx
    obtain ⟨b', p', r', rfl⟩ := itemEnum_head (fun l hl => hg l (hl ▸ hit')) hy
    simp only [SiteId.fam.injEq, List.cons.injEq] at hxy
    omega


/-! ## Identities are distinct -/

theorem hdr_g_ne {s : Summary} (hok : s.StructOk) {f : TFam} (hf : f ∈ s.fams) {l : TInner}
    (hl : TItem.loop l ∈ f.body) : f.hdr.g ≠ l.hdr.g := by
  have hp2 : [f.hdr, l.hdr] ∈ s.hdrPaths := by
    unfold Summary.hdrPaths
    simp only [List.mem_flatMap, List.mem_cons, List.mem_filterMap]
    exact ⟨f, hf, Or.inr ⟨TItem.loop l, hl, rfl⟩⟩
  obtain ⟨hnd, -⟩ := path_facts hok hp2
  intro heq
  have h1 := (List.nodup_cons.mp hnd).1
  apply h1
  simp [heq]

/-- **Distinct positions of the closed-form list have distinct identities.** -/
theorem ids_pairwise {s : Summary} {σ : String → Int} {E : IEnv} (hok : s.StructOk) :
    (s.insts σ E).Pairwise (fun a b => a.id ≠ b.id) := by
  have hkeys := hok.2.2.2.2.2.2.2
  rw [← List.pairwise_map (f := SiteInst.id) (R := fun a b => a ≠ b)]
  unfold Summary.insts
  rw [Summary.enum_map]
  unfold Summary.enum
  rw [List.pairwise_append]
  unfold Summary.lsites at hkeys
  rw [List.pairwise_append] at hkeys
  obtain ⟨hkA, hkB, hkAB⟩ := hkeys
  refine ⟨?_, ?_, ?_⟩
  · rw [List.pairwise_map]
    rw [List.pairwise_map] at hkA
    refine hkA.imp ?_
    intro a b hab hid
    exact hab (key_eq_of_id_eq (σ1 := σ) (σ2 := σ) hid)
  · rw [List.pairwise_flatMap]
    rw [List.pairwise_flatMap] at hkB
    obtain ⟨hkB1, hkB2⟩ := hkB
    refine ⟨fun f hf => fam_ids_pairwise (hkB1 f hf) (fun l hl => hdr_g_ne hok hf hl), ?_⟩
    refine hkB2.imp (fun {f1 f2} h12 x hx y hy hxy => ?_)
    obtain ⟨ls1, hl1, σ1, E1, rfl⟩ := famEnum_mem hx
    obtain ⟨ls2, hl2, σ2, E2, rfl⟩ := famEnum_mem hy
    exact h12 ls1 hl1 ls2 hl2 (key_eq_of_id_eq hxy)
  · intro x hx y hy hxy
    simp only [List.mem_map] at hx
    obtain ⟨st, hst, rfl⟩ := hx
    simp only [List.mem_flatMap] at hy
    obtain ⟨f, hf, hy⟩ := hy
    obtain ⟨ls2, hl2, σ2, E2, rfl⟩ := famEnum_mem hy
    exact hkAB _ (List.mem_map.mpr ⟨st, hst, rfl⟩) ls2
      (List.mem_flatMap.mpr ⟨f, hf, hl2⟩) (key_eq_of_id_eq (σ1 := σ) (σ2 := σ2) hxy)

/-! ## The one-driver rule on instances -/

theorem disjOne_iff {s : Summary} {σ : String → Int} {a b : LSite} :
    s.DisjOne σ a b ↔ ∀ σ1, Reach a.hdrs σ σ1 → ∀ σ2, Reach b.hdrs σ σ2 → a.id σ1 ≠ b.id σ2 →
      Win.overlaps (a.site.tgt.win σ1 (s.dw σ)) (b.site.tgt.win σ2 (s.dw σ)) = false := by
  unfold Summary.DisjOne
  rw [Loops.all_iff]
  constructor
  · intro H σ1 h1 σ2 h2
    exact (Loops.all_iff _ _ _).mp (H σ1 h1) σ2 h2
  · intro H σ1 h1
    exact (Loops.all_iff _ _ _).mpr (fun σ2 h2 => H σ1 h1 σ2 h2)

theorem pairwise_cases {α : Type} {R : α → α → Prop} :
    ∀ {l : List α}, l.Pairwise R → ∀ {a b : α}, a ∈ l → b ∈ l → a ≠ b → R a b ∨ R b a
  | [], _, a, b, ha, _, _ => absurd ha (by simp)
  | x :: xs, h, a, b, ha, hb, hab => by
      rw [List.pairwise_cons] at h
      rcases List.mem_cons.mp ha with rfl | ha'
      · rcases List.mem_cons.mp hb with rfl | hb'
        · exact absurd rfl hab
        · exact Or.inl (h.1 b hb')
      · rcases List.mem_cons.mp hb with rfl | hb'
        · exact Or.inr (h.1 a ha')
        · exact pairwise_cases h.2 ha' hb' hab

/-- **The one-driver rule on instances**: two instances with different identities drive disjoint
windows. -/
theorem insts_disj {s : Summary} {σ : String → Int} {E : IEnv} (hd : s.DisjObl σ) :
    ∀ x ∈ s.insts σ E, ∀ y ∈ s.insts σ E, x.id ≠ y.id →
      Win.overlaps x.win y.win = false := by
  intro x hx y hy hne
  obtain ⟨a, ha, σ1, h1, rfl⟩ := mem_insts.mp hx
  obtain ⟨b, hb, σ2, h2, rfl⟩ := mem_insts.mp hy
  by_cases hab : a = b
  · subst hab
    exact (disjOne_iff.mp (hd.2 a ha)) σ1 h1 σ2 h2 hne
  · rcases pairwise_cases hd.1 ha hb hab with h | h
    · exact (disjOne_iff.mp h) σ1 h1 σ2 h2 hne
    · rw [Win.overlaps_comm]
      exact (disjOne_iff.mp h) σ2 h2 σ1 h1 (fun e => hne e.symm)

/-! ## The geometry of an instance -/

theorem DW_eq {s : Summary} {σ : String → Int} {n : String} (h : (s.find n).isSome = true) :
    s.DW σ n = some (s.dw σ n) := by
  unfold Summary.DW Summary.dw
  cases hf : s.find n with
  | none => simp [hf] at h
  | some dt => simp

theorem dw_pos {s : Summary} {σ : String → Int} {n : String} (h : (s.find n).isSome = true) :
    0 < s.dw σ n := by
  unfold Summary.dw
  cases hf : s.find n with
  | none => simp [hf] at h
  | some dt => simpa using DeclT.width_pos σ dt

def valsW : List (Int × Int) → Nat
  | [] => 1
  | (m, l) :: r => ((m - l).natAbs + 1) * valsW r

theorem dimsW_eq_valsW (σ : String → Int) : ∀ dims : List (PDim × Aff × Aff),
    dimsW σ dims = valsW (dims.map fun p => (p.2.1.eval σ, p.2.2.eval σ))
  | [] => rfl
  | (d, m, l) :: r => by simp [dimsW, valsW, dimsW_eq_valsW σ r]

theorem dw_of_DG {s : Summary} {σ : String → Int} {n : String} {vs : List (Int × Int)}
    (h : s.DG σ n = some vs) : s.dw σ n = valsW vs := by
  unfold Summary.DG at h
  rcases hf : s.find n with _ | dt
  · simp [hf] at h
  · simp only [hf, Option.map_some, Option.some.injEq] at h
    subst h
    simp [Summary.dw, hf, DeclT.width, DeclT.vals, dimsW_eq_valsW]

theorem Acc.win_name (σ : String → Int) (dw : String → Nat) (a : Acc) : (a.win σ dw).1 = a.name := by
  cases a <;> rfl

/-- An in-range target access has a positive-width window inside its declared signal. -/
theorem acc_win_facts {s : Summary} {σd σs : String → Int} {a : Acc}
    (hdw : (s.find a.name).isSome = true) (hg : AccGeom σs (s.DG σd) (s.EW σd) a)
    (hbit : ∀ n x, a = .bit n x → x.eval σs + 1 ≤ (s.dw σd n : Int)) :
    0 < (a.win σs (s.dw σd)).2.2 ∧
      (a.win σs (s.dw σd)).2.1 + (a.win σs (s.dw σd)).2.2 ≤ s.dw σd a.name := by
  cases a with
  | whole n => exact ⟨by simpa [Acc.win, Acc.name] using dw_pos (σ := σd) hdw, by simp [Acc.win, Acc.name]⟩
  | bit n x =>
      obtain ⟨hx0, -⟩ := hg
      have hb := hbit n x rfl
      simp only [Acc.win, Acc.lo, Acc.name]
      exact ⟨by omega, by omega⟩
  | cell1 n x =>
      obtain ⟨m, hdg, hx0, hx1⟩ := hg
      have := dw_of_DG hdg
      simp only [valsW] at this
      simp only [Acc.win, Acc.lo, Acc.name]
      refine ⟨by omega, by omega⟩
  | row n w r =>
      obtain ⟨m1, m2, hdg, hm2, hw, hr0, hr1⟩ := hg
      have h1 : s.dw σd n = (m1.natAbs + 1) * (m2.natAbs + 1) := by
        rw [dw_of_DG hdg]; simp [valsW]
      simp only [Acc.win, Acc.lo, Acc.wid, Acc.name, hw]
      refine ⟨by omega, ?_⟩
      have := rmN_row_le (W := m2 + 1) (i := r.eval σs) (m1 := m1) hr1 (by omega) hr0
      have e1 : (m1 + 1).toNat = m1.natAbs + 1 := by omega
      have e2 : (m2 + 1).toNat = m2.natAbs + 1 := by omega
      rw [h1]
      exact Nat.le_trans this (Nat.le_of_eq (by rw [e1, e2]))
  | cell2 n w r c =>
      obtain ⟨m1, m2, hdg, hw, hr0, hr1, hc0, hc1⟩ := hg
      have h1 : s.dw σd n = (m1.natAbs + 1) * (m2.natAbs + 1) := by
        rw [dw_of_DG hdg]; simp [valsW]
      simp only [Acc.win, Acc.lo, Acc.name, hw]
      refine ⟨by omega, ?_⟩
      have := rmN_cell_le (W := m2 + 1) (i := r.eval σs) (j := c.eval σs) (m1 := m1) hr1
        (by omega) (by omega) hc0 hr0
      have e1 : (m1 + 1).toNat = m1.natAbs + 1 := by omega
      have e2 : (m2 + 1).toNat = m2.natAbs + 1 := by omega
      rw [e1, e2] at this
      rw [h1]
      exact this
  | part1 n hi lo =>
      obtain ⟨m, hdg, hy0, hyx, hxm⟩ := hg
      have := dw_of_DG hdg
      simp only [valsW] at this
      simp only [Acc.win, Acc.lo, Acc.wid, Acc.name]
      refine ⟨by omega, by omega⟩
  | part2 n w r hi lo =>
      obtain ⟨m1, m2, hdg, hw, hr0, hr1, hy0, hyx, hxm⟩ := hg
      have h1 : s.dw σd n = (m1.natAbs + 1) * (m2.natAbs + 1) := by
        rw [dw_of_DG hdg]; simp [valsW]
      simp only [Acc.win, Acc.lo, Acc.wid, Acc.name, hw]
      refine ⟨by omega, ?_⟩
      have := rmN_part_le (W := m2 + 1) (i := r.eval σs) (m1 := m1) (lo := lo.eval σs)
        (hi := hi.eval σs) hr1 (by omega) hr0 hy0 hyx (by omega)
      rw [h1]
      have e1 : (m1 + 1).toNat = m1.natAbs + 1 := by omega
      have e2 : (m2 + 1).toNat = m2.natAbs + 1 := by omega
      rw [e1, e2] at this
      exact this

theorem reach_par {s : Summary} (hok : s.StructOk) {ls : LSite} (hls : ls ∈ s.lsites)
    {σ σ' : String → Int} (hr : Reach ls.hdrs σ σ') : ∀ n ∈ s.params, σ' n = σ n := by
  rcases lsite_hdrs hls with h0 | hp
  · rw [h0] at hr
    have : σ' = σ := hr
    subst this
    intro n _; rfl
  · apply Reach_params hr
    intro h hh
    exact notin_of_nodup (path_facts hok hp).1 (List.mem_map.mpr ⟨h, hh, rfl⟩)

/-- **Every instance is a located site at a reachable valuation, with the in-range geometry of
its target.** -/
theorem inst_geom {s : Summary} {σ : String → Int} {E : IEnv} {args : List Int}
    (hok : s.StructOk) (hauto : s.AutoObl σ args) (hin : s.InRangeObl σ) {a : SiteInst}
    (ha : a ∈ s.insts σ E) :
    ∃ ls ∈ s.lsites, ∃ σ', Reach ls.hdrs σ σ' ∧ a = ls.inst σ' (s.dw σ) ∧
      AccGeom σ' (s.DG σ) (s.EW σ) ls.site.tgt ∧ (s.find ls.site.tgt.name).isSome = true ∧
      (∀ n x, ls.site.tgt = .bit n x → x.eval σ' + 1 ≤ (s.dw σ n : Int)) := by
  obtain ⟨ls, hls, σ', hr, rfl⟩ := mem_insts.mp ha
  obtain ⟨hnodup, hnames, hinput, haff, hpaths, hdecl, hacc, hkeys⟩ := hok
  have hpar := reach_par ⟨hnodup, hnames, hinput, haff, hpaths, hdecl, hacc, hkeys⟩ hls hr
  have hin' := (Loops.all_iff _ _ _).mp (hin ls hls) σ' hr
  have hdn : (s.find ls.site.tgt.name).isSome = true :=
    find_isSome_of_mem (hnames ls hls _ (by simp [TSite.names]))
  exact ⟨ls, hls, σ', hr, rfl,
    accGeom_of hpar hdecl (hacc ls hls _ (List.mem_cons_self ..)) hin'.1 (hauto.2.1 ls hls _ (List.mem_cons_self ..)),
    hdn, fun n x h => by have := hin'.2; rw [h] at this; exact this⟩

theorem declWidth_eq {s : Summary} {σ : String → Int} {m : Design2}
    (hdecl : m.decls.toList = s.decls.map (DeclT.toDecl σ)) (n : String) :
    m.declWidth n = s.DW σ n := by
  simp [Design2.declWidth, hdecl, Summary.DW, Summary.find, findDecl, List.find?_map,
    Function.comp_def, Option.map_map]

theorem Acc.lhs_ne_concat (σ : String → Int) (a : Acc) (ps : List Lhs2) : a.lhs σ ≠ .concat ps := by
  cases a <;> simp [Acc.lhs]

theorem acc_windows {s : Summary} {σd σs : String → Int} {m : Design2}
    (hdecl : m.decls.toList = s.decls.map (DeclT.toDecl σd)) (a : Acc)
    (hdn : (s.find a.name).isSome = true) :
    (a.lhs σs).windows? m = some [a.win σs (s.dw σd)] := by
  cases a with
  | whole n =>
      simp only [Acc.name] at hdn
      simp [Acc.lhs, Acc.win, declWidth_eq hdecl, DW_eq hdn]
  | bit n x => simp [Acc.lhs, Acc.win, Lhs2.windows?, Lhs2.window?]
  | cell1 n x => simp [Acc.lhs, Acc.win, Lhs2.windows?, Lhs2.window?]
  | row n w r => simp [Acc.lhs, Acc.win, Lhs2.windows?, Lhs2.window?]
  | cell2 n w r c => simp [Acc.lhs, Acc.win, Lhs2.windows?, Lhs2.window?]
  | part1 n hi lo => simp [Acc.lhs, Acc.win, Lhs2.windows?, Lhs2.window?]
  | part2 n w r hi lo => simp [Acc.lhs, Acc.win, Lhs2.windows?, Lhs2.window?]

theorem inrange_insts {s : Summary} {σ : String → Int} {E : IEnv} {args : List Int}
    (hok : s.StructOk) (hauto : s.AutoObl σ args) (hin : s.InRangeObl σ) {a : SiteInst}
    (ha : a ∈ s.insts σ E) :
    ∃ dw, s.DW σ a.win.1 = some dw ∧ a.win.2.1 + a.win.2.2 ≤ dw := by
  obtain ⟨ls, hls, σ', hr, rfl, hg, hdn, hbit⟩ := inst_geom hok hauto hin ha
  obtain ⟨-, hle⟩ := acc_win_facts (σd := σ) hdn hg hbit
  refine ⟨s.dw σ ls.site.tgt.name, ?_, ?_⟩
  · have : (ls.inst σ' (s.dw σ)).win.1 = ls.site.tgt.name := Acc.win_name σ' (s.dw σ) ls.site.tgt
    rw [this]
    exact DW_eq hdn
  · exact hle

/-- The window facts of one footprint. -/
theorem inst_facts {s : Summary} {σ : String → Int} {E : IEnv} {args : List Int} {m : Design2}
    (hok : s.StructOk) (hauto : s.AutoObl σ args) (hin : s.InRangeObl σ)
    (hdecl : m.decls.toList = s.decls.map (DeclT.toDecl σ)) {a : SiteInst}
    (ha : a ∈ s.insts σ E) :
    (∀ ps, a.tgt ≠ .concat ps) ∧ a.tgt.windows? m = some [a.win] ∧ 0 < a.win.2.2 ∧
      a.win.1 ∉ s.inputNames := by
  obtain ⟨ls, hls, σ', hr, rfl, hg, hdn, hbit⟩ := inst_geom hok hauto hin ha
  obtain ⟨hpos, -⟩ := acc_win_facts (σd := σ) hdn hg hbit
  have hni := hok.2.2.1 ls hls
  have hname : (ls.inst σ' (s.dw σ)).win.1 = ls.site.tgt.name :=
    Acc.win_name σ' (s.dw σ) ls.site.tgt
  refine ⟨?_, ?_, hpos, by rw [hname]; exact hni⟩
  · intro ps
    exact Acc.lhs_ne_concat σ' ls.site.tgt ps
  · exact acc_windows hdecl ls.site.tgt hdn

theorem Realized.inputNames {s : Summary} {σ : String → Int} {m : Design2}
    (hdecl : m.decls.toList = s.decls.map (DeclT.toDecl σ)) :
    m.inputNames.toList = s.inputNames := by
  simp [Design2.inputNames, hdecl, Summary.inputNames, List.filterMap_map, Function.comp_def] <;> rfl

theorem pairwise_getElem? {α : Type} {R : α → α → Prop} {l : List α} (h : l.Pairwise R)
    {i j : Nat} {a b : α} (hij : i < j) (ha : l[i]? = some a) (hb : l[j]? = some b) : R a b := by
  rw [List.pairwise_iff_getElem] at h
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp ha
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp hb
  exact h i j hi hj hij

theorem win_eq {n : String} {lo w : Nat} {x : Win} (h : (n, lo, w) = x) :
    n = x.1 ∧ lo = x.2.1 ∧ w = x.2.2 := by
  subst h; exact ⟨rfl, rfl, rfl⟩

/-- `Realized` + obligations ⇒ the comb profile (and positive write windows). -/
theorem realized_comb {s : Summary} {σ : String → Int} {m : Design2} {args : List Int}
    (hR : Realized s σ m) (hok : s.StructOk) (hauto : s.AutoObl σ args) (hin : s.InRangeObl σ)
    (hd : s.DisjObl σ) :
    CombDesign m ∧ ∀ i n lo w, m.Writes i (n, lo, w) → 0 < w := by
  obtain ⟨hdecl, E, L, hLf, hP, hdesc⟩ := hR
  have hok' := hok
  obtain ⟨hnodup, -, -, -, -, -, -, -⟩ := hok'
  have hget : ∀ (i : Nat) (p : Process2), m.processes[i]? = some p ↔
      ∃ q : SiteInst × Process2, L[i]? = some q ∧ p = q.2 := by
    intro i p
    rw [← Array.getElem?_toList, hP, List.getElem?_map]
    cases hL : L[i]? with
    | none => simp
    | some q => simp [eq_comm]
  have hmemL : ∀ q : SiteInst × Process2, q ∈ L → q.1 ∈ s.insts σ E :=
    fun q hq => hLf ▸ List.mem_map.2 ⟨q, hq, rfl⟩
  have hfacts := fun (q : SiteInst × Process2) (hq : q ∈ L) =>
    inst_facts hok hauto hin hdecl (hmemL q hq)
  have hpw : L.Pairwise fun p q => Win.overlaps p.1.win q.1.win = false := by
    have h1 : (L.map Prod.fst).Pairwise (fun a b => a.id ≠ b.id) := by
      rw [hLf]; exact ids_pairwise hok
    rw [List.pairwise_map] at h1
    exact h1.imp_of_mem (fun {p q} hp hq hne => insts_disj hd _ (hmemL p hp) _ (hmemL q hq) hne)
  have hwr : ∀ {i wn}, m.Writes i wn → ∃ q, L[i]? = some q ∧ wn = q.1.win := by
    rintro i wn ⟨t, e, hp, hw⟩
    obtain ⟨q, hq, hqe⟩ := (hget i _).mp hp
    obtain ⟨e', hpe, -⟩ := hdesc q (List.mem_of_getElem? hq)
    rw [hpe] at hqe
    simp only [Process2.assign.injEq] at hqe
    obtain ⟨rfl, rfl⟩ := hqe
    refine ⟨q, hq, ?_⟩
    rw [Lhs2.wins_of_windows? (hfacts q (List.mem_of_getElem? hq)).2.1] at hw
    simpa using hw
  have hpos : ∀ i n lo w, m.Writes i (n, lo, w) → 0 < w := by
    intro i n lo w hw
    obtain ⟨q, hq, hwq⟩ := hwr hw
    have := (hfacts q (List.mem_of_getElem? hq)).2.2.1
    obtain ⟨-, -, hw'⟩ := win_eq hwq
    rw [hw']
    exact this
  refine ⟨?_, hpos⟩
  refine
    { nodup := ?_, assign := ?_, inWidth := ?_, notInput := ?_, disjoint := ?_,
      selfDisjoint := ?_, rhsFree := ?_, rhsDeclared := ?_, initWidth := ?_,
      inFourState := ?_ }
  · rw [hdecl]
    simpa [List.map_map, Function.comp_def, Summary.declNames] using hnodup
  · intro i p hp
    obtain ⟨q, hq, rfl⟩ := (hget i p).mp hp
    obtain ⟨e, hpe, -⟩ := hdesc q (List.mem_of_getElem? hq)
    exact ⟨q.1.tgt, e, [q.1.win], hpe, (hfacts q (List.mem_of_getElem? hq)).2.1⟩
  · intro i n lo w hw
    obtain ⟨q, hq, hwq⟩ := hwr hw
    obtain ⟨dw, hdw, hle⟩ := inrange_insts hok hauto hin (hmemL q (List.mem_of_getElem? hq))
    obtain ⟨h1, h2, h3⟩ := win_eq hwq
    refine ⟨dw, by rw [declWidth_eq hdecl, h1]; exact hdw, ?_⟩
    rw [h2, h3]
    exact hle
  · intro n hn
    obtain ⟨i, lo, w, hw⟩ := hn
    obtain ⟨q, hq, hwq⟩ := hwr hw
    have := (hfacts q (List.mem_of_getElem? hq)).2.2.2
    obtain ⟨h1, -, -⟩ := win_eq hwq
    rw [Realized.inputNames hdecl, h1]
    exact this
  · intro i j wi wj hij hi hj
    obtain ⟨qi, hqi, rfl⟩ := hwr hi
    obtain ⟨qj, hqj, rfl⟩ := hwr hj
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · exact pairwise_getElem? hpw h hqi hqj
    · rw [Win.overlaps_comm]
      exact pairwise_getElem? hpw h hqj hqi
  · intro i t e hp
    obtain ⟨q, hq, hqe⟩ := (hget i _).mp hp
    obtain ⟨e', hpe, -⟩ := hdesc q (List.mem_of_getElem? hq)
    rw [hpe] at hqe
    simp only [Process2.assign.injEq] at hqe
    obtain ⟨rfl, rfl⟩ := hqe
    exact Lhs2.wins_pairwise_of_leaf (hfacts q (List.mem_of_getElem? hq)).1 _
  · intro i t e hp
    obtain ⟨q, hq, hqe⟩ := (hget i _).mp hp
    obtain ⟨e', hpe, -, hfree, -⟩ := hdesc q (List.mem_of_getElem? hq)
    rw [hpe] at hqe
    simp only [Process2.assign.injEq] at hqe
    obtain ⟨rfl, rfl⟩ := hqe
    exact hfree
  · intro i t e hp x hx
    obtain ⟨q, hq, hqe⟩ := (hget i _).mp hp
    obtain ⟨e', hpe, -, -, hid⟩ := hdesc q (List.mem_of_getElem? hq)
    rw [hpe] at hqe
    simp only [Process2.assign.injEq] at hqe
    obtain ⟨rfl, rfl⟩ := hqe
    have := hid x hx
    rw [hdecl]
    simpa [List.map_map, Function.comp_def, Summary.declNames] using this
  · intro n _ dc hdc _ v hv
    rw [hdecl] at hdc
    obtain ⟨dt, -, rfl⟩ := List.mem_map.mp hdc
    simp at hv
  · intro dc hdc _
    rw [hdecl] at hdc
    obtain ⟨dt, -, rfl⟩ := List.mem_map.mp hdc
    rfl

theorem Acc.rd_name (σ : String → Int) (a : Acc) : (a.rd σ).name = a.name := by
  cases a <;> rfl

theorem ReadWin.overlaps_name {r : ReadWin} {w : Win} (h : ReadWin.overlaps r w = true) :
    r.name = w.1 := by
  cases r with
  | whole n =>
      obtain ⟨m, lo, wd⟩ := w
      simpa [ReadWin.overlaps, ReadWin.name] using h
  | win n lo wd =>
      obtain ⟨m, lo', wd'⟩ := w
      simp only [ReadWin.overlaps, Win.overlaps_eq_true] at h
      simpa [ReadWin.name] using h.1

/-- **The rank obligation, on instances.** -/
theorem rank_insts {s : Summary} {σ : String → Int} {E : IEnv} {R : SiteId → SiteId → Prop}
    (hr : s.RankObl' R σ) {a b : SiteInst} (ha : a ∈ s.insts σ E) (hb : b ∈ s.insts σ E)
    {r : ReadWin} (hra : r ∈ a.rd) (hov : ReadWin.overlaps r b.win = true) : R b.id a.id := by
  obtain ⟨la, hla, σ1, h1, rfl⟩ := mem_insts.mp ha
  obtain ⟨lb, hlb, σ2, h2, rfl⟩ := mem_insts.mp hb
  obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hra
  have hname : r'.name = lb.site.tgt.name := by
    have h1 := ReadWin.overlaps_name hov
    have h2' : (lb.inst σ2 (s.dw σ)).win.1 = lb.site.tgt.name :=
      Acc.win_name σ2 (s.dw σ) lb.site.tgt
    rw [Acc.rd_name, h2'] at h1
    exact h1
  have hw : lb ∈ s.writersOf r'.name := by
    unfold Summary.writersOf
    rw [List.mem_filter]
    exact ⟨hlb, by simp [hname]⟩
  exact (Loops.all_iff _ _ _).mp ((Loops.all_iff _ _ _).mp (hr la hla r' hr' lb hw) σ1 h1) σ2 h2 hov

theorem realized_acyclic {s : Summary} {σ : String → Int} {m : Design2} {args : List Int}
    {R : SiteId → SiteId → Prop}
    (hR : Realized s σ m) (hok : s.StructOk) (hauto : s.AutoObl σ args) (hin : s.InRangeObl σ)
    (hr : s.RankObl' R σ)
    (hrank : ∀ L : List SiteId, ∃ rk : SiteId → Nat, ∀ a ∈ L, ∀ b ∈ L, R b a → rk b < rk a) :
    Acyclic m := by
  obtain ⟨hdecl, E, L, hLf, hP, hdesc⟩ := hR
  have hget : ∀ (i : Nat) (p : Process2), m.processes[i]? = some p ↔
      ∃ q : SiteInst × Process2, L[i]? = some q ∧ p = q.2 := by
    intro i p
    rw [← Array.getElem?_toList, hP, List.getElem?_map]
    cases hL : L[i]? with
    | none => simp
    | some q => simp [eq_comm]
  have hmemL : ∀ q : SiteInst × Process2, q ∈ L → q.1 ∈ s.insts σ E :=
    fun q hq => hLf ▸ List.mem_map.2 ⟨q, hq, rfl⟩
  obtain ⟨rk, hrk⟩ := hrank (L.map fun q => q.1.id)
  refine ⟨fun j => match L[j]? with | some q => rk q.1.id | none => 0, ?_⟩
  intro i j ti ei tj ej wj hpi hpj hwj ⟨r, hrE, hov⟩
  obtain ⟨qi, hqi, hqie⟩ := (hget i _).mp hpi
  obtain ⟨qj, hqj, hqje⟩ := (hget j _).mp hpj
  obtain ⟨ei', hpei, hrd, -, -⟩ := hdesc qi (List.mem_of_getElem? hqi)
  obtain ⟨ej', hpej, -⟩ := hdesc qj (List.mem_of_getElem? hqj)
  rw [hpei] at hqie
  rw [hpej] at hqje
  simp only [Process2.assign.injEq] at hqie hqje
  obtain ⟨rfl, rfl⟩ := hqie
  obtain ⟨rfl, rfl⟩ := hqje
  have hw : wj = qj.1.win := by
    have hf := (inst_facts hok hauto hin hdecl (hmemL qj (List.mem_of_getElem? hqj))).2.1
    rw [Lhs2.wins_of_windows? hf] at hwj
    simpa using hwj
  subst hw
  simp only [hqi, hqj]
  have hR' := rank_insts hr (hmemL qi (List.mem_of_getElem? hqi))
    (hmemL qj (List.mem_of_getElem? hqj)) (hrd r hrE) hov
  exact hrk qi.1.id (List.mem_map.2 ⟨qi, List.mem_of_getElem? hqi, rfl⟩) qj.1.id
    (List.mem_map.2 ⟨qj, List.mem_of_getElem? hqj, rfl⟩) hR'

/-! ## The structural theorems for `name.sem` -/

/-- **`CombDesign (name.sem N)`** from the summary and the obligations. -/
theorem comb_of_summary {d : PDesign} {s : Summary} (hs : d.summary = .ok s) {args : List Int}
    {σ : String → Int} {env : IEnv} (harity : args.length = d.params.length)
    (h1 : d.paramEnv2 args = .ok env) (hag : Agrees σ env s.params) (hok : s.StructOk)
    (hauto : s.AutoObl σ args) (hin : s.InRangeObl σ) (hdisj : s.DisjObl σ) :
    CombDesign (d.instantiateGD2 args) := by
  obtain ⟨m, hm, hR⟩ := Summary.sound hs harity h1 hag hok hauto hin
  obtain ⟨hc, hpos⟩ := realized_comb hR hok hauto hin hdisj
  rw [PDesign.instantiateGD2_of_combDesign hm hc hpos]
  exact hc

/-- **`Acyclic (name.sem N)`** from the summary, the obligations and a rank over sites. -/
theorem acyclic_of_summary {d : PDesign} {s : Summary} (hs : d.summary = .ok s) {args : List Int}
    {σ : String → Int} {env : IEnv} (harity : args.length = d.params.length)
    (h1 : d.paramEnv2 args = .ok env) (hag : Agrees σ env s.params) (hok : s.StructOk)
    (hauto : s.AutoObl σ args) (hin : s.InRangeObl σ) (hdisj : s.DisjObl σ)
    {ρ : SiteId → Nat} (hrank : s.RankObl ρ σ) :
    Acyclic (d.instantiateGD2 args) := by
  obtain ⟨m, hm, hR⟩ := Summary.sound hs harity h1 hag hok hauto hin
  obtain ⟨hc, hpos⟩ := realized_comb hR hok hauto hin hdisj
  rw [PDesign.instantiateGD2_of_combDesign hm hc hpos]
  exact realized_acyclic hR hok hauto hin hrank (fun _ => ⟨ρ, fun _ _ _ _ h => h⟩)

/-- … from a LEXICOGRAPHIC key: the rank is the number of instances with a smaller key. -/
theorem acyclic_of_lex {d : PDesign} {s : Summary} (hs : d.summary = .ok s) {args : List Int}
    {σ : String → Int} {env : IEnv} (harity : args.length = d.params.length)
    (h1 : d.paramEnv2 args = .ok env) (hag : Agrees σ env s.params) (hok : s.StructOk)
    (hauto : s.AutoObl σ args) (hin : s.InRangeObl σ) (hdisj : s.DisjObl σ)
    {κ : SiteId → Key} (hrank : s.LexObl κ σ) :
    Acyclic (d.instantiateGD2 args) := by
  obtain ⟨m, hm, hR⟩ := Summary.sound hs harity h1 hag hok hauto hin
  obtain ⟨hc, hpos⟩ := realized_comb hR hok hauto hin hdisj
  rw [PDesign.instantiateGD2_of_combDesign hm hc hpos]
  exact realized_acyclic hR hok hauto hin hrank
    (fun L => ⟨countRank L κ, fun a _ b hb h => countRank_lt L κ hb h⟩)

/-! ## The forms the tactic uses: the valuation is the parameters zipped with the arguments, then the localparams -/

theorem Agrees_of_map {σ : String → Int} {env : IEnv} {ns : List String}
    (h : ns.map (fun n => env.vals.lookup n) = ns.map (fun n => some (σ n))) :
    Agrees σ env ns := by
  intro n hn
  exact List.map_inj_left.mp h n hn

/-- `comb_of_summary` at the canonical valuation `s.val args` (the parameters zipped with the
arguments, then the localparams: `σL (params.zip args)` for a design without any), the environment
check in a `rfl`-provable form. -/
theorem comb_view {d : PDesign} {s : Summary} {args : List Int} {env : IEnv}
    (hs : d.summary = .ok s) (harity : args.length = d.params.length)
    (h1 : d.paramEnv2 args = .ok env)
    (hag : s.params.map (fun n => env.vals.lookup n) =
      s.params.map (fun n => some (s.val args n)))
    (hok : s.StructOk) (hauto : s.AutoObl (s.val args) args)
    (hin : s.InRangeObl (s.val args)) (hdisj : s.DisjObl (s.val args)) :
    CombDesign (d.instantiateGD2 args) :=
  comb_of_summary hs harity h1 (Agrees_of_map hag) hok hauto hin hdisj

theorem acyclic_view {d : PDesign} {s : Summary} {args : List Int} {env : IEnv}
    (hs : d.summary = .ok s) (harity : args.length = d.params.length)
    (h1 : d.paramEnv2 args = .ok env)
    (hag : s.params.map (fun n => env.vals.lookup n) =
      s.params.map (fun n => some (s.val args n)))
    (hok : s.StructOk) (hauto : s.AutoObl (s.val args) args)
    (hin : s.InRangeObl (s.val args)) (hdisj : s.DisjObl (s.val args))
    (ρ : SiteId → Nat) (hrank : s.RankObl ρ (s.val args)) :
    Acyclic (d.instantiateGD2 args) :=
  acyclic_of_summary hs harity h1 (Agrees_of_map hag) hok hauto hin hdisj hrank

theorem lex_view {d : PDesign} {s : Summary} {args : List Int} {env : IEnv}
    (hs : d.summary = .ok s) (harity : args.length = d.params.length)
    (h1 : d.paramEnv2 args = .ok env)
    (hag : s.params.map (fun n => env.vals.lookup n) =
      s.params.map (fun n => some (s.val args n)))
    (hok : s.StructOk) (hauto : s.AutoObl (s.val args) args)
    (hin : s.InRangeObl (s.val args)) (hdisj : s.DisjObl (s.val args))
    (κ : SiteId → Key) (hrank : s.LexObl κ (s.val args)) :
    Acyclic (d.instantiateGD2 args) :=
  acyclic_of_lex hs harity h1 (Agrees_of_map hag) hok hauto hin hdisj hrank

/-- A design that is a comb design in the guarded family IS the unguarded instantiation. -/
theorem instantiateGD2_eq_of_comb {d : PDesign} {args : List Int} {m : Design2}
    (hm : d.instantiate2 args (PDesign.surfaceFuel args) = .ok m)
    (hc : CombDesign (d.instantiateGD2 args)) : d.instantiateGD2 args = m := by
  have hG : d.instantiateGD2 args = d.driverGuard m := by
    unfold PDesign.instantiateGD2 PDesign.instantiateG2
    rw [hm]
    rfl
  rw [hG] at hc ⊢
  unfold PDesign.driverGuard Design2.driverGuard at hc ⊢
  by_cases hd : driversOk d.declNames d.inputNames m.processes.toList = true
  · simp only [hd, if_true]
  · exfalso
    simp only [hd] at hc
    have hget : (m.processes.push (Process2.unsupported "PortConn:driver"
        (driversMsg m.name d.declNames d.inputNames m.processes.toList)))[m.processes.size]? =
        some (Process2.unsupported "PortConn:driver"
          (driversMsg m.name d.declNames d.inputNames m.processes.toList)) := by
      simp
    obtain ⟨t, e, ws, hp, -⟩ := hc.assign m.processes.size _ hget
    simp at hp

/-- **`Acyclic (name.sem N)` given `CombDesign (name.sem N)`** (`sv_structure … using hc`): the
comb profile in hand replaces the one-driver obligation (it IS the one-driver rule on the
instantiated design). The in-range obligation stays: an out-of-range element select lowers to a
no-op window, so `CombDesign` alone does not pin the promised windows. -/
theorem acyclic_using {d : PDesign} {s : Summary} (hs : d.summary = .ok s) {args : List Int}
    {σ : String → Int} {env : IEnv} (harity : args.length = d.params.length)
    (h1 : d.paramEnv2 args = .ok env) (hag : Agrees σ env s.params) (hok : s.StructOk)
    (hauto : s.AutoObl σ args) (hin : s.InRangeObl σ)
    (hc : CombDesign (d.instantiateGD2 args))
    {R : SiteId → SiteId → Prop} (hr : s.RankObl' R σ)
    (hrank : ∀ L : List SiteId, ∃ rk : SiteId → Nat, ∀ a ∈ L, ∀ b ∈ L, R b a → rk b < rk a) :
    Acyclic (d.instantiateGD2 args) := by
  obtain ⟨m, hm, hR⟩ := Summary.sound hs harity h1 hag hok hauto hin
  rw [instantiateGD2_eq_of_comb hm hc]
  exact realized_acyclic hR hok hauto hin hr hrank

theorem acyclic_view_using {d : PDesign} {s : Summary} {args : List Int} {env : IEnv}
    (hs : d.summary = .ok s) (harity : args.length = d.params.length)
    (h1 : d.paramEnv2 args = .ok env)
    (hag : s.params.map (fun n => env.vals.lookup n) =
      s.params.map (fun n => some (s.val args n)))
    (hok : s.StructOk) (hauto : s.AutoObl (s.val args) args)
    (hin : s.InRangeObl (s.val args))
    (hc : CombDesign (d.instantiateGD2 args))
    (ρ : SiteId → Nat) (hrank : s.RankObl ρ (s.val args)) :
    Acyclic (d.instantiateGD2 args) :=
  acyclic_using hs harity h1 (Agrees_of_map hag) hok hauto hin hc hrank
    (fun _ => ⟨ρ, fun _ _ _ _ h => h⟩)

theorem lex_view_using {d : PDesign} {s : Summary} {args : List Int} {env : IEnv}
    (hs : d.summary = .ok s) (harity : args.length = d.params.length)
    (h1 : d.paramEnv2 args = .ok env)
    (hag : s.params.map (fun n => env.vals.lookup n) =
      s.params.map (fun n => some (s.val args n)))
    (hok : s.StructOk) (hauto : s.AutoObl (s.val args) args)
    (hin : s.InRangeObl (s.val args))
    (hc : CombDesign (d.instantiateGD2 args))
    (κ : SiteId → Key) (hrank : s.LexObl κ (s.val args)) :
    Acyclic (d.instantiateGD2 args) :=
  acyclic_using hs harity h1 (Agrees_of_map hag) hok hauto hin hc hrank
    (fun L => ⟨countRank L κ, fun a _ b hb h => countRank_lt L κ hb h⟩)

/-! ## Rank constructors (design principle 13: ranks over site identities) -/

/-- One-index families (the ripple shape): plain sites by position, family sites by label,
position and the loop index. -/
def rippleRank (plainRank : Nat → Nat) (famRank : String → Nat → Int → Nat) : SiteId → Nat
  | .plain p => plainRank p
  | .fam l p [i] => famRank l p i
  | .fam _ _ _ => 0

@[simp] theorem rippleRank_plain (pr : Nat → Nat) (fr : String → Nat → Int → Nat) (p : Nat) :
    rippleRank pr fr (.plain p) = pr p := rfl

@[simp] theorem rippleRank_fam (pr : Nat → Nat) (fr : String → Nat → Int → Nat) (l : String)
    (p : Nat) (i : Int) : rippleRank pr fr (.fam l p [i]) = fr l p i := rfl

/-- Two-index families, lexicographic, injected into `Nat` by `i * W + j` for `j < W` (the direct
construction; `sv_structure (lexRank := …)` needs no bound and no multiplication). -/
def lexRank (W : Nat) (plainRank : Nat → Nat) : SiteId → Nat
  | .plain p => plainRank p
  | .fam _ _ [i, j] => i.toNat * W + j.toNat
  | .fam _ _ _ => 0

theorem lexRank_lt {W i j i' j' : Nat} (hj : j < W)
    (h : i < i' ∨ (i = i' ∧ j < j')) : i * W + j < i' * W + j' := by
  rcases h with h | ⟨rfl, h⟩
  · have : (i + 1) * W ≤ i' * W := Nat.mul_le_mul_right W h
    have : (i + 1) * W = i * W + W := by rw [Nat.add_mul, Nat.one_mul]
    omega
  · omega

theorem lexRank_fam_lt {W : Nat} {pr : Nat → Nat} {l l' : String} {p p' : Nat} {i j i' j' : Int}
    (hi : 0 ≤ i) (hj0 : 0 ≤ j) (hi' : 0 ≤ i') (hj'0 : 0 ≤ j') (hj : j < W)
    (h : i < i' ∨ (i = i' ∧ j < j')) :
    lexRank W pr (.fam l p [i, j]) < lexRank W pr (.fam l' p' [i', j']) := by
  show i.toNat * W + j.toNat < i'.toNat * W + j'.toNat
  exact lexRank_lt (by omega) (by omega)

end CombView
end LeanModels.Sv
