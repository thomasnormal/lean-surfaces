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
    exact (disjOne_iff.mp (hd.2.1 a ha)) σ1 h1 σ2 h2 hne
  · rcases pairwise_cases hd.1 ha hb hab with h | h
    · exact (disjOne_iff.mp h) σ1 h1 σ2 h2 hne
    · rw [Win.overlaps_comm]
      exact (disjOne_iff.mp h) σ2 h2 σ1 h1 (fun e => hne e.symm)

/-! ## The further windows of a footprint (WP-G S1b, gate c2)

The extractors `Summary.InRangeObl.more_all`, `Summary.DisjObl.more_all`, `Summary.RankObl'.more_all`
(`CombViewThm.lean`) turn the guarded conjuncts into the plain obligations. -/

/-- The windows of an instance: the target accesses' windows at the valuation. -/
theorem LSite.wins_inst (ls : LSite) (σ : String → Int) (dw : String → Nat) :
    (ls.inst σ dw).wins = (ls.site.tgt :: ls.site.more).map fun a => a.win σ dw := by
  simp [SiteInst.wins, LSite.inst, List.map_map, Function.comp_def]

theorem mem_wins_inst {ls : LSite} {σ : String → Int} {dw : String → Nat} {w : Win} :
    w ∈ (ls.inst σ dw).wins ↔ ∃ a ∈ ls.site.tgt :: ls.site.more, a.win σ dw = w := by
  rw [LSite.wins_inst, List.mem_map]

/-- **The one-driver rule on ALL the windows of two instances**: two instances with different identities drive
disjoint windows, every window of one against every window of the other. -/
theorem insts_disj_wins {s : Summary} {σ : String → Int} {E : IEnv} (hd : s.DisjObl σ) :
    ∀ x ∈ s.insts σ E, ∀ y ∈ s.insts σ E, x.id ≠ y.id →
      ∀ w ∈ x.wins, ∀ w' ∈ y.wins, Win.overlaps w w' = false := by
  intro x hx y hy hne w hw w' hw'
  have hmore := hd.more_all
  obtain ⟨a, ha, σ1, h1, hxa⟩ := mem_insts.mp hx
  obtain ⟨b, hb, σ2, h2, hyb⟩ := mem_insts.mp hy
  subst hxa hyb
  obtain ⟨x0, hx0, rfl⟩ := mem_wins_inst.mp hw
  obtain ⟨y0, hy0, rfl⟩ := mem_wins_inst.mp hw'
  rcases List.mem_cons.mp hy0 with rfl | hy1
  · rcases List.mem_cons.mp hx0 with rfl | hx1
    · exact insts_disj hd _ hx _ hy hne
    · have := hmore.1 b hb a ha x0 hx1 b.site.tgt (List.mem_cons_self ..)
      rw [Win.overlaps_comm]
      exact (Loops.all_iff _ _ _).mp ((Loops.all_iff _ _ _).mp this σ2 h2) σ1 h1 (fun e => hne e.symm)
  · have := hmore.1 a ha b hb y0 hy1 x0 hx0
    exact (Loops.all_iff _ _ _).mp ((Loops.all_iff _ _ _).mp this σ1 h1) σ2 h2 hne

/-- **The windows of ONE instance are pairwise disjoint** (the within-site obligation). -/
theorem insts_within {s : Summary} {σ : String → Int} {E : IEnv} (hd : s.DisjObl σ) :
    ∀ x ∈ s.insts σ E, x.wins.Pairwise fun w w' => Win.overlaps w w' = false := by
  intro x hx
  obtain ⟨a, ha, σ1, h1, hxa⟩ := mem_insts.mp hx
  subst hxa
  have h := (Loops.all_iff _ _ _).mp (hd.more_all.2 a ha) σ1 h1
  rw [LSite.wins_inst]
  exact List.pairwise_map.mpr h

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

/-- **The geometry of every target window of a located site at a reached valuation** (the head and the further
ones): the access is consistent with its declaration, and its window is positive and inside the declared signal. -/
theorem SiteCtx.win_facts {s : Summary} {σ : String → Int} {elems : List (String × Nat)} {ls : LSite}
    {σ' : String → Int} {E' : IEnv} {args : List Int} (hc : SiteCtx s σ elems ls σ' E') (hls : ls ∈ s.lsites)
    (hok : s.StructOk) (hauto : s.AutoObl σ args) :
    ∀ a ∈ ls.site.tgt :: ls.site.more,
      AccGeom σ' (s.DG σ) (s.EW σ) a ∧ (s.find a.name).isSome = true ∧ 0 < (a.win σ' (s.dw σ)).2.2 ∧
        (a.win σ' (s.dw σ)).2.1 + (a.win σ' (s.dw σ)).2.2 ≤ s.dw σ a.name := by
  intro a ha
  obtain ⟨hnodup, hnames, hinput, haff, hpaths, hdecl, hacc, hkeys⟩ := hok
  obtain ⟨-, hauto2, -⟩ := hauto
  have hmem : a ∈ ls.site.tgt :: (ls.site.more ++ ls.site.rds) := by
    rcases List.mem_cons.mp ha with rfl | hm
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ hm)
  have hI : s.InR σ σ' a ∧ ∀ n x, a = .bit n x → x.eval σ' + 1 ≤ (s.dw σ n : Int) := by
    rcases List.mem_cons.mp ha with rfl | hm
    · exact ⟨hc.inw.1, fun n x h => by have := hc.inw.2; rw [h] at this; exact this⟩
    · exact ⟨(hc.inwMore a hm).1, fun n x h => by have := (hc.inwMore a hm).2; rw [h] at this; exact this⟩
  have hg := accGeom_of hc.par hdecl (hacc ls hls a hmem) hI.1 (hauto2 ls hls a hmem)
  have hdn : (s.find a.name).isSome = true := by
    refine find_isSome_of_mem (hnames ls hls _ ?_)
    simp only [TSite.names, List.mem_cons, List.mem_map]
    rcases List.mem_cons.mp ha with rfl | hm
    · exact Or.inl rfl
    · exact Or.inr ⟨a, List.mem_append_left _ hm, rfl⟩
  obtain ⟨hpos, hle⟩ := acc_win_facts (σd := σ) hdn hg hI.2
  exact ⟨hg, hdn, hpos, hle⟩

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
      (∀ n x, ls.site.tgt = .bit n x → x.eval σ' + 1 ≤ (s.dw σ n : Int)) ∧
      ∀ y ∈ ls.site.more, AccGeom σ' (s.DG σ) (s.EW σ) y ∧ (s.find y.name).isSome = true ∧
        (∀ n x, y = .bit n x → x.eval σ' + 1 ≤ (s.dw σ n : Int)) := by
  obtain ⟨ls, hls, σ', hr, rfl⟩ := mem_insts.mp ha
  obtain ⟨hnodup, hnames, hinput, haff, hpaths, hdecl, hacc, hkeys⟩ := hok
  have hpar := reach_par ⟨hnodup, hnames, hinput, haff, hpaths, hdecl, hacc, hkeys⟩ hls hr
  have hin' := (Loops.all_iff _ _ _).mp (hin.1 ls hls) σ' hr
  have hinM := (Loops.all_iff _ _ _).mp (hin.more_all ls hls) σ' hr
  have hdn : (s.find ls.site.tgt.name).isSome = true :=
    find_isSome_of_mem (hnames ls hls _ (by simp [TSite.names]))
  refine ⟨ls, hls, σ', hr, rfl,
    accGeom_of hpar hdecl (hacc ls hls _ (List.mem_cons_self ..)) hin'.1 (hauto.2.1 ls hls _ (List.mem_cons_self ..)),
    hdn, fun n x h => by have := hin'.2; rw [h] at this; exact this, fun y hy => ?_⟩
  have hmem : y ∈ ls.site.tgt :: (ls.site.more ++ ls.site.rds) :=
    List.mem_cons_of_mem _ (List.mem_append_left _ hy)
  have hdn' : (s.find y.name).isSome = true := by
    refine find_isSome_of_mem (hnames ls hls _ ?_)
    simp only [TSite.names, List.mem_cons, List.mem_map]
    exact Or.inr ⟨y, List.mem_append_left _ hy, rfl⟩
  exact ⟨accGeom_of hpar hdecl (hacc ls hls y hmem) (hinM y hy).1 (hauto.2.1 ls hls y hmem), hdn',
    fun n x h => by have := (hinM y hy).2; rw [h] at this; exact this⟩

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
  obtain ⟨ls, hls, σ', hr, rfl, hg, hdn, hbit, -⟩ := inst_geom hok hauto hin ha
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
  obtain ⟨ls, hls, σ', hr, rfl, hg, hdn, hbit, -⟩ := inst_geom hok hauto hin ha
  obtain ⟨hpos, -⟩ := acc_win_facts (σd := σ) hdn hg hbit
  have hni := hok.2.2.1 ls hls ls.site.tgt (List.mem_cons_self ..)
  have hname : (ls.inst σ' (s.dw σ)).win.1 = ls.site.tgt.name :=
    Acc.win_name σ' (s.dw σ) ls.site.tgt
  refine ⟨?_, ?_, hpos, by rw [hname]; exact hni⟩
  · intro ps
    exact Acc.lhs_ne_concat σ' ls.site.tgt ps
  · exact acc_windows hdecl ls.site.tgt hdn

/-- **Every window of an instance is positive and inside its declared signal.** -/
theorem inrange_insts_wins {s : Summary} {σ : String → Int} {E : IEnv} {args : List Int}
    (hok : s.StructOk) (hauto : s.AutoObl σ args) (hin : s.InRangeObl σ) {a : SiteInst}
    (ha : a ∈ s.insts σ E) :
    ∀ w ∈ a.wins, 0 < w.2.2 ∧ ∃ dw, s.DW σ w.1 = some dw ∧ w.2.1 + w.2.2 ≤ dw := by
  intro w hw
  obtain ⟨ls, hls, σ', hr, hxa, hg, hdn, hbit, hmore⟩ := inst_geom hok hauto hin ha
  subst hxa
  obtain ⟨y, hy, rfl⟩ := mem_wins_inst.mp hw
  rcases List.mem_cons.mp hy with rfl | hy1
  · obtain ⟨hpos, hle⟩ := acc_win_facts (σd := σ) hdn hg hbit
    refine ⟨hpos, s.dw σ ls.site.tgt.name, ?_, hle⟩
    rw [Acc.win_name]
    exact DW_eq hdn
  · obtain ⟨hg', hdn', hbit'⟩ := hmore y hy1
    obtain ⟨hpos, hle⟩ := acc_win_facts (σd := σ) hdn' hg' hbit'
    refine ⟨hpos, s.dw σ y.name, ?_, hle⟩
    rw [Acc.win_name]
    exact DW_eq hdn'

/-- **No window of an instance is an input port.** -/
theorem inst_notInput {s : Summary} {σ : String → Int} {E : IEnv} (hok : s.StructOk) {a : SiteInst}
    (ha : a ∈ s.insts σ E) : ∀ w ∈ a.wins, w.1 ∉ s.inputNames := by
  intro w hw
  obtain ⟨ls, hls, σ', hr, hxa⟩ := mem_insts.mp ha
  subst hxa
  obtain ⟨y, hy, rfl⟩ := mem_wins_inst.mp hw
  rw [Acc.win_name]
  exact hok.2.2.1 ls hls y hy

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

/-- The facts the structural proofs read off one footprint `a` and its process `p` in the design `d'`: the process is
an assign to a target whose windows are those of the footprint (one, or several when the site writes several), each
positive and none an input; its right-hand side is loud-free and reads only the footprint's promised windows and
declared names. (`desc_facts` for the instantiated design, `descL_facts` for its lowering.) -/
def PairFacts (s : Summary) (d' : Design2) (a : SiteInst) (p : Process2) : Prop :=
  ∃ (t : Lhs2) (e : Expr2), p = .assign t e ∧ t.windows? d' = some a.wins ∧ (∀ w ∈ a.wins, 0 < w.2.2) ∧
    (∀ w ∈ a.wins, w.1 ∉ s.inputNames) ∧ e.unsupportedFree = true ∧ (∀ r ∈ e.reads, r ∈ a.rd) ∧
    ∀ x ∈ e.idents, x ∈ s.declNames

/-- The footprint of a pair of the list is an instance of the summary. -/
theorem mem_insts_of_map_fst {s : Summary} {σ : String → Int} {E : IEnv} {L : List (SiteInst × Process2)}
    (hLf : L.map Prod.fst = s.insts σ E) {q : SiteInst × Process2} (hq : q ∈ L) : q.1 ∈ s.insts σ E :=
  hLf ▸ List.mem_map.2 ⟨q, hq, rfl⟩

/-- An instantiated old site satisfies `PairFacts`. -/
theorem desc_facts {s : Summary} {σ : String → Int} {E : IEnv} {args : List Int} {d' : Design2}
    (hok : s.StructOk) (hauto : s.AutoObl σ args) (hin : s.InRangeObl σ)
    (hdecl : d'.decls.toList = s.decls.map (DeclT.toDecl σ)) {a : SiteInst}
    (ha : a ∈ s.insts σ E) {p : Process2} (hD : Desc s.declNames a p) : PairFacts s d' a p := by
  obtain ⟨-, hwin, hpos, hni⟩ := inst_facts hok hauto hin hdecl ha
  obtain ⟨e, hpe, hrd, hfree, hid, hmore⟩ := hD
  have hw : a.wins = [a.win] := by simp [SiteInst.wins, hmore]
  refine ⟨a.tgt, e, hpe, by rw [hw]; exact hwin, ?_, ?_, hfree, hrd, hid⟩
  · intro w hw'
    rw [hw, List.mem_singleton] at hw'
    subst hw'
    exact hpos
  · intro w hw'
    rw [hw, List.mem_singleton] at hw'
    subst hw'
    exact hni

/-- **The comb profile from the pair facts**, the core shared by the instantiated design (`realized_comb`) and
its lowering (`realizedL_comb`): the process list of `d'` is the second components of `L`, whose first components
are the instances of the summary, and every pair satisfies `PairFacts`. -/
theorem realized_comb_core {s : Summary} {σ : String → Int} {d' : Design2} {args : List Int} {E : IEnv}
    {L : List (SiteInst × Process2)}
    (hdecl : d'.decls.toList = s.decls.map (DeclT.toDecl σ)) (hLf : L.map Prod.fst = s.insts σ E)
    (hP : d'.processes.toList = L.map Prod.snd) (hdf : ∀ q ∈ L, PairFacts s d' q.1 q.2)
    (hok : s.StructOk) (hauto : s.AutoObl σ args) (hin : s.InRangeObl σ) (hd : s.DisjObl σ) :
    CombDesign d' ∧ ∀ i n lo w, d'.Writes i (n, lo, w) → 0 < w := by
  have hok' := hok
  obtain ⟨hnodup, -, -, -, -, -, -, -⟩ := hok'
  have hget : ∀ (i : Nat) (p : Process2), d'.processes[i]? = some p ↔
      ∃ q : SiteInst × Process2, L[i]? = some q ∧ p = q.2 := by
    intro i p
    rw [← Array.getElem?_toList, hP, List.getElem?_map]
    cases hL : L[i]? with
    | none => simp
    | some q => simp [eq_comm]
  have hmemL : ∀ q : SiteInst × Process2, q ∈ L → q.1 ∈ s.insts σ E :=
    fun q hq => mem_insts_of_map_fst hLf hq
  have hpw : L.Pairwise fun p q => ∀ w ∈ p.1.wins, ∀ w' ∈ q.1.wins, Win.overlaps w w' = false := by
    have h1 : (L.map Prod.fst).Pairwise (fun a b => a.id ≠ b.id) := by
      rw [hLf]; exact ids_pairwise hok
    rw [List.pairwise_map] at h1
    exact h1.imp_of_mem (fun {p q} hp hq hne => insts_disj_wins hd _ (hmemL p hp) _ (hmemL q hq) hne)
  have hwr : ∀ {i wn}, d'.Writes i wn → ∃ q, L[i]? = some q ∧ wn ∈ q.1.wins := by
    rintro i wn ⟨t, e, hp, hw⟩
    obtain ⟨q, hq, hqe⟩ := (hget i _).mp hp
    obtain ⟨t', e', hpe, hwin, -⟩ := hdf q (List.mem_of_getElem? hq)
    rw [hpe] at hqe
    simp only [Process2.assign.injEq] at hqe
    obtain ⟨rfl, rfl⟩ := hqe
    refine ⟨q, hq, ?_⟩
    rw [Lhs2.wins_of_windows? hwin] at hw
    exact hw
  have hpos : ∀ i n lo w, d'.Writes i (n, lo, w) → 0 < w := by
    intro i n lo w hw
    obtain ⟨q, hq, hwq⟩ := hwr hw
    obtain ⟨-, -, -, -, hp, -⟩ := hdf q (List.mem_of_getElem? hq)
    exact hp _ hwq
  refine ⟨?_, hpos⟩
  refine
    { nodup := ?_, assign := ?_, inWidth := ?_, notInput := ?_, disjoint := ?_,
      selfDisjoint := ?_, rhsFree := ?_, rhsDeclared := ?_, initWidth := ?_,
      inFourState := ?_ }
  · rw [hdecl]
    simpa [List.map_map, Function.comp_def, Summary.declNames] using hnodup
  · intro i p hp
    obtain ⟨q, hq, rfl⟩ := (hget i p).mp hp
    obtain ⟨t, e, hpe, hwin, -⟩ := hdf q (List.mem_of_getElem? hq)
    exact ⟨t, e, q.1.wins, hpe, hwin⟩
  · intro i n lo w hw
    obtain ⟨q, hq, hwq⟩ := hwr hw
    obtain ⟨-, dw, hdw, hle⟩ := inrange_insts_wins hok hauto hin (hmemL q (List.mem_of_getElem? hq)) _ hwq
    exact ⟨dw, by rw [declWidth_eq hdecl]; exact hdw, hle⟩
  · intro n hn
    obtain ⟨i, lo, w, hw⟩ := hn
    obtain ⟨q, hq, hwq⟩ := hwr hw
    obtain ⟨-, -, -, -, -, hni, -⟩ := hdf q (List.mem_of_getElem? hq)
    rw [Realized.inputNames hdecl]
    exact hni _ hwq
  · intro i j wi wj hij hi hj
    obtain ⟨qi, hqi, hwi⟩ := hwr hi
    obtain ⟨qj, hqj, hwj⟩ := hwr hj
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · exact pairwise_getElem? hpw h hqi hqj wi hwi wj hwj
    · rw [Win.overlaps_comm]
      exact pairwise_getElem? hpw h hqj hqi wj hwj wi hwi
  · intro i t e hp
    obtain ⟨q, hq, hqe⟩ := (hget i _).mp hp
    obtain ⟨t', e', hpe, hwin, -⟩ := hdf q (List.mem_of_getElem? hq)
    rw [hpe] at hqe
    simp only [Process2.assign.injEq] at hqe
    obtain ⟨rfl, rfl⟩ := hqe
    rw [Lhs2.wins_of_windows? hwin]
    exact insts_within hd _ (hmemL q (List.mem_of_getElem? hq))
  · intro i t e hp
    obtain ⟨q, hq, hqe⟩ := (hget i _).mp hp
    obtain ⟨t', e', hpe, -, -, -, hfree, -⟩ := hdf q (List.mem_of_getElem? hq)
    rw [hpe] at hqe
    simp only [Process2.assign.injEq] at hqe
    obtain ⟨rfl, rfl⟩ := hqe
    exact hfree
  · intro i t e hp x hx
    obtain ⟨q, hq, hqe⟩ := (hget i _).mp hp
    obtain ⟨t', e', hpe, -, -, -, -, -, hid⟩ := hdf q (List.mem_of_getElem? hq)
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

/-- `Realized` + obligations ⇒ the comb profile (and positive write windows). -/
theorem realized_comb {s : Summary} {σ : String → Int} {m : Design2} {args : List Int}
    (hR : Realized s σ m) (hok : s.StructOk) (hauto : s.AutoObl σ args) (hin : s.InRangeObl σ)
    (hd : s.DisjObl σ) :
    CombDesign m ∧ ∀ i n lo w, m.Writes i (n, lo, w) → 0 < w := by
  obtain ⟨hdecl, E, L, hLf, hP, hdesc⟩ := hR
  exact realized_comb_core hdecl hLf hP
    (fun q hq => desc_facts hok hauto hin hdecl (mem_insts_of_map_fst hLf hq) (hdesc q hq)) hok hauto hin hd

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
  exact (Loops.all_iff _ _ _).mp ((Loops.all_iff _ _ _).mp (hr.1 la hla r' hr' lb hw) σ1 h1) σ2 h2 hov

/-- **The rank obligation, on instances, against ALL the windows of the writer.** -/
theorem rank_insts_all {s : Summary} {σ : String → Int} {E : IEnv} {R : SiteId → SiteId → Prop}
    (hr : s.RankObl' R σ) {a b : SiteInst} (ha : a ∈ s.insts σ E) (hb : b ∈ s.insts σ E)
    {r : ReadWin} (hra : r ∈ a.rd) {w : Win} (hw : w ∈ b.wins) (hov : ReadWin.overlaps r w = true) :
    R b.id a.id := by
  have hmore := hr.more_all
  obtain ⟨la, hla, σ1, h1, hxa⟩ := mem_insts.mp ha
  obtain ⟨lb, hlb, σ2, h2, hyb⟩ := mem_insts.mp hb
  subst hxa hyb
  obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hra
  obtain ⟨y, hy, rfl⟩ := mem_wins_inst.mp hw
  rcases List.mem_cons.mp hy with rfl | hy1
  · exact rank_insts hr ha hb hra hov
  · have hname : y.name = r'.name := by
      have h1' := ReadWin.overlaps_name hov
      rw [Acc.rd_name, Acc.win_name] at h1'
      exact h1'.symm
    exact (Loops.all_iff _ _ _).mp ((Loops.all_iff _ _ _).mp (hmore lb hlb y hy1 la hla r' hr' hname) σ1 h1)
      σ2 h2 hov

/-- **Acyclicity from the pair facts and a rank**, the core shared by the instantiated design
(`realized_acyclic`) and its lowering (`realizedL_acyclic`). -/
theorem realized_acyclic_core {s : Summary} {σ : String → Int} {d' : Design2} {E : IEnv}
    {L : List (SiteInst × Process2)} {R : SiteId → SiteId → Prop}
    (hLf : L.map Prod.fst = s.insts σ E) (hP : d'.processes.toList = L.map Prod.snd)
    (hdf : ∀ q ∈ L, PairFacts s d' q.1 q.2) (hr : s.RankObl' R σ)
    (hrank : ∀ L : List SiteId, ∃ rk : SiteId → Nat, ∀ a ∈ L, ∀ b ∈ L, R b a → rk b < rk a) :
    Acyclic d' := by
  have hget : ∀ (i : Nat) (p : Process2), d'.processes[i]? = some p ↔
      ∃ q : SiteInst × Process2, L[i]? = some q ∧ p = q.2 := by
    intro i p
    rw [← Array.getElem?_toList, hP, List.getElem?_map]
    cases hL : L[i]? with
    | none => simp
    | some q => simp [eq_comm]
  have hmemL : ∀ q : SiteInst × Process2, q ∈ L → q.1 ∈ s.insts σ E :=
    fun q hq => mem_insts_of_map_fst hLf hq
  obtain ⟨rk, hrk⟩ := hrank (L.map fun q => q.1.id)
  refine ⟨fun j => match L[j]? with | some q => rk q.1.id | none => 0, ?_⟩
  intro i j ti ei tj ej wj hpi hpj hwj ⟨r, hrE, hov⟩
  obtain ⟨qi, hqi, hqie⟩ := (hget i _).mp hpi
  obtain ⟨qj, hqj, hqje⟩ := (hget j _).mp hpj
  obtain ⟨ti', ei', hpei, -, -, -, -, hrd, -⟩ := hdf qi (List.mem_of_getElem? hqi)
  obtain ⟨tj', ej', hpej, hwinj, -⟩ := hdf qj (List.mem_of_getElem? hqj)
  rw [hpei] at hqie
  rw [hpej] at hqje
  simp only [Process2.assign.injEq] at hqie hqje
  obtain ⟨rfl, rfl⟩ := hqie
  obtain ⟨rfl, rfl⟩ := hqje
  have hw : wj ∈ qj.1.wins := by
    rw [Lhs2.wins_of_windows? hwinj] at hwj
    exact hwj
  simp only [hqi, hqj]
  have hR' := rank_insts_all hr (hmemL qi (List.mem_of_getElem? hqi))
    (hmemL qj (List.mem_of_getElem? hqj)) (hrd r hrE) hw hov
  exact hrk qi.1.id (List.mem_map.2 ⟨qi, List.mem_of_getElem? hqi, rfl⟩) qj.1.id
    (List.mem_map.2 ⟨qj, List.mem_of_getElem? hqj, rfl⟩) hR'

theorem realized_acyclic {s : Summary} {σ : String → Int} {m : Design2} {args : List Int}
    {R : SiteId → SiteId → Prop}
    (hR : Realized s σ m) (hok : s.StructOk) (hauto : s.AutoObl σ args) (hin : s.InRangeObl σ)
    (hr : s.RankObl' R σ)
    (hrank : ∀ L : List SiteId, ∃ rk : SiteId → Nat, ∀ a ∈ L, ∀ b ∈ L, R b a → rk b < rk a) :
    Acyclic m := by
  obtain ⟨hdecl, E, L, hLf, hP, hdesc⟩ := hR
  exact realized_acyclic_core hLf hP
    (fun q hq => desc_facts hok hauto hin hdecl (mem_insts_of_map_fst hLf hq) (hdesc q hq)) hr hrank

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
    (h : ns.map (fun n => env.intVal? n) = ns.map (fun n => some (σ n))) :
    Agrees σ env ns := by
  intro n hn
  exact List.map_inj_left.mp h n hn

/-- `comb_of_summary` at the canonical valuation `s.val args` (the parameters zipped with the
arguments, then the localparams: `σL (params.zip args)` for a design without any), the environment
check in a `rfl`-provable form. -/
theorem comb_view {d : PDesign} {s : Summary} {args : List Int} {env : IEnv}
    (hs : d.summary = .ok s) (harity : args.length = d.params.length)
    (h1 : d.paramEnv2 args = .ok env)
    (hag : s.params.map (fun n => env.intVal? n) =
      s.params.map (fun n => some (s.val args n)))
    (hok : s.StructOk) (hauto : s.AutoObl (s.val args) args)
    (hin : s.InRangeObl (s.val args)) (hdisj : s.DisjObl (s.val args)) :
    CombDesign (d.instantiateGD2 args) :=
  comb_of_summary hs harity h1 (Agrees_of_map hag) hok hauto hin hdisj

theorem acyclic_view {d : PDesign} {s : Summary} {args : List Int} {env : IEnv}
    (hs : d.summary = .ok s) (harity : args.length = d.params.length)
    (h1 : d.paramEnv2 args = .ok env)
    (hag : s.params.map (fun n => env.intVal? n) =
      s.params.map (fun n => some (s.val args n)))
    (hok : s.StructOk) (hauto : s.AutoObl (s.val args) args)
    (hin : s.InRangeObl (s.val args)) (hdisj : s.DisjObl (s.val args))
    (ρ : SiteId → Nat) (hrank : s.RankObl ρ (s.val args)) :
    Acyclic (d.instantiateGD2 args) :=
  acyclic_of_summary hs harity h1 (Agrees_of_map hag) hok hauto hin hdisj hrank

theorem lex_view {d : PDesign} {s : Summary} {args : List Int} {env : IEnv}
    (hs : d.summary = .ok s) (harity : args.length = d.params.length)
    (h1 : d.paramEnv2 args = .ok env)
    (hag : s.params.map (fun n => env.intVal? n) =
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
    (hag : s.params.map (fun n => env.intVal? n) =
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
    (hag : s.params.map (fun n => env.intVal? n) =
      s.params.map (fun n => some (s.val args n)))
    (hok : s.StructOk) (hauto : s.AutoObl (s.val args) args)
    (hin : s.InRangeObl (s.val args))
    (hc : CombDesign (d.instantiateGD2 args))
    (κ : SiteId → Key) (hrank : s.LexObl κ (s.val args)) :
    Acyclic (d.instantiateGD2 args) :=
  acyclic_using hs harity h1 (Agrees_of_map hag) hok hauto hin hc hrank
    (fun L => ⟨countRank L κ, fun a _ b hb h => countRank_lt L κ hb h⟩)

/-! ## WP-P (P1): the bundle `CombDesign ∧ Acyclic`, and the declarations of a comb design

`sv_structure` on a goal `CombDesign (X.sem N) ∧ Acyclic (X.sem N)` derives both from ONE
application of `Summary.sound` and ONE round of the obligation normalizations (`auto`, `inRange`,
`driverDisjoint`, `rankDecreases`). Proved separately, `CombDesign` and `Acyclic` each re-normalize the
first two (and `Acyclic` without `using hc` the third): measured at about a sixth of the CPU time of a
2-D reference proof (svgolf/PROVING.md, "Proof effort").

`decls_view` is the theorem under `sv_interface`: the declarations of `name.sem N` are the summary's,
read off the `CombDesign` profile alone (no `AutoObl`, no `InRangeObl`: the profile already says the
instantiation succeeded). -/

/-- `CombDesign` and `Acyclic` of `name.sem N` from one set of obligations and a `Nat` rank. -/
theorem comb_acyclic_of_summary {d : PDesign} {s : Summary} (hs : d.summary = .ok s) {args : List Int}
    {σ : String → Int} {env : IEnv} (harity : args.length = d.params.length)
    (h1 : d.paramEnv2 args = .ok env) (hag : Agrees σ env s.params) (hok : s.StructOk)
    (hauto : s.AutoObl σ args) (hin : s.InRangeObl σ) (hdisj : s.DisjObl σ)
    {ρ : SiteId → Nat} (hrank : s.RankObl ρ σ) :
    CombDesign (d.instantiateGD2 args) ∧ Acyclic (d.instantiateGD2 args) := by
  obtain ⟨m, hm, hR⟩ := Summary.sound hs harity h1 hag hok hauto hin
  obtain ⟨hc, hpos⟩ := realized_comb hR hok hauto hin hdisj
  rw [PDesign.instantiateGD2_of_combDesign hm hc hpos]
  exact ⟨hc, realized_acyclic hR hok hauto hin hrank (fun _ => ⟨ρ, fun _ _ _ _ h => h⟩)⟩

/-- … from a LEXICOGRAPHIC key. -/
theorem comb_acyclic_of_lex {d : PDesign} {s : Summary} (hs : d.summary = .ok s) {args : List Int}
    {σ : String → Int} {env : IEnv} (harity : args.length = d.params.length)
    (h1 : d.paramEnv2 args = .ok env) (hag : Agrees σ env s.params) (hok : s.StructOk)
    (hauto : s.AutoObl σ args) (hin : s.InRangeObl σ) (hdisj : s.DisjObl σ)
    {κ : SiteId → Key} (hrank : s.LexObl κ σ) :
    CombDesign (d.instantiateGD2 args) ∧ Acyclic (d.instantiateGD2 args) := by
  obtain ⟨m, hm, hR⟩ := Summary.sound hs harity h1 hag hok hauto hin
  obtain ⟨hc, hpos⟩ := realized_comb hR hok hauto hin hdisj
  rw [PDesign.instantiateGD2_of_combDesign hm hc hpos]
  exact ⟨hc, realized_acyclic hR hok hauto hin hrank
    (fun L => ⟨countRank L κ, fun a _ b hb h => countRank_lt L κ hb h⟩)⟩

/-- The tactic's form of `comb_acyclic_of_summary` (valuation `s.val args`, `rfl`-provable environment
check, as `comb_view`). -/
theorem comb_acyclic_view {d : PDesign} {s : Summary} {args : List Int} {env : IEnv}
    (hs : d.summary = .ok s) (harity : args.length = d.params.length)
    (h1 : d.paramEnv2 args = .ok env)
    (hag : s.params.map (fun n => env.intVal? n) =
      s.params.map (fun n => some (s.val args n)))
    (hok : s.StructOk) (hauto : s.AutoObl (s.val args) args)
    (hin : s.InRangeObl (s.val args)) (hdisj : s.DisjObl (s.val args))
    (ρ : SiteId → Nat) (hrank : s.RankObl ρ (s.val args)) :
    CombDesign (d.instantiateGD2 args) ∧ Acyclic (d.instantiateGD2 args) :=
  comb_acyclic_of_summary hs harity h1 (Agrees_of_map hag) hok hauto hin hdisj hrank

/-- … with a lexicographic key. -/
theorem comb_lex_view {d : PDesign} {s : Summary} {args : List Int} {env : IEnv}
    (hs : d.summary = .ok s) (harity : args.length = d.params.length)
    (h1 : d.paramEnv2 args = .ok env)
    (hag : s.params.map (fun n => env.intVal? n) =
      s.params.map (fun n => some (s.val args n)))
    (hok : s.StructOk) (hauto : s.AutoObl (s.val args) args)
    (hin : s.InRangeObl (s.val args)) (hdisj : s.DisjObl (s.val args))
    (κ : SiteId → Key) (hrank : s.LexObl κ (s.val args)) :
    CombDesign (d.instantiateGD2 args) ∧ Acyclic (d.instantiateGD2 args) :=
  comb_acyclic_of_lex hs harity h1 (Agrees_of_map hag) hok hauto hin hdisj hrank

theorem errorDesign_not_comb (n m : String) : ¬ CombDesign (Design2.errorDesign n m) := by
  intro hc
  obtain ⟨t, e, ws, hp, -⟩ := hc.assign 0 (Process2.unsupported "Instantiate" m)
    (by simp [Design2.errorDesign])
  cases hp

/-- A comb design in the family is the successful instantiation: `CombDesign` rules out the loud
error designs (`timeout`, `unsupported`) that `instantiateGD2` collapses failures into. -/
theorem instantiate2_ok_of_comb {d : PDesign} {args : List Int}
    (hc : CombDesign (d.instantiateGD2 args)) :
    ∃ m, d.instantiate2 args (PDesign.surfaceFuel args) = .ok m := by
  unfold PDesign.instantiateGD2 PDesign.instantiateG2 at hc
  cases h : d.instantiate2 args (PDesign.surfaceFuel args) with
  | ok m => exact ⟨m, rfl⟩
  | timeout =>
    exfalso
    rw [h] at hc
    exact errorDesign_not_comb _ _ hc
  | unsupported msg =>
    exfalso
    rw [h] at hc
    exact errorDesign_not_comb _ _ hc

/-- **The declarations of a comb design of the fragment** are the summary's, evaluated at the
valuation. Only the parameter stage (`h1`, `hag`) and the structural check (`hok`) are needed: the
profile `hc` says the instantiation succeeded, and `buildDecls_summary` is the declaration half of
`Summary.sound`. -/
theorem decls_of_comb {d : PDesign} {s : Summary} (hs : d.summary = .ok s) {args : List Int}
    {σ : String → Int} {env : IEnv} (h1 : d.paramEnv2 args = .ok env)
    (hag : Agrees σ env s.params) (hok : s.StructOk)
    (hc : CombDesign (d.instantiateGD2 args)) :
    (d.instantiateGD2 args).decls.toList = s.decls.map (DeclT.toDecl σ) := by
  obtain ⟨m, hm⟩ := instantiate2_ok_of_comb hc
  rw [instantiateGD2_eq_of_comb hm hc]
  obtain ⟨env', decls, elems, gens, h1', h2, -, -, -, hdecls, -⟩ :=
    PDesign.instantiate2_processes hm
  rw [hdecls]
  rw [h1] at h1'
  have henv : env = env' := Res.ok.inj h1'
  subst henv
  obtain ⟨-, -, -, -, hsd, -, -, -⟩ := summary_spec hs
  obtain ⟨-, -, -, -, -, hdecl, -, -⟩ := hok
  have hagd : ∀ dt ∈ s.decls, ∀ n ∈ dt.affNames, env.intVal? n = some (σ n) :=
    fun dt hdt n hn => hag n (hdecl dt hdt n hn)
  have h2' := buildDecls_summary (σ := σ) d.decls s.decls hsd env hagd
  rw [h2] at h2'
  exact Res.ok.inj h2'

/-- The tactic's form of `decls_of_comb` (valuation `s.val args`). -/
theorem decls_view {d : PDesign} {s : Summary} {args : List Int} {env : IEnv}
    (hs : d.summary = .ok s) (h1 : d.paramEnv2 args = .ok env)
    (hag : s.params.map (fun n => env.intVal? n) =
      s.params.map (fun n => some (s.val args n)))
    (hok : s.StructOk) (hc : CombDesign (d.instantiateGD2 args)) :
    (d.instantiateGD2 args).decls.toList = s.decls.map (DeclT.toDecl (s.val args)) :=
  decls_of_comb hs h1 (Agrees_of_map hag) hok hc

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
