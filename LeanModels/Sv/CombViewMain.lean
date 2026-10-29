import LeanModels.Sv.CombViewSound

/-!
# `sv_structure`, stage 4: `CombDesign` and `Acyclic` of `name.sem N` from the obligations

The list-level half: from a design that REALIZES a summary (`Summary.sound`) and the obligations
(`InRangeObl`, `DisjObl`, `RankObl`) to the comb profile and the rank certificate. Everything is
proved on the closed-form list `statics ++ range.flatMap body`.

* `comb_of_summary`   : `CombDesign (d.instantiateGD2 args)`
* `acyclic_of_summary`: `Acyclic   (d.instantiateGD2 args)`

(`d.instantiateGD2 args` is `name.sem` of `load_design_sv2`: `instantiateD2` under the one-driver
rule; the rule is the disjointness obligation, `PDesign.instantiateGD2_of_combDesign`.)
-/

namespace LeanModels.Sv
namespace CombView

theorem pairwise_intRange {P : Int → Int → Prop} : ∀ (n : Nat) (c0 : Int),
    (intRange c0 n).Pairwise P ↔ ∀ i k, c0 ≤ i → i < k → k < c0 + n → P i k
  | 0, c0 => by
      simp only [intRange, List.Pairwise.nil, true_iff]
      intro i k hi hik hk
      omega
  | n + 1, c0 => by
      rw [intRange, List.pairwise_cons, pairwise_intRange n (c0 + 1)]
      constructor
      · rintro ⟨h1, h2⟩ i k hi hik hk
        by_cases hic : i = c0
        · subst hic
          exact h1 k (mem_intRange.2 ⟨by omega, by omega⟩)
        · exact h2 i k (by omega) hik (by omega)
      · intro h
        refine ⟨fun k hk => ?_, fun i k hi hik hk => h i k (by omega) hik (by omega)⟩
        rw [mem_intRange] at hk
        exact h c0 k (Int.le_refl c0) (by omega) (by omega)

theorem mem_famInsts {f : TFam} {σ : String → Int} {dw : String → Nat} {b : SiteInst} :
    b ∈ f.insts σ dw ↔ ∃ i, f.Rng σ i ∧ ∃ st ∈ f.body,
      b = st.inst (bindσ f.g i σ) dw (.fam f.label st.pos [i]) := by
  simp only [TFam.insts, List.mem_flatMap, List.mem_map, TFam.mem_range]
  constructor
  · rintro ⟨i, hi, st, hst, rfl⟩
    exact ⟨i, hi, st, hst, rfl⟩
  · rintro ⟨i, hi, st, hst, rfl⟩
    exact ⟨i, hi, st, hst, rfl⟩

theorem mem_insts {s : Summary} {σ : String → Int} {a : SiteInst} (h : a ∈ s.insts σ) :
    (∃ st ∈ s.statics, a = st.inst σ (s.dw σ) (.plain st.pos)) ∨
    (∃ f, s.fam = some f ∧ ∃ i, f.Rng σ i ∧ ∃ st ∈ f.body,
      a = st.inst (bindσ f.g i σ) (s.dw σ) (.fam f.label st.pos [i])) := by
  unfold Summary.insts at h
  rw [List.mem_append] at h
  rcases h with h | h
  · obtain ⟨st, hst, rfl⟩ := List.mem_map.mp h
    exact Or.inl ⟨st, hst, rfl⟩
  · cases hfm : s.fam with
    | none => simp [hfm] at h
    | some f =>
      simp only [hfm] at h
      exact Or.inr ⟨f, rfl, mem_famInsts.mp h⟩

theorem insts_pairwise {s : Summary} {σ : String → Int} (hd : s.DisjObl σ) :
    (s.insts σ).Pairwise fun a b => Win.overlaps a.win b.win = false := by
  obtain ⟨hss, hfam⟩ := hd
  unfold Summary.insts
  rw [List.pairwise_append]
  refine ⟨?_, ?_, ?_⟩
  · rw [List.pairwise_map]
    exact hss
  · cases hfm : s.fam with
    | none => simp
    | some f =>
      have hf : f ∈ s.fam.toList := by simp [hfm]
      obtain ⟨-, hwithin, hcross⟩ := hfam f hf
      simp only [TFam.insts]
      rw [List.pairwise_flatMap]
      refine ⟨fun i hi => ?_, ?_⟩
      · rw [List.pairwise_map]
        exact hwithin i (TFam.mem_range.mp hi)
      · rw [TFam.range, pairwise_intRange]
        intro i k hi hik hk x hx y hy
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hy
        exact hcross i ⟨hi, by omega⟩ k ⟨by omega, by omega⟩ hik a ha b hb
  · intro a ha b hb
    obtain ⟨st, hst, rfl⟩ := List.mem_map.mp ha
    cases hfm : s.fam with
    | none => simp [hfm] at hb
    | some f =>
      simp only [hfm] at hb
      obtain ⟨i, hi, st', hst', rfl⟩ := mem_famInsts.mp hb
      have hf : f ∈ s.fam.toList := by simp [hfm]
      exact (hfam f hf).1 st hst i hi st' hst'

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

theorem inrange_insts {s : Summary} {σ : String → Int} (hok : s.StructOk)
    (hin : s.InRangeObl σ) {a : SiteInst} (ha : a ∈ s.insts σ) :
    ∃ dw, s.DW σ a.win.1 = some dw ∧ a.win.2.1 + a.win.2.2 ≤ dw := by
  obtain ⟨-, hnames, -, -, -, -, harr⟩ := hok
  have key : ∀ (st : TSite) (σs : String → Int), st ∈ s.sites → s.InWin σ σs st →
      ∃ dw, s.DW σ (st.tgt.win σs (s.dw σ)).1 = some dw ∧
        (st.tgt.win σs (s.dw σ)).2.1 + (st.tgt.win σs (s.dw σ)).2.2 ≤ dw := by
    intro st σs hst hw
    have hdn : (s.find st.tgt.name).isSome = true :=
      find_isSome_of_mem (hnames st hst _ (by simp [TSite.names]))
    cases ht : st.tgt with
    | whole n =>
      rw [ht] at hdn
      exact ⟨s.dw σ n, DW_eq hdn, by simp [TTgt.win]⟩
    | bit n a =>
      rw [ht] at hdn
      simp only [Summary.InWin, ht] at hw
      exact ⟨s.dw σ n, DW_eq hdn, by simp only [TTgt.win]; omega⟩
    | arr n a =>
      rw [ht] at hdn
      have hnn : s.arrOk n = true := harr st hst n (by simp [TSite.arrNames, ht])
      obtain ⟨m, hm, hdw⟩ := ad_dw (σ := σ) hnn
      simp only [Summary.InWin, ht, hm, Option.getD_some] at hw
      exact ⟨s.dw σ n, DW_eq hdn, by simp only [TTgt.win]; omega⟩
  rcases mem_insts ha with ⟨st, hst, rfl⟩ | ⟨f, hfm, i, hi, st, hst, rfl⟩
  · exact key st σ (by simp [Summary.sites, hst]) (hin.1 st hst)
  · have hf : f ∈ s.fam.toList := by simp [hfm]
    exact key st (bindσ f.g i σ) (by simp [Summary.sites, Summary.famSites, hfm, hst])
      (hin.2 f hf i hi st hst)

theorem declWidth_eq {s : Summary} {σ : String → Int} {m : Design2}
    (hdecl : m.decls.toList = s.decls.map (DeclT.toDecl σ)) (n : String) :
    m.declWidth n = s.DW σ n := by
  simp [Design2.declWidth, hdecl, Summary.DW, Summary.find, List.find?_map, Function.comp_def,
    Option.map_map]

/-- The window facts of one footprint. -/
theorem inst_facts {s : Summary} {σ : String → Int} {m : Design2} (hok : s.StructOk)
    (hdecl : m.decls.toList = s.decls.map (DeclT.toDecl σ)) {a : SiteInst}
    (ha : a ∈ s.insts σ) :
    (∀ ps, a.tgt ≠ .concat ps) ∧ a.tgt.windows? m = some [a.win] ∧ 0 < a.win.2.2 ∧
      a.win.1 ∉ s.inputNames := by
  obtain ⟨-, hnames, hinput, -⟩ := hok
  have key : ∀ (st : TSite) (σs : String → Int) (id : SiteId), st ∈ s.sites →
      (∀ ps, (st.inst σs (s.dw σ) id).tgt ≠ .concat ps) ∧
      (st.inst σs (s.dw σ) id).tgt.windows? m = some [(st.inst σs (s.dw σ) id).win] ∧
      0 < (st.inst σs (s.dw σ) id).win.2.2 ∧
      (st.inst σs (s.dw σ) id).win.1 ∉ s.inputNames := by
    intro st σs id hst
    have hdn : (s.find st.tgt.name).isSome = true :=
      find_isSome_of_mem (hnames st hst _ (by simp [TSite.names]))
    have hni := hinput st hst
    cases ht : st.tgt with
    | whole n =>
      rw [ht] at hdn hni
      simp only [TTgt.name] at hdn hni
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro ps; simp [TSite.inst, TTgt.lhs, ht]
      · simp [TSite.inst, TTgt.lhs, TTgt.win, ht, declWidth_eq hdecl, DW_eq hdn]
      · simpa [TSite.inst, TTgt.win, ht] using dw_pos (σ := σ) hdn
      · simpa [TSite.inst, TTgt.win, ht, TTgt.name] using hni
    | bit n a =>
      rw [ht] at hni
      simp only [TTgt.name] at hni
      exact ⟨by intro ps; simp [TSite.inst, TTgt.lhs, ht],
        by simp [TSite.inst, TTgt.lhs, TTgt.win, ht],
        by simp [TSite.inst, TTgt.win, ht],
        by simpa [TSite.inst, TTgt.win, ht, TTgt.name] using hni⟩
    | arr n a =>
      rw [ht] at hni
      simp only [TTgt.name] at hni
      exact ⟨by intro ps; simp [TSite.inst, TTgt.lhs, ht],
        by simp [TSite.inst, TTgt.lhs, TTgt.win, ht],
        by simp [TSite.inst, TTgt.win, ht],
        by simpa [TSite.inst, TTgt.win, ht, TTgt.name] using hni⟩
  rcases mem_insts ha with ⟨st, hst, rfl⟩ | ⟨f, hfm, i, hi, st, hst, rfl⟩
  · exact key st σ _ (by simp [Summary.sites, hst])
  · exact key st _ _ (by simp [Summary.sites, Summary.famSites, hfm, hst])

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
theorem realized_comb {s : Summary} {σ : String → Int} {m : Design2} (hR : Realized s σ m)
    (hok : s.StructOk) (hin : s.InRangeObl σ) (hd : s.DisjObl σ) :
    CombDesign m ∧ ∀ i n lo w, m.Writes i (n, lo, w) → 0 < w := by
  obtain ⟨hdecl, L, hLf, hP, hdesc⟩ := hR
  have hok' := hok
  obtain ⟨hnodup, -, -, -, -, -, -⟩ := hok'
  have hget : ∀ (i : Nat) (p : Process2), m.processes[i]? = some p ↔ ∃ q : SiteInst × Process2, L[i]? = some q ∧ p = q.2 := by
    intro i p
    rw [← Array.getElem?_toList, hP, List.getElem?_map]
    cases hL : L[i]? with
    | none => simp
    | some q => simp [eq_comm]
  have hmemL : ∀ q : SiteInst × Process2, q ∈ L → q.1 ∈ s.insts σ :=
    fun q hq => hLf ▸ List.mem_map.2 ⟨q, hq, rfl⟩
  have hfacts := fun (q : SiteInst × Process2) (hq : q ∈ L) => inst_facts hok hdecl (hmemL q hq)
  have hpw : L.Pairwise fun p q => Win.overlaps p.1.win q.1.win = false := by
    have := insts_pairwise hd
    rw [← hLf, List.pairwise_map] at this
    exact this
  -- writes of process `i` are the single window of footprint `L[i]`
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
    obtain ⟨dw, hdw, hle⟩ := inrange_insts hok hin (hmemL q (List.mem_of_getElem? hq))
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

theorem rank_insts {s : Summary} {ρ : SiteId → Nat} {σ : String → Int} (hr : s.RankObl ρ σ)
    {a b : SiteInst} (ha : a ∈ s.insts σ) (hb : b ∈ s.insts σ) {r : ReadWin} (hra : r ∈ a.rd)
    (hov : ReadWin.overlaps r b.win = true) : ρ b.id < ρ a.id := by
  obtain ⟨hss, hfam⟩ := hr
  rcases mem_insts ha with ⟨sa, hsa, rfl⟩ | ⟨f, hfm, i, hi, sa, hsa, rfl⟩ <;>
  rcases mem_insts hb with ⟨sb, hsb, rfl⟩ | ⟨f', hfm', k, hk, sb, hsb, rfl⟩
  · obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hra
    exact hss sa hsa sb hsb r' hr' hov
  · obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hra
    exact (hfam f' (by simp [hfm'])).1 sa hsa k hk sb hsb r' hr' hov
  · obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hra
    exact (hfam f (by simp [hfm])).2.1 i hi sa hsa sb hsb r' hr' hov
  · rw [hfm] at hfm'
    cases hfm'
    obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hra
    exact (hfam f (by simp [hfm])).2.2 i hi k hk sa hsa sb hsb r' hr' hov

theorem realized_acyclic {s : Summary} {ρ : SiteId → Nat} {σ : String → Int} {m : Design2}
    (hR : Realized s σ m) (hok : s.StructOk) (hr : s.RankObl ρ σ) : Acyclic m := by
  obtain ⟨hdecl, L, hLf, hP, hdesc⟩ := hR
  have hget : ∀ (i : Nat) (p : Process2), m.processes[i]? = some p ↔ ∃ q : SiteInst × Process2, L[i]? = some q ∧ p = q.2 := by
    intro i p
    rw [← Array.getElem?_toList, hP, List.getElem?_map]
    cases hL : L[i]? with
    | none => simp
    | some q => simp [eq_comm]
  have hmemL : ∀ q : SiteInst × Process2, q ∈ L → q.1 ∈ s.insts σ :=
    fun q hq => hLf ▸ List.mem_map.2 ⟨q, hq, rfl⟩
  refine ⟨fun j => match L[j]? with | some q => ρ q.1.id | none => 0, ?_⟩
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
    have hf := (inst_facts hok hdecl (hmemL qj (List.mem_of_getElem? hqj))).2.1
    rw [Lhs2.wins_of_windows? hf] at hwj
    simpa using hwj
  subst hw
  simp only [hqi, hqj]
  exact rank_insts hr (hmemL qi (List.mem_of_getElem? hqi)) (hmemL qj (List.mem_of_getElem? hqj))
    (hrd r hrE) hov

/-! ## The structural theorems for `name.sem` -/

/-- **`CombDesign (name.sem N)`** from the summary and the obligations. -/
theorem comb_of_summary {d : PDesign} {s : Summary} (hs : d.summary = .ok s) {args : List Int}
    {σ : String → Int} {env : IEnv} (harity : args.length = d.params.length)
    (h1 : d.paramEnv2 args = .ok env) (hag : Agrees σ env s.params) (hok : s.StructOk)
    (hauto : s.AutoObl σ args) (hin : s.InRangeObl σ) (hdisj : s.DisjObl σ) :
    CombDesign (d.instantiateGD2 args) := by
  obtain ⟨m, hm, hR⟩ := Summary.sound hs harity h1 hag hok hauto hin
  obtain ⟨hc, hpos⟩ := realized_comb hR hok hin hdisj
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
  obtain ⟨hc, hpos⟩ := realized_comb hR hok hin hdisj
  rw [PDesign.instantiateGD2_of_combDesign hm hc hpos]
  exact realized_acyclic hR hok hrank

/-! ## The forms the tactic uses: the valuation is the parameters zipped with the arguments -/

theorem Agrees_of_map {σ : String → Int} {env : IEnv} {ns : List String}
    (h : ns.map (fun n => env.vals.lookup n) = ns.map (fun n => some (σ n))) :
    Agrees σ env ns := by
  intro n hn
  exact List.map_inj_left.mp h n hn

/-- `comb_of_summary` at the canonical valuation `σL (params.zip args)`, the environment check
in a `rfl`-provable form. -/
theorem comb_view {d : PDesign} {s : Summary} {args : List Int} {env : IEnv}
    (hs : d.summary = .ok s) (harity : args.length = d.params.length)
    (h1 : d.paramEnv2 args = .ok env)
    (hag : s.params.map (fun n => env.vals.lookup n) =
      s.params.map (fun n => some (σL (s.params.zip args) n)))
    (hok : s.StructOk) (hauto : s.AutoObl (σL (s.params.zip args)) args)
    (hin : s.InRangeObl (σL (s.params.zip args))) (hdisj : s.DisjObl (σL (s.params.zip args))) :
    CombDesign (d.instantiateGD2 args) :=
  comb_of_summary hs harity h1 (Agrees_of_map hag) hok hauto hin hdisj

theorem acyclic_view {d : PDesign} {s : Summary} {args : List Int} {env : IEnv}
    (hs : d.summary = .ok s) (harity : args.length = d.params.length)
    (h1 : d.paramEnv2 args = .ok env)
    (hag : s.params.map (fun n => env.vals.lookup n) =
      s.params.map (fun n => some (σL (s.params.zip args) n)))
    (hok : s.StructOk) (hauto : s.AutoObl (σL (s.params.zip args)) args)
    (hin : s.InRangeObl (σL (s.params.zip args))) (hdisj : s.DisjObl (σL (s.params.zip args)))
    (ρ : SiteId → Nat) (hrank : s.RankObl ρ (σL (s.params.zip args))) :
    Acyclic (d.instantiateGD2 args) :=
  acyclic_of_summary hs harity h1 (Agrees_of_map hag) hok hauto hin hdisj hrank

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

/-- Two-index families, lexicographic: `(i, j) ↦ i * W + j` for `j < W`. The decrease goal is
closed by `lexRank_fam_lt` (lexicographic, linear hypotheses), so the nonlinear `i * W + j` never
reaches the player; `lexRank` is deliberately NOT unfolded by the tactic's normalization. -/
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
