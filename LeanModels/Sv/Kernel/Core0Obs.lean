import LeanModels.Sv.Kernel.Core0Comb
import LeanModels.Sv.Kernel.Core0Proc
import LeanModels.Sv.Mono2
import LeanModels.Sv.Observe

/-!
# E-core-0 as an observation backend, and the comb slice of R-DESIGN2 (`LeanModels.Sv.Kernel`)

**Status: transport theorem** (R-DESIGN2, comb slice) between the `run2` backend `Obs_run2`
(agent P's `Observe.lean`, provisional over `run2`) and E-core-0 as a backend, `Obs_E0`.

## The backend `Obs_E0` (an instance of P's `ESig`)

E-core-0 has no clocks. The environment is a list of stimulus entries (`run2`'s own type). Each
cycle takes TWO slots, the discipline `clockExpand` uses: slot `2c` carries entry `c`'s input events
(`Config.nextSlot`, `Core0.lean`; time zero is `Config.start`), slot `2c + 1` carries none and is the
cycle's sample slot. So the pre sample (Preponed of slot `2c + 1`) is slot `2c`'s closed store:
inputs applied and comb logic settled; the post sample (Postponed of slot `2c + 1`) is the same store,
since nothing happens in a quiet slot. A configuration is reported through its view
(`ESig.Config := SvState`), so a probe reads a declared name exactly as `run2`'s does.

## What is proved

For an equation design `d` of `E` (`Settles E d rank`) and `SettleAgree E d`, which holds for
assign-only designs (`SettleAgree.ofSettles`, `d = E.toDesign2`) and for designs with `always_comb`
blocks through their lowering (`SettleAgree.ofLower`, gate G-B's `Settles.ofLower`):

* `behaves0_inv`, `exists_behaves0`, `progress_E0`: every slot of every behaviour closes (R-COMB-0
  per slot), and every choice and environment has a behaviour.
* E → `run2`: every E behaviour is a `run2` behaviour, under ANY schedule, with the stimulus that
  re-drives every input to the value the cycle's pre sample holds. `included_E0_run2_agree`;
  assign-only at `run2`'s own fuel: `runObs2_of_runs_E0`, `included_E0_run2`; with `always_comb`:
  `included_E0_run2_lower`.
* `run2` → E, for typed stimuli (`StimTyped`: every entry binds each input it mentions at the
  declared width): `included_run2_E0_of_typed`, as `IncludedOn` (`Included` restricted to an
  environment predicate).
* The restriction is needed: `not_included_run2_E0` proves `¬ Included Obs_run2 Obs_E0` for every
  assign-only design with an input. `run2` stores a stimulus value as given, E converts it to the
  port's width (LRM 10.7), and E's samples are typed (`E0_pre_width`).
* `pre_input`: the pre sample holds the inputs the cycle's entry binds (at declared width), which
  the receptiveness conjunct needs.
* Instances: `Core0Smoke.mux1_included`, `mux1_included_typed` (one `always_comb` between two
  assigns); the records' designs in `svgolf/design/architecture/ObsCombE*.lean`.
-/

namespace LeanModels.Sv.Kernel

open LeanModels.Sv.Observe

set_option autoImplicit false

/-! ## The backend -/

/-- The entry of slot `t`: slot `2c` carries entry `c`, slot `2c + 1` none. -/
def slotEntry (env : List SvState) (t : Nat) : SvState :=
  if t % 2 = 0 then (env[t / 2]?).getD [] else []

/-- **A behaviour of E-core-0** under an environment: slot `t` closes at `cfg t`, from time zero,
each slot opened by its input events. -/
def Behaves0 (E : Elab) (env : List SvState) (ch : Choice) (cfg : Nat → Config) : Prop :=
  SlotCloses E ch (Config.start E (slotEntry env 0)) (cfg 0) ∧
  ∀ t, SlotCloses E ch (Config.nextSlot E (cfg t) (slotEntry env (t + 1))) (cfg (t + 1))

/-- **E-core-0 as an `ESig`** (agent P's signature): two slots per cycle, the sample slot odd. -/
def E0 : ESig where
  Elab := Elab
  Choice := Choice
  Env := List SvState
  Config := SvState
  iface e := ⟨inputSigs e.toDesign2, outputSigs e.toDesign2⟩
  Disciplined _ _ := True
  read := SvState.lookup
  Behaves e env ch b := ∃ cfg, Behaves0 e env ch cfg ∧ ∀ t, b t = e.view (cfg t).store
  preponed b t := b (t - 1)
  cycles env := env.length
  edgeSlot _ c := 2 * c + 1

/-- **`Obs_E0`**: E-core-0 as an observation backend. -/
abbrev Obs_E0 : ObservationModel := Obs_E E0

/-! ## Input events on the store -/

theorem Elab.applyInputs_ty (E : Elab) (s : Store) (entry : SvState) (x : VarId) :
    (E.applyInputs s entry x).ty = (s x).ty := by
  unfold Elab.applyInputs
  split
  · split
    · split <;> rfl
    · rfl
  · rfl

theorem Elab.Typed.applyInputs {E : Elab} {s : Store} (hT : E.Typed s) (entry : SvState) :
    E.Typed (E.applyInputs s entry) := by
  intro x dc h
  rw [E.applyInputs_ty]
  exact hT x dc h

/-- An empty batch of input events changes nothing. -/
theorem Elab.applyInputs_nil (E : Elab) (s : Store) : E.applyInputs s [] = s := by
  funext x
  unfold Elab.applyInputs
  split
  · split
    · simp [SvState.lookup]
    · rfl
  · rfl

/-- The declared name a variable resolves from is an input name when its declaration is an input. -/
theorem Elab.mem_inputNames {E : Elab} {dc : Decl} (hdc : dc ∈ E.decls.toList)
    (hin : dc.isInput = true) : dc.name ∈ E.toDesign2.inputNames.toList := by
  simp only [Design2.inputNames, Elab.toDesign2, Array.toList_filterMap, List.mem_filterMap]
  exact ⟨dc, hdc, by simp [hin]⟩

/-- **Input events touch only inputs**: a name that is not an input reads the same. -/
theorem Elab.lookup_view_applyInputs_of_not_input {E : Elab} (s : Store) (entry : SvState)
    {n : String} (hn : n ∉ E.toDesign2.inputNames.toList) :
    SvState.lookup (E.view (E.applyInputs s entry)) n = SvState.lookup (E.view s) n := by
  rw [E.lookup_view, E.lookup_view]
  cases hx : E.resolve n with
  | none => rfl
  | some x =>
      obtain ⟨dc, hdecl, hname, hmem, -⟩ := Elab.resolve_some hx
      have hin : dc.isInput = false := by
        cases h : dc.isInput with
        | false => rfl
        | true => exact absurd (hname ▸ Elab.mem_inputNames hmem h) hn
      simp only [Option.map_some, Elab.applyInputs, hdecl, hin]
      rfl

/-- `resizeU` to a vector's own width is the identity. -/
theorem LVec.resizeU_of_width {v : LVec} {w : Nat} (h : v.width = w) : v.resizeU w = v := by
  apply LVec.ext_getD (by simp [h])
  intro i hi
  simp only [LVec.width_resizeU] at hi
  have hi' : i < v.bits.size := by simp only [LVec.width] at h; omega
  simp [LVec.resizeU, hi, hi']

/-- On a list whose image has no duplicates, the map is injective. -/
theorem nodup_map_inj {α β : Type} {f : α → β} :
    ∀ {l : List α}, (l.map f).Nodup → ∀ {x y : α}, x ∈ l → y ∈ l → f x = f y → x = y
  | [], _, _, _, hx, _, _ => absurd hx List.not_mem_nil
  | a :: l, h, x, y, hx, hy, hxy => by
      simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at h
      rcases List.mem_cons.mp hx with hx | hx <;> rcases List.mem_cons.mp hy with hy | hy
      · rw [hx, hy]
      · rw [hx] at hxy; exact absurd hxy.symm (h.1 y hy)
      · rw [hy] at hxy; exact absurd hxy (h.1 x hx)
      · exact nodup_map_inj h.2 hx hy hxy

/-- An input event on an input of a 4-state design, at the declared width, is read back as given. -/
theorem Elab.lookup_view_applyInputs_input {E : Elab} (hnd : (E.decls.toList.map Decl.name).Nodup)
    (h4 : AllFour E) {s : Store} (hT : E.Typed s) {entry : SvState} {n : String} {v : LVec}
    (hn : n ∈ E.toDesign2.inputNames.toList) (hv : SvState.lookup entry n = some v)
    (hw : E.toDesign2.declWidth n = some v.width) :
    SvState.lookup (E.view (E.applyInputs s entry)) n = some v := by
  rw [E.lookup_view]
  cases hx : E.resolve n with
  | none =>
      rw [Elab.resolve_none hx] at hw
      cases hw
  | some x =>
      obtain ⟨dc, hdecl, hname, hmem, hdw⟩ := Elab.resolve_some hx
      -- the declaration `resolve` finds is the input declaration of that name
      have hin : dc.isInput = true := by
        simp only [Design2.inputNames, Elab.toDesign2, Array.toList_filterMap,
          List.mem_filterMap] at hn
        obtain ⟨dc', hdc', hsome⟩ := hn
        cases hi : dc'.isInput with
        | false => simp [hi] at hsome
        | true =>
            simp only [hi, if_true, Option.some.injEq] at hsome
            have : dc' = dc := nodup_map_inj hnd hdc' hmem (hsome.trans hname.symm)
            exact this ▸ hi
      have hty := hT x dc hdecl
      have h4' : (s x).ty.fourState = true := by
        rw [hty]; simp [VType.ofDecl, h4 dc hmem]
      have hwd : (s x).ty.width = v.width := by
        rw [hty]; rw [hdw, Option.some.injEq] at hw; simpa [VType.ofDecl] using hw
      simp only [Option.map_some, Elab.applyInputs, hdecl, hin, if_true, hname, hv]
      simp only [Val.ofLVec, VType.conv_of_four h4', hwd, LVec.resizeU_of_width rfl]

/-! ## Slots -/

/-- A closed configuration steps to nothing: its only closure is itself. -/
theorem slotCloses_closed {E : Elab} {ch : Choice} {c c' : Config} (hc : c.active = [])
    (h : SlotCloses E ch c c') : c' = c := by
  obtain ⟨hs, -⟩ := h
  cases hs with
  | refl => rfl
  | head hstep _ =>
      have hperm := ch.choose_perm c.k c.active
      rw [hc] at hperm
      have : ch.choose c.k [] = [] := List.perm_nil.mp hperm
      simp [step, hc, this] at hstep

/-- A quiet slot after a closed one is the closed configuration again. -/
theorem nextSlot_nil {E : Elab} {c : Config} (hc : c.active = []) : Config.nextSlot E c [] = c := by
  obtain ⟨s, a, k⟩ := c
  simp only at hc
  subst hc
  have htr : E.triggered (E.view s) (E.view s) = [] := by
    unfold Elab.triggered
    rw [List.filter_eq_nil_iff]
    intro q _
    simp [ReadWin.agree_refl]
  simp only [Config.nextSlot, Elab.applyInputs_nil, htr]

/-- **A slot opened by input events keeps the settle invariant** (assign-only or lowered: any
equation design). A process not woken by the events reads only unchanged elements, and its
windows are not inputs. -/
theorem Settles.nextSlot_inv {E : Elab} {d : Design2} {rank : Nat → Nat} (hS : Settles E d rank)
    {c : Config} (hI : SettleInv E d c) (hc : c.active = []) (entry : SvState) :
    SettleInv E d (Config.nextSlot E c entry) := by
  have hnames : d.inputNames = E.toDesign2.inputNames := by
    simp [Design2.inputNames, Elab.toDesign2, hS.decls]
  refine ⟨hI.typed.applyInputs entry, (List.nodup_range.filter _), fun q hq =>
    (Elab.mem_triggered hq).1, fun q hq => ?_⟩
  have hold := hI.eqs q (by rw [hc]; exact List.not_mem_nil)
  intro t e n lo w off hp hm
  obtain ⟨old, v, hlo, hv, hext⟩ := hold t e n lo w off hp hm
  have hqn : q < E.procs.size := hS.lt_of_proc hp
  have hreads := Elab.not_triggered hqn hq
  -- the window's signal is driven, so it is not an input
  have hdr : n ∉ E.toDesign2.inputNames.toList := by
    rw [← hnames]
    exact hS.comb.notInput n ⟨q, lo, w, t, e, hp, Win.mem_of_mem_placed hm⟩
  refine ⟨old, v, ?_, ?_, hext⟩
  · show SvState.lookup (E.view (E.applyInputs c.store entry)) n = some old
    rw [Elab.lookup_view_applyInputs_of_not_input _ _ hdr]; exact hlo
  rw [← hv]
  exact (evalPure2_congr_reads fun r hr => hreads r (hS.complete q t e hp r hr)).symm

/-- The startup store is typed. -/
theorem Config.start_inv {E : Elab} {d : Design2} {rank : Nat → Nat} (hS : Settles E d rank)
    (entry : SvState) : SettleInv E d (Config.start E entry) :=
  SettleInv.init hS.size ((Elab.typed_initStore E).applyInputs entry)

/-- **Every slot of a behaviour is closed and keeps the invariant.** -/
theorem behaves0_inv {E : Elab} {d : Design2} {rank : Nat → Nat} (hS : Settles E d rank)
    {env : List SvState} {ch : Choice} {cfg : Nat → Config} (hb : Behaves0 E env ch cfg) :
    ∀ t, SettleInv E d (cfg t) ∧ (cfg t).active = []
  | 0 => ⟨hS.steps_inv hb.1.1 (Config.start_inv hS _), active_nil_of_closed hb.1.2⟩
  | t + 1 =>
      have ih := behaves0_inv hS hb t
      ⟨hS.steps_inv (hb.2 t).1 (hS.nextSlot_inv ih.1 ih.2 _), active_nil_of_closed (hb.2 t).2⟩

open Classical in
/-- The closure of a configuration, if there is one. -/
noncomputable def closeOf (E : Elab) (ch : Choice) (c : Config) : Config :=
  if h : ∃ c', SlotCloses E ch c c' then Classical.choose h else c

open Classical in
theorem closeOf_spec {E : Elab} {ch : Choice} {c : Config} (h : ∃ c', SlotCloses E ch c c') :
    SlotCloses E ch c (closeOf E ch c) := by
  unfold closeOf
  rw [dif_pos h]
  exact Classical.choose_spec h

/-- The slot sequence: each slot closed from the previous one. -/
noncomputable def runCfg (E : Elab) (ch : Choice) (env : List SvState) : Nat → Config
  | 0 => closeOf E ch (Config.start E (slotEntry env 0))
  | t + 1 => closeOf E ch (Config.nextSlot E (runCfg E ch env t) (slotEntry env (t + 1)))

/-- **Every choice and every environment has a behaviour** (R-COMB-0 in every slot). -/
theorem exists_behaves0 {E : Elab} {d : Design2} {rank : Nat → Nat} (hS : Settles E d rank)
    (ch : Choice) (env : List SvState) : Behaves0 E env ch (runCfg E ch env) := by
  have key : ∀ t, SettleInv E d (runCfg E ch env t) ∧ (runCfg E ch env t).active = [] ∧
      (t = 0 → SlotCloses E ch (Config.start E (slotEntry env 0)) (runCfg E ch env 0)) := by
    intro t
    induction t with
    | zero =>
        obtain ⟨c', hc', -⟩ := hS.slot_closes ch (Config.start_inv hS (slotEntry env 0))
        have h := closeOf_spec ⟨c', hc'⟩
        exact ⟨hS.steps_inv h.1 (Config.start_inv hS _), active_nil_of_closed h.2, fun _ => h⟩
    | succ t ih =>
        have hI := hS.nextSlot_inv ih.1 ih.2.1 (slotEntry env (t + 1))
        obtain ⟨c', hc', -⟩ := hS.slot_closes ch hI
        have h := closeOf_spec ⟨c', hc'⟩
        exact ⟨hS.steps_inv h.1 hI, active_nil_of_closed h.2, fun h0 => by cases h0⟩
  refine ⟨(key 0).2.2 rfl, fun t => ?_⟩
  have hI := hS.nextSlot_inv (key t).1 (key t).2.1 (slotEntry env (t + 1))
  obtain ⟨c', hc', -⟩ := hS.slot_closes ch hI
  exact closeOf_spec ⟨c', hc'⟩

/-- **Progress over `Obs_E0`**: every choice and every environment has a completed behaviour. -/
theorem progress_E0 {E : Elab} {d : Design2} {rank : Nat → Nat} (hS : Settles E d rank)
    (k : Clocking) : Obs_E0.Progress k E := by
  intro ch env _
  refine ⟨_, _, ⟨fun t => E.view (runCfg E ch env t).store, ⟨runCfg E ch env,
    exists_behaves0 hS ch env, fun _ => rfl⟩, rfl⟩, rfl⟩

/-! ## The `run2` side of one comb cycle -/

/-- The stimulus entry that re-drives every input port of `d` to its value in `st`. -/
def inputsOf (d : Design2) (st : SvState) : SvState :=
  d.inputNames.toList.filterMap fun n => (SvState.lookup st n).map fun v => (n, v)

theorem lookup_inputsOf (d : Design2) (st : SvState) (n : String) :
    SvState.lookup (inputsOf d st) n =
      if n ∈ d.inputNames.toList then SvState.lookup st n else none :=
  lookup_filterMap (SvState.lookup st) n _

/-- **Re-driving the inputs**: from a state `st₀`, the entry that drives every input to its value
in `st₂` gives a state `st₁` that agrees with `st₀` off the inputs and with `st₂` on them. -/
theorem applyInputs2_redrive {d : Design2} (hd : CombDesign d) {st₀ st₁ st₂ : SvState}
    (hs₀ : StateShape d st₀) (hs₁ : StateShape d st₁)
    (hoff : ∀ n, n ∉ d.inputNames.toList → SvState.lookup st₁ n = SvState.lookup st₀ n)
    (hon : ∀ n, n ∈ d.inputNames.toList → SvState.lookup st₂ n = SvState.lookup st₁ n) :
    applyInputs2 d (inputsOf d st₂) st₀ = st₁ := by
  have hkeys : ∀ n ∈ d.inputNames.toList, n ∈ st₀.map Prod.fst := by
    intro n hn
    rw [hs₀.keys]
    obtain ⟨dc, hdc, -, rfl⟩ : ∃ dc ∈ d.decls.toList, dc.isInput = true ∧ dc.name = n := by
      simpa [Design2.inputNames] using hn
    exact List.mem_map_of_mem (f := Decl.name) hdc
  apply SvState.ext
  · rw [keys_applyInputs2 d _ hd.inFourState hkeys, hs₀.keys, hs₁.keys]
  · rw [keys_applyInputs2 d _ hd.inFourState hkeys, hs₀.keys]; exact hd.nodup
  · intro n
    rw [lookup_applyInputs2 d _ _ n hd.inFourState, lookup_inputsOf]
    by_cases hn : n ∈ d.inputNames.toList
    · rw [if_pos hn, if_pos hn, hon n hn]
      cases h1 : SvState.lookup st₁ n with
      | none =>
          obtain ⟨v, hv⟩ := hs₁.lookup_of_mem (n := n) (by
            obtain ⟨dc, hdc, -, rfl⟩ : ∃ dc ∈ d.decls.toList, dc.isInput = true ∧ dc.name = n := by
              simpa [Design2.inputNames] using hn
            exact List.mem_map_of_mem (f := Decl.name) hdc)
          rw [hv] at h1; cases h1
      | some v => rfl
    · rw [if_neg hn]; exact (hoff n hn).symm

/-- **One comb cycle of `run2`** on an assign-only design: from a shaped state, if the input settle
returns `S`, the cycle's pre and post samples are both `S`. -/
theorem cycleObs2_comb {d : Design2} (hd : CombDesign d) {σ : ScheduleOracle} {F : Nat}
    (hF : d.settleFuel ≤ F) {inputs st S : SvState} {k k1 : Nat} (hs : StateShape d st)
    (h1 : combSettle2 d σ F (applyInputs2 d inputs st) k = .ok (S, k1)) :
    cycleObs2 d σ F inputs st k = .ok (⟨S, S⟩, k1 + 2) := by
  obtain ⟨heqs, hsS, -⟩ := combSettle2_eqs hd (StateShape.of_applyInputs2 hd hs inputs) h1
  have hpre : cyclePre2 d σ F inputs st k = .ok (S, k1) := by
    simp only [cyclePre2, h1, Res.ok_bind]
    exact resetPhase2_of_nil (hd.resetIndices_eq _ _)
  have hnil : σ.choose k1 d.edgeIndices = [] := by
    rw [hd.edgeIndices_eq]; exact List.perm_nil.mp (σ.choose_perm k1 [])
  have hpost : cyclePost2 d σ F S k1 = .ok (S, k1 + 2) := by
    have h2 := combSettle2_of_combEqs_combFuel hd
      (show d.combFuel < F by unfold Design2.settleFuel at hF; omega) hsS heqs σ (k1 + 1)
    simp only [cyclePost2, hnil, edgePass2, Res.ok_bind, commitNba2, List.foldl_nil]
    exact h2
  simp only [cycleObs2, hpre, hpost, Res.ok_bind]
  rfl

/-! ## Every E behaviour is a `run2` behaviour -/

/-- The startup view is `run2`'s startup state, when every initializer has its declared width. -/
def InitTyped (d : Design2) : Prop := ∀ dc ∈ d.decls.toList, ∀ v, dc.init = some v → v.width = dc.width

theorem view_initStore {E : Elab} (hnd : (E.decls.toList.map Decl.name).Nodup)
    (hinit : InitTyped E.toDesign2) : E.view E.initStore = initState2 E.toDesign2 := by
  apply SvState.ext
  · rw [E.keys_view]; simp [initState2, Elab.toDesign2, List.map_map, Function.comp_def]
  · rw [E.keys_view]; exact hnd
  · intro n
    rw [E.lookup_view, lookup_initState2]
    cases hx : E.resolve n with
    | none =>
        have hf : (E.toDesign2.decls.toList.find? fun dc => dc.name == n) = none :=
          resolveAux_none hx
        simp only [hf, Option.map_none]
    | some x =>
        obtain ⟨j, dc, rfl, hj, hf⟩ := resolveAux_some hx
        have hdecl : E.declOf { decl := 0 + j } = some dc := by
          show E.decls[0 + j]? = some dc
          rw [Nat.zero_add, ← Array.getElem?_toList]; exact hj
        have hmem : dc ∈ E.decls.toList := List.mem_of_find?_eq_some hf
        have hf' : (E.toDesign2.decls.toList.find? fun dc => dc.name == n) = some dc := hf
        rw [hf']
        simp only [Option.map_some, Elab.initStore, hdecl, Val.ofLVec, VType.ofDecl, VType.conv]
        have hw : (dc.init.getD (if dc.isNet = true then LVec.replicate dc.width Logic.lz else LVec.xVec dc.width)).width = dc.width := by
          cases hi : dc.init with
          | none => cases hnet : dc.isNet <;> simp [hnet, LVec.replicate, LVec.xVec, LVec.width]
          | some v => exact hinit dc hmem v hi
        rw [LVec.resizeU_of_width hw]
        cases hi : dc.init
        · cases hnet : dc.isNet
          · rcases Bool.eq_false_or_eq_true dc.twoState with ht | ht <;>
              simp [hi, hnet, ht, LVec.replicate, LVec.xVec]
          · rcases Bool.eq_false_or_eq_true dc.twoState with ht | ht <;>
              simp [hi, hnet, ht, LVec.replicate, LVec.xVec]
        · cases hnet : dc.isNet
          · rcases Bool.eq_false_or_eq_true dc.twoState with ht | ht <;>
              simp [hi, hnet, ht, LVec.replicate, LVec.xVec]
          · rcases Bool.eq_false_or_eq_true dc.twoState with ht | ht <;>
              simp [hi, hnet, ht, LVec.replicate, LVec.xVec]

/-- Inputs are undriven, so a frame keeps their values. -/
theorem Frame.lookup_input {d : Design2} (hd : CombDesign d) {st st' : SvState} (hF : Frame d st st')
    {n : String} (hn : n ∈ d.inputNames.toList) : SvState.lookup st n = SvState.lookup st' n :=
  ReadWin.lookup_eq_of_agree_bits fun b => hF.undriven n b fun ⟨j, ⟨m, lo, w⟩, hW, hov⟩ => by
    rw [ReadWin.overlaps_win_one] at hov
    obtain ⟨rfl, -, -⟩ := hov
    exact hd.notInput n ⟨j, lo, w, hW⟩ hn

/-- The start of slot `2c` of a behaviour: input events applied to the previous closed store (the
startup store at `c = 0`), the invariant holding, and closing at `cfg (2c)`. -/
theorem slot_start {E : Elab} {d : Design2} {rank : Nat → Nat} (hS : Settles E d rank)
    {env : List SvState} {ch : Choice} {cfg : Nat → Config} (hb : Behaves0 E env ch cfg) (c : Nat) :
    ∃ (C : Config) (s₀ : Store), C.store = E.applyInputs s₀ (slotEntry env (2 * c)) ∧
      E.Typed s₀ ∧ SettleInv E d C ∧ SlotCloses E ch C (cfg (2 * c)) ∧
      (c = 0 → s₀ = E.initStore) ∧ (0 < c → s₀ = (cfg (2 * c - 1)).store) := by
  cases c with
  | zero =>
      exact ⟨Config.start E (slotEntry env 0), E.initStore, rfl, E.typed_initStore,
        Config.start_inv hS _, hb.1, fun _ => rfl, fun h => absurd h (Nat.lt_irrefl 0)⟩
  | succ c =>
      have hidx : 2 * (c + 1) - 1 + 1 = 2 * (c + 1) := by omega
      have hinv := behaves0_inv hS hb (2 * (c + 1) - 1)
      have hcl := hb.2 (2 * (c + 1) - 1)
      rw [hidx] at hcl
      exact ⟨Config.nextSlot E (cfg (2 * (c + 1) - 1)) (slotEntry env (2 * (c + 1))),
        (cfg (2 * (c + 1) - 1)).store, rfl, hinv.1.typed, hS.nextSlot_inv hinv.1 hinv.2 _, hcl,
        fun h => absurd h (Nat.succ_ne_zero c), fun _ => rfl⟩

/-- The sample slot `2c + 1` is quiet: it closes where slot `2c` closed. -/
theorem slot_quiet {E : Elab} {d : Design2} {rank : Nat → Nat} (hS : Settles E d rank)
    {env : List SvState} {ch : Choice} {cfg : Nat → Config} (hb : Behaves0 E env ch cfg) (c : Nat) :
    cfg (2 * c + 1) = cfg (2 * c) := by
  have hcl := hb.2 (2 * c)
  have hentry : slotEntry env (2 * c + 1) = [] := by
    have h1 : (2 * c + 1) % 2 = 1 := by omega
    simp [slotEntry, h1]
  rw [hentry, nextSlot_nil (behaves0_inv hS hb (2 * c)).2] at hcl
  exact slotCloses_closed (behaves0_inv hS hb (2 * c)).2 hcl

/-- The entry of slot `2c`. -/
theorem slotEntry_even (env : List SvState) (c : Nat) :
    slotEntry env (2 * c) = (env[c]?).getD [] := by
  have h1 : (2 * c) % 2 = 0 := by omega
  have h2 : 2 * c / 2 = c := by omega
  simp [slotEntry, h1, h2]

/-- **One cycle agrees** (assign-only). If slot `2c` applies input events to a store `s₀` and
closes at `c'`, then `run2`'s cycle from `s₀`'s view, driven by the entry that re-drives every input
to its value in `c'`, has pre and post samples both equal to `c'`'s view. -/
theorem cycleObs2_of_slot {E : Elab} {rank : Nat → Nat} (hS : Settles E E.toDesign2 rank)
    {ch : Choice} {C c' : Config} {s₀ : Store} {entry : SvState} (hT0 : E.Typed s₀)
    (hC : C.store = E.applyInputs s₀ entry) (hI : SettleInv E E.toDesign2 C)
    (hcl : SlotCloses E ch C c') (σ : ScheduleOracle) (k : Nat) :
    ∃ k', cycleObs2 E.toDesign2 σ E.toDesign2.settleFuel
        (inputsOf E.toDesign2 (E.view c'.store)) (E.view s₀) k =
      .ok (⟨E.view c'.store, E.view c'.store⟩, k') := by
  have hd := hS.comb
  have hs₀ := hS.shape hT0
  have hs₁ := hS.shape hI.typed
  have hF := hS.steps_frame hcl.1 hI
  have hre : applyInputs2 E.toDesign2 (inputsOf E.toDesign2 (E.view c'.store)) (E.view s₀) =
      E.view C.store := by
    refine applyInputs2_redrive hd hs₀ hs₁ (fun n hn => ?_) (fun n hn => ?_)
    · rw [hC]; exact Elab.lookup_view_applyInputs_of_not_input _ _ hn
    · exact (Frame.lookup_input hd hF hn).symm
  obtain ⟨S, k1, hset⟩ := combSettle2_terminates_of_le hd hS.acyclic (Nat.le_refl _) σ
    (E.view C.store) k hs₁
  have hSeq := hS.closed_eq_combSettle2 hI hcl hset
  subst hSeq
  rw [← hre] at hset
  exact ⟨_, cycleObs2_comb hd (Nat.le_refl _) hs₀ hset⟩

/-- **Every E behaviour is a `run2` behaviour** (assign-only), under ANY schedule: with the
stimulus that re-drives every input to its value in the cycle's pre sample, `run2` produces the
same pre and post samples, cycle by cycle. -/
theorem runFromObs2_of_behaves0 {E : Elab} {rank : Nat → Nat} (hS : Settles E E.toDesign2 rank)
    (hinit : InitTyped E.toDesign2) {env : List SvState} {ch : Choice} {cfg : Nat → Config}
    (hb : Behaves0 E env ch cfg) (σ : ScheduleOracle) :
    ∀ (n c0 k : Nat) (st : SvState),
      (c0 = 0 → st = initState2 E.toDesign2) → (0 < c0 → st = E.view (cfg (2 * c0 - 1)).store) →
      runFromObs2 E.toDesign2 σ E.toDesign2.settleFuel st k
          ((List.range' c0 n).map fun c => inputsOf E.toDesign2 (E.view (cfg (2 * c)).store)) =
        .ok ((List.range' c0 n).map fun c =>
          ⟨E.view (cfg (2 * c)).store, E.view (cfg (2 * c + 1)).store⟩) := by
  have hnd : (E.decls.toList.map Decl.name).Nodup := hS.comb.nodup
  intro n
  induction n with
  | zero => intro _ _ _ _ _; rfl
  | succ n ih =>
      intro c0 k st h0 hpos
      simp only [List.range', List.map_cons]
      obtain ⟨C, s₀, hC, hT0, hI, hcl, hz, hp⟩ := slot_start hS hb c0
      have hst : st = E.view s₀ := by
        cases c0 with
        | zero => rw [h0 rfl, hz rfl]; exact (view_initStore hnd hinit).symm
        | succ c => rw [hpos (Nat.succ_pos c), hp (Nat.succ_pos c)]
      subst hst
      obtain ⟨k', hcyc⟩ := cycleObs2_of_slot hS hT0 hC hI hcl σ k
      have hq := slot_quiet hS hb c0
      simp only [runFromObs2, hcyc, Res.ok_bind]
      rw [ih (c0 + 1) k' (E.view (cfg (2 * c0)).store) (fun h => absurd h (Nat.succ_ne_zero c0))
        (fun _ => by rw [show 2 * (c0 + 1) - 1 = 2 * c0 + 1 by omega, hq])]
      simp only [Res.ok_bind, hq]
      rfl

/-- **Every E-core-0 behaviour is a `run2` behaviour** (the run form): an `Obs_E0` run `r` is the
`runObs2` run of the stimulus that re-drives every input to its value in `r`'s pre samples, under
every process-atomic legal schedule, at the explicit fuel. -/
theorem runObs2_of_runs_E0 {E : Elab} {rank : Nat → Nat} (hS : Settles E E.toDesign2 rank)
    (hinit : InitTyped E.toDesign2) {ch : Choice} {env : List SvState} {r : List (CycleObs SvState)}
    (hr : Obs_E0.Runs E ch env r) (σ : ScheduleOracle) :
    runObs2 E.toDesign2 σ E.toDesign2.settleFuel (r.map fun o => inputsOf E.toDesign2 o.pre) =
      .ok r := by
  obtain ⟨b, ⟨cfg, hb, hbt⟩, rfl⟩ := hr
  show runObs2 E.toDesign2 σ E.toDesign2.settleFuel
      (((List.range env.length).map fun c =>
        (⟨b (2 * c + 1 - 1), b (2 * c + 1)⟩ : CycleObs SvState)).map
          fun o => inputsOf E.toDesign2 o.pre) =
    .ok ((List.range env.length).map fun c =>
      (⟨b (2 * c + 1 - 1), b (2 * c + 1)⟩ : CycleObs SvState))
  have hr : ((List.range env.length).map fun c =>
      (⟨b (2 * c + 1 - 1), b (2 * c + 1)⟩ : CycleObs SvState)) =
      (List.range' 0 env.length).map fun c =>
        ⟨E.view (cfg (2 * c)).store, E.view (cfg (2 * c + 1)).store⟩ := by
    rw [List.range_eq_range']
    apply List.map_congr_left
    intro c _
    rw [Nat.add_sub_cancel, hbt, hbt]
  rw [hr, List.map_map]
  unfold runObs2
  have hg : run2ClockGuard E.toDesign2 = .ok () := by
    have hnames : ∀ ps : List Proc0,
        (ps.map Proc0.toProcess2).filterMap run2Clock? = [] := by
      intro ps
      induction ps with
      | nil => rfl
      | cons p ps ih => cases p <;>
          simp only [List.map_cons, List.filterMap_cons, Proc0.toProcess2, run2Clock?, ih]
    have himplicit : ∀ ps : List Proc0,
        (ps.map Proc0.toProcess2).any (fun p =>
          match p with
          | .unsupported svKind _ => svKind.startsWith "SignalEventControl:"
          | _ => false) = false := by
      intro ps
      induction ps with
      | nil => rfl
      | cons p ps ih => cases p <;>
          simp only [List.map_cons, List.any_cons, Proc0.toProcess2, ih, Bool.false_or]
    have hc : run2ClockNames E.toDesign2 = [] := by
      simp [run2ClockNames, Elab.toDesign2, hnames E.procs.toList]
    have hi : E.toDesign2.processes.toList.any (fun p =>
        match p with
        | .unsupported svKind _ => svKind.startsWith "SignalEventControl:"
        | _ => false) = false := by
      simpa [Elab.toDesign2] using himplicit E.procs.toList
    unfold run2ClockGuard
    rw [hc]
    simp only [List.length_nil, Nat.not_lt_zero, ↓reduceIte]
    split
    · next h => exact Bool.noConfusion (hi.symm.trans h)
    · rfl
  simp only [hg, Res.ok_bind]
  exact runFromObs2_of_behaves0 hS hinit hb σ env.length 0 0 _ (fun _ => rfl)
    (fun h => absurd h (Nat.lt_irrefl 0))

/-- **R-DESIGN2, comb slice, E → `run2`** (transport theorem): every trusted behaviour of an
assign-only design under E-core-0 is one under `run2`, for every clocking. With
`Safe.of_included`, every safety statement proved over `run2` holds over E. -/
theorem included_E0_run2 {E : Elab} {rank : Nat → Nat} (hS : Settles E E.toDesign2 rank)
    (hinit : InitTyped E.toDesign2) (k : Clocking) :
    Included Obs_E0 Obs_run2 k E E.toDesign2 := by
  refine ⟨rfl, fun ch e₁ b _ hb => ?_⟩
  obtain ⟨r, hr, rfl⟩ := hb
  exact ⟨ch, r.map fun o => inputsOf E.toDesign2 o.pre, trivial, r,
    ⟨_, runObs2_of_runs_E0 hS hinit hr ch⟩, rfl⟩

/-- **The pre sample holds the inputs the cycle's entry binds**, at their declared widths. -/
theorem pre_input {E : Elab} {rank : Nat → Nat} (hS : Settles E E.toDesign2 rank)
    {env : List SvState} {ch : Choice} {cfg : Nat → Config} (hb : Behaves0 E env ch cfg)
    {c : Nat} {entry : SvState} (he : env[c]? = some entry) {n : String} {v : LVec}
    (hn : n ∈ E.toDesign2.inputNames.toList) (hv : SvState.lookup entry n = some v)
    (hw : E.toDesign2.declWidth n = some v.width) :
    SvState.lookup (E.view (cfg (2 * c)).store) n = some v := by
  obtain ⟨C, s₀, hC, hT0, hI, hcl, -, -⟩ := slot_start hS hb c
  rw [slotEntry_even, he, Option.getD_some] at hC
  have hF := hS.steps_frame hcl.1 hI
  rw [← Frame.lookup_input hS.comb hF hn, hC]
  exact Elab.lookup_view_applyInputs_input hS.comb.nodup hS.four hT0 hn hv hw

/-! ## One cycle argument for assign-only and `always_comb` designs (`SettleAgree`) -/

/-- **What the cycle argument needs of an equation design `d` of `E`**: `E.toDesign2` has no edge
and no reset process; a closed slot's store is what any completed `combSettle2 E.toDesign2`
returns from the slot's start; and some fuel completes it. Assign-only designs give it with
`d = E.toDesign2` (`SettleAgree.ofSettles`); a design with `always_comb` blocks gives it through its
lowering (`SettleAgree.ofLower`, by `CombSim`). -/
structure SettleAgree (E : Elab) (d : Design2) : Prop where
  edge : E.toDesign2.edgeIndices = []
  reset : ∀ a b, E.toDesign2.resetIndices a b = []
  closed : ∀ {ch : Choice} {c c' : Config}, SettleInv E d c → SlotCloses E ch c c' →
    ∀ {σ : ScheduleOracle} {fuel k : Nat} {S : SvState} {k' : Nat},
      combSettle2 E.toDesign2 σ fuel (E.view c.store) k = .ok (S, k') → E.view c'.store = S
  settles : ∀ {ch : Choice} {c c' : Config}, SettleInv E d c → SlotCloses E ch c c' →
    ∀ (σ : ScheduleOracle) (k : Nat), ∃ fuel k',
      combSettle2 E.toDesign2 σ fuel (E.view c.store) k = .ok (E.view c'.store, k')

/-- The assign-only instance. -/
theorem SettleAgree.ofSettles {E : Elab} {rank : Nat → Nat} (hS : Settles E E.toDesign2 rank) :
    SettleAgree E E.toDesign2 where
  edge := hS.comb.edgeIndices_eq
  reset := hS.comb.resetIndices_eq
  closed := fun {_ _ _} hI h {_ _ _ _ _} hS2 => hS.closed_eq_combSettle2 hI h hS2
  settles := fun hI h σ k => by
    obtain ⟨S, k', hS2⟩ := combSettle2_terminates_of_le hS.comb hS.acyclic (Nat.le_refl _) σ
      (E.view _) k (hS.shape hI.typed)
    exact ⟨_, k', by rw [hS.closed_eq_combSettle2 hI h hS2]; exact hS2⟩

/-- The `always_comb` instance, through the lowering `d'` (gate G-B's `Settles.ofLower`). -/
theorem SettleAgree.ofLower {E : Elab} {d' : Design2} {rank : Nat → Nat}
    (hl : E.toDesign2.lowerComb = some d') (hS : Settles E d' rank) : SettleAgree E d' where
  edge := (Design2.lowerComb_phases hl).1
  reset := (Design2.lowerComb_phases hl).2.1
  closed := fun {_ _ _} hI h {_ _ _ _ _} hS2 => closed_eq_combSettle2_lower hl hS hI h hS2
  settles := fun hI h σ k => by
    obtain ⟨S, k', hS2⟩ := combSettle2_terminates_of_le hS.comb hS.acyclic (Nat.le_refl _) σ
      (E.view _) k (hS.shape hI.typed)
    obtain ⟨-, f', hf'⟩ := (CombSim.of_lowerComb' hl hS.comb).combSettle2 σ _ _ k S k'
      (hS.shape hI.typed) hS2
    exact ⟨f', k', by rw [closed_eq_combSettle2_lower hl hS hI h hf']; exact hf'⟩

theorem applyInputs2_congr {d₁ d₂ : Design2} (h : d₁.decls = d₂.decls) (inputs st : SvState) :
    applyInputs2 d₁ inputs st = applyInputs2 d₂ inputs st := by
  simp only [applyInputs2, h]

theorem inputNames_congr {d₁ d₂ : Design2} (h : d₁.decls = d₂.decls) :
    d₁.inputNames = d₂.inputNames := by
  simp only [Design2.inputNames, h]

theorem inputsOf_congr {d₁ d₂ : Design2} (h : d₁.decls = d₂.decls) (st : SvState) :
    inputsOf d₁ st = inputsOf d₂ st := by
  simp only [inputsOf, inputNames_congr h]

/-- A closed configuration closes its own slot. -/
theorem SlotCloses.self {E : Elab} {ch : Choice} {c c' : Config} (h : SlotCloses E ch c c') :
    SlotCloses E ch c' c' :=
  ⟨Steps.refl c', h.2⟩

/-- **One cycle agrees** (any equation design): `cycleObs2_of_slot` for every `SettleAgree`
design, at every fuel above a threshold. -/
theorem cycleObs2_of_slot_agree {E : Elab} {d : Design2} {rank : Nat → Nat}
    (hS : Settles E d rank) (hA : SettleAgree E d) {ch : Choice} {C c' : Config} {s₀ : Store}
    {entry : SvState} (hT0 : E.Typed s₀) (hC : C.store = E.applyInputs s₀ entry)
    (hI : SettleInv E d C) (hcl : SlotCloses E ch C c') (σ : ScheduleOracle) (k : Nat) :
    ∃ F₀ k', ∀ F, F₀ ≤ F → cycleObs2 E.toDesign2 σ F
        (inputsOf E.toDesign2 (E.view c'.store)) (E.view s₀) k =
      .ok (⟨E.view c'.store, E.view c'.store⟩, k') := by
  have hdd : E.toDesign2.decls = d.decls := hS.decls.symm
  have hd := hS.comb
  have hre : applyInputs2 E.toDesign2 (inputsOf E.toDesign2 (E.view c'.store)) (E.view s₀) =
      E.view C.store := by
    rw [applyInputs2_congr hdd, inputsOf_congr hdd]
    have hF := hS.steps_frame hcl.1 hI
    refine applyInputs2_redrive hd (hS.shape hT0) (hS.shape hI.typed) (fun n hn => ?_)
      (fun n hn => ?_)
    · rw [hC]; exact Elab.lookup_view_applyInputs_of_not_input _ _ (by rwa [inputNames_congr hdd])
    · exact (Frame.lookup_input hd hF hn).symm
  have hI' : SettleInv E d c' := hS.steps_inv hcl.1 hI
  obtain ⟨F1, k1, h1⟩ := hA.settles hI hcl σ k
  obtain ⟨F2, k2, h2⟩ := hA.settles hI' hcl.self σ (k1 + 1)
  refine ⟨max F1 F2, k2, fun F hF => ?_⟩
  have h1' := combSettle2_mono h1 (fun h => by cases h) F (Nat.le_trans (Nat.le_max_left _ _) hF)
  have h2' := combSettle2_mono h2 (fun h => by cases h) F (Nat.le_trans (Nat.le_max_right _ _) hF)
  rw [← hre] at h1'
  have hnil : σ.choose k1 E.toDesign2.edgeIndices = [] := by
    rw [hA.edge]; exact List.perm_nil.mp (σ.choose_perm k1 [])
  simp only [cycleObs2, cyclePre2, h1', Res.ok_bind, resetPhase2_of_nil (hA.reset _ _), cyclePost2,
    hnil, edgePass2, commitNba2, List.foldl_nil, h2']
  rfl

/-- The run form of `cycleObs2_of_slot_agree`: `runFromObs2_of_behaves0` for every `SettleAgree`
design, at every fuel above a threshold. -/
theorem runFromObs2_of_behaves0_agree {E : Elab} {d : Design2} {rank : Nat → Nat}
    (hS : Settles E d rank) (hA : SettleAgree E d) (hinit : InitTyped E.toDesign2)
    {env : List SvState} {ch : Choice} {cfg : Nat → Config} (hb : Behaves0 E env ch cfg)
    (σ : ScheduleOracle) :
    ∀ (n c0 k : Nat) (st : SvState),
      (c0 = 0 → st = initState2 E.toDesign2) → (0 < c0 → st = E.view (cfg (2 * c0 - 1)).store) →
      ∃ F₀, ∀ F, F₀ ≤ F → runFromObs2 E.toDesign2 σ F st k
          ((List.range' c0 n).map fun c => inputsOf E.toDesign2 (E.view (cfg (2 * c)).store)) =
        .ok ((List.range' c0 n).map fun c =>
          ⟨E.view (cfg (2 * c)).store, E.view (cfg (2 * c + 1)).store⟩) := by
  have hnd : (E.decls.toList.map Decl.name).Nodup := hS.decls ▸ hS.comb.nodup
  intro n
  induction n with
  | zero => intro _ _ _ _ _; exact ⟨0, fun _ _ => rfl⟩
  | succ n ih =>
      intro c0 k st h0 hpos
      simp only [List.range', List.map_cons]
      obtain ⟨C, s₀, hC, hT0, hI, hcl, hz, hp⟩ := slot_start hS hb c0
      have hst : st = E.view s₀ := by
        cases c0 with
        | zero => rw [h0 rfl, hz rfl]; exact (view_initStore hnd hinit).symm
        | succ c => rw [hpos (Nat.succ_pos c), hp (Nat.succ_pos c)]
      subst hst
      obtain ⟨F1, k', hcyc⟩ := cycleObs2_of_slot_agree hS hA hT0 hC hI hcl σ k
      have hq := slot_quiet hS hb c0
      obtain ⟨F2, hrest⟩ := ih (c0 + 1) k' (E.view (cfg (2 * c0)).store)
        (fun h => absurd h (Nat.succ_ne_zero c0))
        (fun _ => by rw [show 2 * (c0 + 1) - 1 = 2 * c0 + 1 by omega, hq])
      refine ⟨max F1 F2, fun F hF => ?_⟩
      simp only [runFromObs2, hcyc F (Nat.le_trans (Nat.le_max_left _ _) hF), Res.ok_bind]
      rw [hrest F (Nat.le_trans (Nat.le_max_right _ _) hF)]
      simp only [Res.ok_bind, hq]
      rfl

/-- **Every E behaviour is a `run2` behaviour** (any equation design): the run form, with the
re-driving stimulus. -/
theorem runs2_of_runs_E0_agree {E : Elab} {d : Design2} {rank : Nat → Nat}
    (hS : Settles E d rank) (hA : SettleAgree E d) (hinit : InitTyped E.toDesign2) {ch : Choice}
    {env : List SvState} {r : List (CycleObs SvState)} (hr : Obs_E0.Runs E ch env r)
    (σ : ScheduleOracle) :
    Obs_run2.Runs E.toDesign2 σ (r.map fun o => inputsOf E.toDesign2 o.pre) r := by
  obtain ⟨b, ⟨cfg, hb, hbt⟩, rfl⟩ := hr
  have hr : ((List.range env.length).map fun c =>
      (⟨b (2 * c + 1 - 1), b (2 * c + 1)⟩ : CycleObs SvState)) =
      (List.range' 0 env.length).map fun c =>
        ⟨E.view (cfg (2 * c)).store, E.view (cfg (2 * c + 1)).store⟩ := by
    rw [List.range_eq_range']
    apply List.map_congr_left
    intro c _
    rw [Nat.add_sub_cancel, hbt, hbt]
  obtain ⟨F₀, hF⟩ := runFromObs2_of_behaves0_agree hS hA hinit hb σ env.length 0 0 _ (fun _ => rfl)
    (fun h => absurd h (Nat.lt_irrefl 0))
  refine ⟨F₀, ?_⟩
  show runObs2 E.toDesign2 σ F₀
      (((List.range env.length).map fun c =>
        (⟨b (2 * c + 1 - 1), b (2 * c + 1)⟩ : CycleObs SvState)).map
          fun o => inputsOf E.toDesign2 o.pre) =
    .ok ((List.range env.length).map fun c =>
      (⟨b (2 * c + 1 - 1), b (2 * c + 1)⟩ : CycleObs SvState))
  rw [hr, List.map_map]
  unfold runObs2
  have hg : run2ClockGuard E.toDesign2 = .ok () := by
    have hnames : ∀ ps : List Proc0,
        (ps.map Proc0.toProcess2).filterMap run2Clock? = [] := by
      intro ps
      induction ps with
      | nil => rfl
      | cons p ps ih => cases p <;>
          simp only [List.map_cons, List.filterMap_cons, Proc0.toProcess2, run2Clock?, ih]
    have himplicit : ∀ ps : List Proc0,
        (ps.map Proc0.toProcess2).any (fun p =>
          match p with
          | .unsupported svKind _ => svKind.startsWith "SignalEventControl:"
          | _ => false) = false := by
      intro ps
      induction ps with
      | nil => rfl
      | cons p ps ih => cases p <;>
          simp only [List.map_cons, List.any_cons, Proc0.toProcess2, ih, Bool.false_or]
    have hc : run2ClockNames E.toDesign2 = [] := by
      simp [run2ClockNames, Elab.toDesign2, hnames E.procs.toList]
    have hi : E.toDesign2.processes.toList.any (fun p =>
        match p with
        | .unsupported svKind _ => svKind.startsWith "SignalEventControl:"
        | _ => false) = false := by
      simpa [Elab.toDesign2] using himplicit E.procs.toList
    unfold run2ClockGuard
    rw [hc]
    simp only [List.length_nil, Nat.not_lt_zero, ↓reduceIte]
    split
    · next h => exact Bool.noConfusion (hi.symm.trans h)
    · rfl
  simp only [hg, Res.ok_bind]
  exact hF F₀ (Nat.le_refl _)

/-- **R-DESIGN2, comb slice, E → `run2`, any equation design** (transport theorem). -/
theorem included_E0_run2_agree {E : Elab} {d : Design2} {rank : Nat → Nat}
    (hS : Settles E d rank) (hA : SettleAgree E d) (hinit : InitTyped E.toDesign2) (k : Clocking) :
    Included Obs_E0 Obs_run2 k E E.toDesign2 := by
  refine ⟨rfl, fun ch e₁ b _ hb => ?_⟩
  obtain ⟨r, hr, rfl⟩ := hb
  exact ⟨ch, _, trivial, r, runs2_of_runs_E0_agree hS hA hinit hr ch, rfl⟩

/-- **R-DESIGN2, comb slice, E → `run2`, with `always_comb` blocks** (transport theorem): for a
design whose bodies lower to an equation design `d'` (gate G-B's hypotheses, through
`Settles.ofLower`), every E behaviour is a `run2` behaviour of the design itself. -/
theorem included_E0_run2_lower {E : Elab} {d' : Design2} {rank : Nat → Nat}
    (hl : E.toDesign2.lowerComb = some d') (hS : Settles E d' rank)
    (hinit : InitTyped E.toDesign2) (k : Clocking) :
    Included Obs_E0 Obs_run2 k E E.toDesign2 :=
  included_E0_run2_agree hS (SettleAgree.ofLower hl hS) hinit k

/-! ## The converse: every `run2` behaviour is an E behaviour, for typed stimuli -/

/-- A stimulus entry is **typed** for `d`: every input it binds, it binds at the declared width. -/
def EntryTyped (d : Design2) (entry : SvState) : Prop :=
  ∀ n v, n ∈ d.inputNames.toList → SvState.lookup entry n = some v → d.declWidth n = some v.width

/-- A stimulus is typed when every entry is. -/
def StimTyped (d : Design2) (stim : List SvState) : Prop := ∀ entry ∈ stim, EntryTyped d entry

/-- `Included` restricted to the environments satisfying `P`. -/
def IncludedOn (M₁ M₂ : ObservationModel) (k : Clocking) (d₁ : M₁.Design) (d₂ : M₂.Design)
    (P : M₁.Env → Prop) : Prop :=
  M₁.iface d₁ = M₂.iface d₂ ∧
    ∀ ch₁ e₁ b, P e₁ → M₁.Disciplined k e₁ → M₁.Behaves d₁ ch₁ e₁ b →
      ∃ ch₂ e₂, M₂.Disciplined k e₂ ∧ M₂.Behaves d₂ ch₂ e₂ b

/-- An input the entry does not bind keeps its value. -/
theorem Elab.lookup_view_applyInputs_none {E : Elab} (s : Store) {entry : SvState} {n : String}
    (hv : SvState.lookup entry n = none) :
    SvState.lookup (E.view (E.applyInputs s entry)) n = SvState.lookup (E.view s) n := by
  rw [E.lookup_view, E.lookup_view]
  cases hx : E.resolve n with
  | none => rfl
  | some x =>
      obtain ⟨dc, hdecl, hname, -, -⟩ := Elab.resolve_some hx
      simp [Elab.applyInputs, hdecl, hname, hv]

/-- **E's input events are `run2`'s** on a typed entry (4-state design): the view of the store
after the events is `applyInputs2` of the view. -/
theorem Elab.view_applyInputs {E : Elab} (hnd : (E.decls.toList.map Decl.name).Nodup)
    (h4 : AllFour E) {s : Store} (hT : E.Typed s) {entry : SvState}
    (hty : EntryTyped E.toDesign2 entry) :
    E.view (E.applyInputs s entry) = applyInputs2 E.toDesign2 entry (E.view s) := by
  have h4' : ∀ dc ∈ E.toDesign2.decls.toList, dc.isInput = true → dc.twoState = false :=
    fun dc hdc _ => h4 dc hdc
  have hkeys : ∀ n ∈ E.toDesign2.inputNames.toList, n ∈ (E.view s).map Prod.fst := by
    intro n hn
    rw [E.keys_view]
    obtain ⟨dc, hdc, -, rfl⟩ : ∃ dc ∈ E.decls.toList, dc.isInput = true ∧ dc.name = n := by
      simpa [Design2.inputNames, Elab.toDesign2] using hn
    exact List.mem_map_of_mem (f := Decl.name) hdc
  apply SvState.ext
  · rw [E.keys_view, keys_applyInputs2 _ _ h4' hkeys, E.keys_view]
  · rw [E.keys_view]; exact hnd
  · intro n
    rw [lookup_applyInputs2 _ _ _ n h4']
    by_cases hn : n ∈ E.toDesign2.inputNames.toList
    · rw [if_pos hn]
      cases hv : SvState.lookup entry n with
      | none => rw [Option.none_or]; exact Elab.lookup_view_applyInputs_none s hv
      | some v =>
          rw [Option.some_or]
          exact Elab.lookup_view_applyInputs_input hnd h4 hT hn hv (hty n v hn hv)
    · rw [if_neg hn]; exact Elab.lookup_view_applyInputs_of_not_input s entry hn

/-- **One `run2` cycle is E's** (any equation design, typed entry): a cycle of `run2` that
completes, at any fuel, from the view of the store slot `2c` opens with, has E's closed stores of
slots `2c` and `2c + 1` as its pre and post samples. -/
theorem cycleObs2_eq_of_slot {E : Elab} {d : Design2} {rank : Nat → Nat} (hS : Settles E d rank)
    (hA : SettleAgree E d) {env : List SvState} {ch : Choice} {cfg : Nat → Config}
    (hb : Behaves0 E env ch cfg) {c : Nat} {C : Config} {s₀ : Store} {entry : SvState}
    (hT0 : E.Typed s₀) (hC : C.store = E.applyInputs s₀ entry) (hI : SettleInv E d C)
    (hcl : SlotCloses E ch C (cfg (2 * c))) (hty : EntryTyped E.toDesign2 entry)
    {σ : ScheduleOracle} {F k k' : Nat} {o : CycleObs SvState}
    (h : cycleObs2 E.toDesign2 σ F entry (E.view s₀) k = .ok (o, k')) :
    o = ⟨E.view (cfg (2 * c)).store, E.view (cfg (2 * c + 1)).store⟩ := by
  have hnd : (E.decls.toList.map Decl.name).Nodup := hS.decls ▸ hS.comb.nodup
  have hre : applyInputs2 E.toDesign2 entry (E.view s₀) = E.view C.store := by
    rw [hC, Elab.view_applyInputs hnd hS.four hT0 hty]
  unfold cycleObs2 at h
  obtain ⟨⟨pre, k2⟩, hpre, hrest⟩ := Res.bind_eq_ok.mp h
  obtain ⟨⟨post, k3⟩, hpost, hfin⟩ := Res.bind_eq_ok.mp hrest
  simp only [Res.pure_eq, Res.ok.injEq, Prod.mk.injEq] at hfin
  obtain ⟨rfl, -⟩ := hfin
  unfold cyclePre2 at hpre
  rw [hre] at hpre
  obtain ⟨⟨S1, k1⟩, h1, hr⟩ := Res.bind_eq_ok.mp hpre
  dsimp only at hr
  rw [resetPhase2_of_nil (hA.reset _ _), Res.ok.injEq, Prod.mk.injEq] at hr
  obtain ⟨rfl, rfl⟩ := hr
  have hpre' : E.view (cfg (2 * c)).store = S1 := hA.closed hI hcl h1
  subst hpre'
  unfold cyclePost2 at hpost
  have hnil : σ.choose k1 E.toDesign2.edgeIndices = [] := by
    rw [hA.edge]; exact List.perm_nil.mp (σ.choose_perm k1 [])
  rw [hnil] at hpost
  simp only [edgePass2, Res.ok_bind, commitNba2, List.foldl_nil] at hpost
  have hpost' := hA.closed (hS.steps_inv hcl.1 hI) hcl.self hpost
  rw [slot_quiet hS hb c, hpost']

/-- The run form: a completed `run2` run of a typed stimulus is E's run, cycle by cycle. -/
theorem runFromObs2_eq_behaves0 {E : Elab} {d : Design2} {rank : Nat → Nat}
    (hS : Settles E d rank) (hA : SettleAgree E d) (hinit : InitTyped E.toDesign2)
    {env : List SvState} {ch : Choice} {cfg : Nat → Config} (hb : Behaves0 E env ch cfg)
    (hty : ∀ c : Nat, EntryTyped E.toDesign2 ((env[c]?).getD [])) {σ : ScheduleOracle} {F : Nat} :
    ∀ (n c0 k : Nat) (st : SvState) (r : List (CycleObs SvState)),
      (c0 = 0 → st = initState2 E.toDesign2) → (0 < c0 → st = E.view (cfg (2 * c0 - 1)).store) →
      runFromObs2 E.toDesign2 σ F st k ((List.range' c0 n).map fun c => (env[c]?).getD []) =
        .ok r →
      r = (List.range' c0 n).map fun c =>
        ⟨E.view (cfg (2 * c)).store, E.view (cfg (2 * c + 1)).store⟩ := by
  have hnd : (E.decls.toList.map Decl.name).Nodup := hS.decls ▸ hS.comb.nodup
  intro n
  induction n with
  | zero =>
      intro _ _ _ r _ _ h
      simp only [List.range'_zero, List.map_nil, runFromObs2, Res.ok.injEq] at h
      rw [← h]; rfl
  | succ n ih =>
      intro c0 k st r h0 hpos h
      simp only [List.range', List.map_cons] at h ⊢
      obtain ⟨C, s₀, hC, hT0, hI, hcl, hz, hp⟩ := slot_start hS hb c0
      have hst : st = E.view s₀ := by
        cases c0 with
        | zero => rw [h0 rfl, hz rfl]; exact (view_initStore hnd hinit).symm
        | succ c => rw [hpos (Nat.succ_pos c), hp (Nat.succ_pos c)]
      subst hst
      rw [slotEntry_even] at hC
      simp only [runFromObs2] at h
      obtain ⟨⟨o, k'⟩, hcyc, hrest⟩ := Res.bind_eq_ok.mp h
      have ho := cycleObs2_eq_of_slot hS hA hb hT0 hC hI hcl (hty c0) hcyc
      subst ho
      obtain ⟨os, hos, hfin⟩ := Res.bind_eq_ok.mp hrest
      simp only [Res.pure_eq, Res.ok.injEq] at hfin
      rw [← hfin, ih (c0 + 1) k' _ os (fun h => absurd h (Nat.succ_ne_zero c0))
        (fun _ => by rw [show 2 * (c0 + 1) - 1 = 2 * c0 + 1 by omega]) hos]

theorem map_range'_getD (l : List SvState) :
    (List.range' 0 l.length).map (fun c => (l[c]?).getD []) = l := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getElem?_eq_getElem h2]

/-- **Every `run2` behaviour of a typed stimulus is an E behaviour** (the run form). -/
theorem runs_E0_of_runObs2 {E : Elab} {d : Design2} {rank : Nat → Nat} (hS : Settles E d rank)
    (hA : SettleAgree E d) (hinit : InitTyped E.toDesign2) {σ : ScheduleOracle}
    {stim : List SvState} {F : Nat} {r : List (CycleObs SvState)}
    (hty : StimTyped E.toDesign2 stim) (h : runObs2 E.toDesign2 σ F stim = .ok r) :
    Obs_E0.Runs E σ stim r := by
  have hty' : ∀ c : Nat, EntryTyped E.toDesign2 ((stim[c]?).getD []) := by
    intro c
    cases hc : stim[c]? with
    | none => intro n v _ hv; simp at hv
    | some e =>
        obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp hc
        exact hty _ (List.getElem_mem hi)
  let cfg := runCfg E σ stim
  have hb : Behaves0 E stim σ cfg := exists_behaves0 hS σ stim
  have hfrom : runFromObs2 E.toDesign2 σ F (initState2 E.toDesign2) 0 stim = .ok r := by
    unfold runObs2 at h
    cases hg : run2ClockGuard E.toDesign2 with
    | ok u => simpa [hg] using h
    | timeout => simp [hg] at h
    | unsupported msg => simp [hg] at h
  have hr := runFromObs2_eq_behaves0 hS hA hinit hb hty' stim.length 0 0 _ r (fun _ => rfl)
    (fun h => absurd h (Nat.lt_irrefl 0)) (by
      rw [map_range'_getD]
      exact hfrom)
  refine ⟨fun t => E.view (cfg t).store, ⟨cfg, hb, fun _ => rfl⟩, ?_⟩
  rw [hr]
  show _ = (List.range stim.length).map fun c =>
    (⟨E.view (cfg (2 * c + 1 - 1)).store, E.view (cfg (2 * c + 1)).store⟩ : CycleObs SvState)
  rw [List.range_eq_range']
  apply List.map_congr_left
  intro c _
  rw [Nat.add_sub_cancel]

/-- **R-DESIGN2, comb slice, `run2` → E** (transport theorem), any equation design: every `run2`
behaviour of a typed stimulus is an E behaviour, under the same schedule and stimulus. -/
theorem included_run2_E0_of_typed {E : Elab} {d : Design2} {rank : Nat → Nat}
    (hS : Settles E d rank) (hA : SettleAgree E d) (hinit : InitTyped E.toDesign2) (k : Clocking) :
    IncludedOn Obs_run2 Obs_E0 k E.toDesign2 E (StimTyped E.toDesign2) := by
  refine ⟨rfl, fun σ stim b hty _ hb => ?_⟩
  obtain ⟨r, ⟨F, h⟩, rfl⟩ := hb
  exact ⟨σ, stim, trivial, r, runs_E0_of_runObs2 hS hA hinit hty h, rfl⟩

/-! ## The unrestricted converse is false: an ill-typed stimulus -/

theorem inputSigs_mem_inputNames {d : Design2} {p : Sig} (hp : p ∈ inputSigs d) :
    p.1 ∈ d.inputNames.toList := by
  obtain ⟨dc, hdc, hp⟩ := List.mem_filterMap.mp hp
  cases hin : dc.isInput with
  | false => simp [hin] at hp
  | true =>
      simp only [hin, if_true, Option.some.injEq] at hp
      subst hp
      simp only [Design2.inputNames, Array.toList_filterMap, List.mem_filterMap]
      exact ⟨dc, by simpa using hdc, by simp [hin]⟩

theorem inputSigs_declWidth {d : Design2} (hnd : (d.decls.toList.map Decl.name).Nodup)
    {p : Sig} (hp : p ∈ inputSigs d) : d.declWidth p.1 = some p.2 := by
  obtain ⟨dc, hdc, hp⟩ := List.mem_filterMap.mp hp
  cases hin : dc.isInput with
  | false => simp [hin] at hp
  | true =>
      simp only [hin, if_true, Option.some.injEq] at hp
      subst hp
      exact Design2.declWidth_of_mem hnd hdc

/-- **E's samples are typed**: in every E behaviour, a declared name reads at its declared width. -/
theorem E0_pre_width {E : Elab} {d : Design2} {rank : Nat → Nat} (hS : Settles E d rank)
    {ch : Choice} {env : List SvState} {b : List (CycleObs PortSample)}
    (hb : Obs_E0.Behaves E ch env b) {c : Nat} {o : CycleObs PortSample} (hc : b[c]? = some o)
    {n : String} {w : Nat} (hw : E.toDesign2.declWidth n = some w) {v : LVec}
    (hv : o.pre.read n = some v) : v.width = w := by
  obtain ⟨r, ⟨b', ⟨cfg, hb0, hbt⟩, rfl⟩, rfl⟩ := hb
  obtain ⟨hlt, ho⟩ := List.getElem?_eq_some_iff.mp hc
  have hmem := List.getElem_mem hlt
  rw [ho] at hmem
  obtain ⟨o', ho', rfl⟩ := List.mem_map.mp hmem
  obtain ⟨c', -, rfl⟩ := List.mem_map.mp ho'
  change (Obs_E0.sample E (b' (2 * c' + 1 - 1))).read n = some v at hv
  have hrs := ObservationModel.read_sample Obs_E0 E (b' (2 * c' + 1 - 1)) n
  rw [hrs] at hv
  split at hv
  · change SvState.lookup (b' (2 * c' + 1 - 1)) n = some v at hv
    rw [hbt, E.lookup_view] at hv
    have hT := (behaves0_inv hS hb0 (2 * c' + 1 - 1)).1.typed
    cases hx : E.resolve n with
    | none => rw [Elab.resolve_none hx] at hw; cases hw
    | some x =>
        obtain ⟨dc, hdecl, -, -, hdw⟩ := Elab.resolve_some hx
        rw [hx, Option.map_some, Option.some.injEq] at hv
        subst hv
        rw [hdw, Option.some.injEq] at hw
        rw [Val.width_eq, hT x dc hdecl, ← hw]
        simp [VType.ofDecl]
  · cases hv

/-- `run2` completes a one-entry stimulus on an assign-only acyclic design, whatever the entry
binds, and keeps every undriven name at its value after the input events. -/
theorem run2_one_entry {d : Design2} (hd : CombDesign d) (ha : Acyclic d) (σ : ScheduleOracle)
    (entry : SvState) :
    ∃ S, runObs2 d σ d.settleFuel [entry] = .ok [⟨S, S⟩] ∧
      ∀ n, NotDriven d n → SvState.lookup S n =
        SvState.lookup (applyInputs2 d entry (initState2 d)) n := by
  have hs := StateShape.of_initState2 hd
  obtain ⟨S, k1, h1⟩ := combSettle2_terminates_of_le hd ha (Nat.le_refl _) σ _ 0
    (StateShape.of_applyInputs2 hd hs entry)
  obtain ⟨-, -, hnd⟩ := combSettle2_eqs hd (StateShape.of_applyInputs2 hd hs entry) h1
  refine ⟨S, ?_, hnd⟩
  simp only [runObs2, runFromObs2, CombDesign.run2ClockGuard_ok hd,
    cycleObs2_comb hd (Nat.le_refl _) hs h1, Res.ok_bind,
    Res.pure_eq]

/-- **The unrestricted converse is false** (transport theorem, negative): for an assign-only
design with an input `n` of declared width `w`, the stimulus that binds `n` to a value of another
width has a `run2` behaviour that is no E behaviour. `run2` stores a stimulus value as given; E
converts it to the port's width (LRM 10.7), so E's samples read `n` at width `w` (`E0_pre_width`).
`included_run2_E0_of_typed` is the converse under the typing restriction. -/
theorem not_included_run2_E0 {E : Elab} {rank : Nat → Nat} (hS : Settles E E.toDesign2 rank)
    {n : String} {w : Nat} (hp : (n, w) ∈ inputSigs E.toDesign2) {v : LVec} (hv : v.width ≠ w)
    (k : Clocking) : ¬ Included Obs_run2 Obs_E0 k E.toDesign2 E := by
  rintro ⟨-, hinc⟩
  have hd := hS.comb
  have hn : n ∈ E.toDesign2.inputNames.toList := inputSigs_mem_inputNames hp
  have hw : E.toDesign2.declWidth n = some w := inputSigs_declWidth hd.nodup hp
  have hnames : n ∈ (Obs_run2.iface E.toDesign2).names := by
    show n ∈ (inputSigs E.toDesign2).map Prod.fst ++ (outputSigs E.toDesign2).map Prod.fst
    exact List.mem_append_left _ (List.mem_map_of_mem (f := Prod.fst) hp)
  obtain ⟨S, hrun, hund⟩ := run2_one_entry hd hS.acyclic σ_src [(n, v)]
  have hSn : SvState.lookup S n = some v := by
    rw [hund n (fun hdr => hd.notInput n hdr hn), lookup_applyInputs2 _ _ _ n hd.inFourState,
      if_pos hn]
    simp [SvState.lookup]
  have hb : Obs_run2.Behaves E.toDesign2 σ_src [[(n, v)]]
      [⟨Obs_run2.sample E.toDesign2 S, Obs_run2.sample E.toDesign2 S⟩] :=
    ⟨[⟨S, S⟩], ⟨_, hrun⟩, rfl⟩
  obtain ⟨_, _, -, hbE⟩ := hinc σ_src [[(n, v)]] _ trivial hb
  have hread : (Obs_run2.sample E.toDesign2 S).read n = some v := by
    rw [Obs_run2.read_sample hnames]; exact hSn
  exact hv (E0_pre_width hS hbE (c := 0)
    (o := ⟨Obs_run2.sample E.toDesign2 S, Obs_run2.sample E.toDesign2 S⟩) rfl hw hread)

/-! ## The elaboration of a `Design2` into E-core-0 (R-DESIGN2's `toE`) -/

/-- A `Design2` process as an E-core-0 process. Clocked and loud processes become loud
`always_comb` bodies: they are outside E-core-0 and refuse when run. -/
def Proc0.ofProcess2 : Process2 → Proc0
  | .assign t e => .assign t e
  | .alwaysComb b => .comb b
  | .unsupported k x => .comb (.unsupported k x)
  | .alwaysFF _ _ | .alwaysPlain _ _ | .alwaysFFR _ _ _ _ =>
      .comb (.unsupported "always_ff" "clocked processes are outside E-core-0")

/-- **`toE`**: the E-core-0 design of a `Design2`: the same name and declarations, every process
its E-core-0 image. -/
def Elab.ofDesign2 (d : Design2) : Elab :=
  { decls := d.decls, procs := (d.processes.toList.map Proc0.ofProcess2).toArray, name := d.name }

/-- The round trip: when every process is an assign or an `always_comb`, the corresponding
Design2 of `toE d` is `d`. -/
theorem Elab.toDesign2_ofDesign2 {d : Design2}
    (h : ∀ p ∈ d.processes.toList, (Proc0.ofProcess2 p).toProcess2 = p) :
    (Elab.ofDesign2 d).toDesign2 = d := by
  obtain ⟨name, decls, procs⟩ := d
  have hp : (procs.toList.map Proc0.ofProcess2).map Proc0.toProcess2 = procs.toList :=
    calc (procs.toList.map Proc0.ofProcess2).map Proc0.toProcess2
        = procs.toList.map (Proc0.toProcess2 ∘ Proc0.ofProcess2) := List.map_map
      _ = procs.toList.map id := List.map_congr_left fun p hp => h p hp
      _ = procs.toList := List.map_id _
  simp only [Elab.toDesign2, Elab.ofDesign2, List.toList_toArray, hp, Array.toArray_toList]

/-- An assign-only design round-trips. -/
theorem Elab.toDesign2_ofDesign2_of_comb {d : Design2} (hd : CombDesign d) :
    (Elab.ofDesign2 d).toDesign2 = d := by
  refine Elab.toDesign2_ofDesign2 fun p hp => ?_
  obtain ⟨i, hi, hpi⟩ := List.getElem_of_mem hp
  have hq : d.processes[i]? = some p := by
    rw [← Array.getElem?_toList, List.getElem?_eq_getElem hi, hpi]
  obtain ⟨t, e, ws, h, -⟩ := hd.assign i p hq
  rw [h]
  rfl

/-! ## The `always_comb` slice, instantiated (gate G-B's fixture) -/

namespace Core0Smoke

theorem mux1_initTyped : InitTyped mux1.toDesign2 := by
  intro dc hdc v hv
  simp [mux1, Elab.toDesign2] at hdc
  rcases hdc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp at hv

/-- **E → `run2` with an `always_comb` block** (non-vacuity of `included_E0_run2_lower`): two
assigns around one `always_comb` (`mux1`, `Core0.lean`). -/
theorem mux1_included (k : Clocking) : Included Obs_E0 Obs_run2 k mux1 mux1.toDesign2 :=
  included_E0_run2_lower mux1_lower mux1_settles mux1_initTyped k

/-- **`run2` → E with an `always_comb` block, typed stimuli** (non-vacuity of
`included_run2_E0_of_typed` through the lowering). -/
theorem mux1_included_typed (k : Clocking) :
    IncludedOn Obs_run2 Obs_E0 k mux1.toDesign2 mux1 (StimTyped mux1.toDesign2) :=
  included_run2_E0_of_typed mux1_settles (SettleAgree.ofLower mux1_lower mux1_settles)
    mux1_initTyped k

end Core0Smoke

/-! ## Axioms -/

#print axioms progress_E0
#print axioms runObs2_of_runs_E0
#print axioms included_E0_run2
#print axioms pre_input
#print axioms Elab.toDesign2_ofDesign2_of_comb
#print axioms included_E0_run2_agree
#print axioms included_E0_run2_lower
#print axioms included_run2_E0_of_typed
#print axioms not_included_run2_E0
#print axioms Core0Smoke.mux1_included
#print axioms Core0Smoke.mux1_included_typed

end LeanModels.Sv.Kernel
