import LeanModels.Sv.Loop2E
import LeanModels.Sv.Kernel.Core0Obs

/-!
# One `always_comb` process in E-core-0's slots, at a symbolic bound (WS3) — *derived from E*

E-core-0's slot theorems for `always_comb` (`activate_comb`, `Settles.ofLower`, `rcomb1`) take a
lowering and rank certificates computed on a concrete design. A design whose ONLY process is one
`always_comb` needs none of them: this module proves its slots directly, at every bound, from
structural facts.

**`SingleE E body I F W`**: E's only process is `body`; one activation runs it to `F` from every typed
store (`DenotesE`); `F` writes only the signals `W` (`frame`) and is idempotent; and a slot that wakes
nothing finds the store settled (`quiet`: if no element of the process's sensitivity changed, `F` still fixes the view).
For a fragment body all of it is derived (`Loop2Slot.singleE_frag` in `LoopTaskE`): `quiet` from
the LOCALITY of the fragment's meaning (`Stmt2.frag_local`: the step reads only its expressions'
windows) and the fact that every read of another signal is in E's sensitivity (`sens_of_read`: the
only windows the body writes are `n`'s, so LRM 9.2.2.2.1's self-write exclusion removes no other
read).

**The slot** (`SingleE.slot`): from a slot that opens typed, with the process ready or the store
settled, every legal schedule closes it, at ONE configuration, whose view is `F` of the opening view.
The process runs once, and possibly a second time (when its own write woke it: a no-op, `F` being
idempotent). **The behaviours** (`SingleE.behaves`, `SingleE.exists_behaves`): every slot of every
E-core-0 behaviour closes settled, and every choice and environment has one.
-/

namespace LeanModels.Sv.Loop2

open Kernel

/-! ## Locality of the fragment's meaning -/

theorem valE_congr {e : Expr2} {st st' : SvState} (hs : simpleExpr e = true)
    (hb : ∀ x ∈ e.idents, ∃ v, SvState.lookup st x = some v)
    (hb' : ∀ x ∈ e.idents, ∃ v, SvState.lookup st' x = some v)
    (h : ∀ r ∈ e.reads, r.agree st st') : valE st e = valE st' e :=
  Res.ok.inj ((evalPure2_valE hs hb).symm.trans ((evalPure2_congr_reads h).trans (evalPure2_valE hs hb')))

theorem agree_set_both {st st' : SvState} {r : ReadWin} (n : String) (v : LVec)
    (h : r.name ≠ n → r.agree st st') : r.agree (SvState.set st n v) (SvState.set st' n v) := by
  by_cases hn : r.name = n
  · exact ReadWin.agree_of_lookup (by rw [hn, CombGuard.lookup_set_self, CombGuard.lookup_set_self])
  · have := h hn
    cases r <;> simp_all [ReadWin.agree, ReadWin.name, CombGuard.lookup_set_ne]

/-- **The fragment's meaning reads only its expressions' windows** (`n` itself through the row). -/
theorem Stmt2.frag_local {n : String} {sl : Nat → Nat → Bool} {ns : List String} :
    ∀ s : Stmt2, s.fragOk n sl (fun x => decide (x ∈ ns)) = true →
      ∀ st st', BoundAll ns st → BoundAll ns st' → (∀ r ∈ s.rawReads, r.name ≠ n → r.agree st st') →
        ∀ v, s.step n st v = s.step n st' v := by
  have hv : ∀ e, exprOk (fun x => decide (x ∈ ns)) e = true → ∀ st st', BoundAll ns st →
      BoundAll ns st' → (∀ r ∈ e.reads, r.name ≠ n → r.agree st st') →
        ∀ v, valE (SvState.set st n v) e = valE (SvState.set st' n v) e :=
    fun e he st st' h h' hr v => valE_congr (exprOk_mem he).1 ((exprOk_mem he).2 _ (h.set n v))
      ((exprOk_mem he).2 _ (h'.set n v)) fun r hr' => agree_set_both n v (hr r hr')
  refine Stmt2.frag_rec _ (fun e he => ?_) (fun lo w e _ he => ?_) (fun c a b hc ha hb => ?_)
    (fun arr h => ?_)
  · intro st st' h h' hr v
    simp only [Stmt2.step, hv e he st st' h h' fun r hr' => hr r (by simpa [Stmt2.rawReads] using hr')]
  · intro st st' h h' hr v
    simp only [Stmt2.step, hv e he st st' h h' fun r hr' => hr r (by simpa [Stmt2.rawReads] using hr')]
  · intro st st' h h' hr v
    simp only [Stmt2.rawReads, List.mem_append] at hr
    simp only [Stmt2.step, hv c hc st st' h h' (fun r hr' => hr r (.inl (.inl hr'))),
      ha st st' h h' (fun r hr' => hr r (.inl (.inr hr')))]
    cases b with
    | none => rfl
    | some e =>
        simp only [Stmt2.optStep, hb e rfl st st' h h'
          (fun r hr' => hr r (.inr (by simpa [Stmt2.optRawReads] using hr')))]
  · intro st st' h' h'' hr v
    have key : ∀ l : List Stmt2, (∀ s ∈ l, ∀ st st', BoundAll ns st → BoundAll ns st' →
        (∀ r ∈ s.rawReads, r.name ≠ n → r.agree st st') → ∀ v, s.step n st v = s.step n st' v) →
        (∀ r ∈ Stmt2.listRawReads l, r.name ≠ n → r.agree st st') →
        ∀ v, Stmt2.listStep n st l v = Stmt2.listStep n st' l v := by
      intro l
      induction l with
      | nil => intros; rfl
      | cons s ss ih =>
          intro hl hr v
          simp only [Stmt2.listRawReads, List.mem_append] at hr
          simp only [Stmt2.listStep, hl s (List.mem_cons_self ..) st st' h' h''
            (fun r hr' => hr r (.inl hr')) v]
          exact ih (fun t ht => hl t (List.mem_cons_of_mem _ ht)) (fun r hr' => hr r (.inr hr')) _
    simp only [Stmt2.step]
    exact key arr.toList h (by simpa [Stmt2.rawReads] using hr) v

/-- Every window a fragment statement writes is `n`'s. -/
theorem Stmt2.frag_targets {d : Design2} {n : String} {sl : Nat → Nat → Bool} {rd : String → Bool} :
    ∀ s : Stmt2, s.fragOk n sl rd = true → ∀ W ∈ s.targetWins d, W.1 = n := by
  refine Stmt2.frag_rec _ (fun e _ => ?_) (fun lo w e _ _ => ?_) (fun c a b _ ha hb => ?_)
    (fun arr h => ?_)
  · intro ⟨m, lo, w⟩ hW
    simp only [Stmt2.targetWins, Option.mem_toList] at hW
    have := (Lhs2.staticWin_spec hW).1
    simp only [Lhs2.window?, Option.map_eq_some_iff, Prod.mk.injEq] at this
    obtain ⟨_, _, h1, -⟩ := this
    exact h1.symm
  · intro ⟨m, lo', w'⟩ hW
    simp only [Stmt2.targetWins, Option.mem_toList] at hW
    have := (Lhs2.staticWin_spec hW).1
    simp only [Lhs2.window?, Option.some.injEq, Prod.mk.injEq] at this
    exact this.1.symm
  · intro W hW
    simp only [Stmt2.targetWins, List.mem_append] at hW
    rcases hW with hW | hW
    · exact ha W hW
    · cases b with
      | none => simp [Stmt2.optTargetWins] at hW
      | some e => exact hb e rfl W (by simpa [Stmt2.optTargetWins] using hW)
  · intro W hW
    simp only [Stmt2.targetWins] at hW
    have key : ∀ l : List Stmt2, (∀ s ∈ l, ∀ W ∈ s.targetWins d, W.1 = n) →
        W ∈ Stmt2.listTargetWins d l → W.1 = n := by
      intro l
      induction l with
      | nil => simp [Stmt2.listTargetWins]
      | cons s ss ih =>
          intro hl hm
          simp only [Stmt2.listTargetWins, List.mem_append] at hm
          exact hm.elim (hl s (List.mem_cons_self ..) W)
            (ih fun t ht => hl t (List.mem_cons_of_mem _ ht))
    exact key arr.toList h hW

theorem ReadWin.name_of_overlaps {r : ReadWin} {W : Win} (h : r.overlaps W = true) : r.name = W.1 := by
  obtain ⟨m, lo, w⟩ := W
  cases r with
  | whole k => simpa [ReadWin.overlaps, ReadWin.name] using h
  | win k lo' w' => exact (Win.overlaps_eq_true.mp h).1

/-- **A read of another signal is in E's sensitivity**: self-write exclusion removes only reads of
windows the body writes, and they are all `n`'s. -/
theorem sens_of_read {E : Elab} {body : Stmt2} {n : String}
    (hp : E.procs[0]? = some (.comb body)) (ht : ∀ W ∈ body.targetWins E.toDesign2, W.1 = n)
    {r : ReadWin} (hr : r ∈ body.rawReads) (hn : r.name ≠ n) : r ∈ E.sens 0 := by
  simp only [Elab.sens, hp]
  refine List.mem_append_left _ (List.mem_filter.mpr ⟨hr, ?_⟩)
  simp only [Bool.not_eq_true', List.any_eq_false]
  exact fun W hW hov => hn ((ReadWin.name_of_overlaps hov).trans (ht W hW))

/-- **A quiet slot stays settled**: if no read in the process's sensitivity changed (and `n` did
not), the fragment body's meaning still fixes the state. -/
theorem settled_of_quiet {E : Elab} {body : Stmt2} {n : String} {ns : List String}
    {sl : Nat → Nat → Bool} (hp : E.procs[0]? = some (.comb body))
    (hfr : body.fragOk n sl (fun x => decide (x ∈ ns)) = true) (hn : n ∈ ns) {st st' : SvState}
    (h : BoundAll ns st) (h' : BoundAll ns st') (hl : SvState.lookup st' n = SvState.lookup st n)
    (hq : ∀ r ∈ E.sens 0, r.agree st st')
    (hF : SvState.set st n (body.step n st (sig st n)) = st) :
    SvState.set st' n (body.step n st' (sig st' n)) = st' := by
  have hsig : sig st' n = sig st n := by simp [sig, hl]
  have hloc := Stmt2.frag_local body hfr st st' h h'
    (fun r hr hrn => hq r (sens_of_read hp (Stmt2.frag_targets body hfr) hr hrn)) (sig st n)
  have hR : body.step n st (sig st n) = sig st n := by
    have := congrArg (fun s => sig s n) hF
    simpa using this
  rw [hsig, ← hloc, hR, ← hsig]
  obtain ⟨v, hv⟩ := h' n hn
  rw [show sig st' n = v by simp [sig, hv]]
  exact set_self hv

/-! ## The slot of a single `always_comb` -/

/-- **A single-`always_comb` design over E-core-0** (see the module docstring). -/
structure SingleE (E : Elab) (body : Stmt2) (I : SvState → Prop) (F : SvState → SvState)
    (W : List String) :
    Prop where
  procs : E.procs = #[.comb body]
  run : DenotesE E I body F
  typedI : ∀ σ, E.Typed σ → I (E.view σ)
  idem : ∀ st, I st → F (F st) = F st
  frame : ∀ st x, x ∉ W → SvState.lookup (F st) x = SvState.lookup st x
  quiet : ∀ σ entry, E.Typed σ → F (E.view σ) = E.view σ →
    0 ∉ E.triggered (E.view σ) (E.view (E.applyInputs σ entry)) →
    F (E.view (E.applyInputs σ entry)) = E.view (E.applyInputs σ entry)

namespace SingleE

variable {E : Elab} {body : Stmt2} {I : SvState → Prop} {F : SvState → SvState} {W : List String}

theorem triggered_cases (hs : SingleE E body I F W) (st st' : SvState) :
    E.triggered st st' = [] ∨ E.triggered st st' = [0] := by
  unfold Elab.triggered
  rw [hs.procs]
  by_cases h : ((E.sens 0).any fun r => !decide (r.agree st st')) = true <;> simp [h]

theorem triggered_self (E : Elab) (st : SvState) : E.triggered st st = [] := by
  unfold Elab.triggered
  rw [List.filter_eq_nil_iff]
  intro q _
  simp [ReadWin.agree_refl]

/-- A slot with nothing ready closes where it is, and only there. -/
theorem closes_nil {ch : Choice} {c : Config} (hc : c.active = []) :
    ∀ c', SlotCloses E ch c c' ↔ c' = c := by
  have hst : step E ch c = .slotClosed c := by
    have : ch.choose c.k c.active = [] := by rw [hc]; exact List.perm_nil.mp (ch.choose_perm _ _)
    simp [step, this]
  exact fun c' => ⟨slotCloses_closed hc, fun h => by subst h; exact ⟨.refl _, hst⟩⟩

/-- A step that runs something leaves the same closures. -/
theorem closes_next {ch : Choice} {c c₁ : Config} (h : step E ch c = .next c₁) :
    ∀ c', SlotCloses E ch c c' ↔ SlotCloses E ch c₁ c' := by
  intro c'
  refine ⟨fun ⟨hs, hc⟩ => ?_, fun ⟨hs, hc⟩ => ⟨.head h hs, hc⟩⟩
  cases hs with
  | refl => rw [h] at hc; cases hc
  | head h' hs' => rw [h] at h'; cases h'; exact ⟨hs', hc⟩

/-- One activation of the process, from a ready slot on a typed store. -/
theorem step_active (hs : SingleE E body I F W) (ch : Choice) {c : Config} (hc : c.active = [0])
    (hT : E.Typed c.store) : ∃ σ', E.Typed σ' ∧ E.view σ' = F (E.view c.store) ∧
      step E ch c = .next ⟨σ', E.triggered (E.view c.store) (E.view σ'), c.k + 1⟩ := by
  obtain ⟨σ', h1, h2, h3⟩ := hs.run c.store hT (hs.typedI _ hT)
  have hch : ch.choose c.k c.active = [0] := by
    rw [hc]; exact List.perm_singleton.mp (ch.choose_perm _ _)
  have hact : activate E 0 c.store = .ok (.ok (), σ') := by simp [activate, hs.procs, h1]
  exact ⟨σ', h2, h3, by simp [step, hch, hact]⟩

/-- **The slot**: from a typed opening with the process ready, or settled, every legal schedule
closes the slot at one configuration, whose view is `F` of the opening view. -/
theorem slot (hs : SingleE E body I F W) (ch : Choice) {c : Config} (hT : E.Typed c.store)
    (hc : (c.active = [] ∧ F (E.view c.store) = E.view c.store) ∨ c.active = [0]) :
    ∃ c', (∀ c'', SlotCloses E ch c c'' ↔ c'' = c') ∧ c'.active = [] ∧ E.Typed c'.store ∧
      E.view c'.store = F (E.view c.store) := by
  rcases hc with ⟨hc, hF⟩ | hc
  · exact ⟨c, closes_nil hc, hc, hT, hF.symm⟩
  obtain ⟨σ₁, hT₁, hv₁, h₁⟩ := hs.step_active ch hc hT
  have hF₁ : F (E.view σ₁) = E.view σ₁ := by rw [hv₁, hs.idem _ (hs.typedI _ hT)]
  rcases hs.triggered_cases (E.view c.store) (E.view σ₁) with h0 | h0
  · refine ⟨_, fun c'' => (closes_next h₁ c'').trans (closes_nil h0 c''), h0, hT₁, hv₁⟩
  · obtain ⟨σ₂, hT₂, hv₂, h₂⟩ := hs.step_active ch (c := ⟨σ₁, _, _⟩) h0 hT₁
    have hv : E.view σ₂ = E.view σ₁ := by rw [hv₂]; exact hF₁
    have h00 : E.triggered (E.view σ₁) (E.view σ₂) = [] := by rw [hv]; exact triggered_self E _
    refine ⟨_, fun c'' => (closes_next h₁ c'').trans ((closes_next h₂ c'').trans (closes_nil h00 c'')),
      h00, hT₂, by rw [hv, hv₁]⟩

/-- A slot that opens after a closed, settled one is ready or settled. -/
theorem open_next (hs : SingleE E body I F W) {c : Config} (hT : E.Typed c.store)
    (hF : F (E.view c.store) = E.view c.store) (entry : SvState) :
    ((Config.nextSlot E c entry).active = [] ∧
        F (E.view (Config.nextSlot E c entry).store) = E.view (Config.nextSlot E c entry).store) ∨
      (Config.nextSlot E c entry).active = [0] := by
  rcases hs.triggered_cases (E.view c.store) (E.view (E.applyInputs c.store entry)) with h0 | h0
  · exact .inl ⟨h0, hs.quiet c.store entry hT hF (by rw [h0]; exact List.not_mem_nil)⟩
  · exact .inr h0

theorem start_active (hs : SingleE E body I F W) (entry : SvState) :
    (Config.start E entry).active = [0] := by
  simp [Config.start, Config.init, hs.procs]

/-- **Every slot of every behaviour closes settled and typed.** -/
theorem behaves (hs : SingleE E body I F W) {env : List SvState} {ch : Choice} {cfg : Nat → Config}
    (hb : Behaves0 E env ch cfg) :
    ∀ t, (cfg t).active = [] ∧ E.Typed (cfg t).store ∧ F (E.view (cfg t).store) = E.view (cfg t).store
  | 0 => by
      have hT0 := (Elab.typed_initStore E).applyInputs (slotEntry env 0)
      obtain ⟨c', hu, ha, hT, hv⟩ :=
        hs.slot ch (c := Config.start E (slotEntry env 0)) hT0 (.inr (hs.start_active _))
      obtain rfl := (hu _).mp hb.1
      exact ⟨ha, hT, by rw [hv]; exact hs.idem _ (hs.typedI _ hT0)⟩
  | t + 1 => by
      obtain ⟨-, hT, hF⟩ := hs.behaves hb t
      have hTo := hT.applyInputs (slotEntry env (t + 1))
      obtain ⟨c', hu, ha, hT', hv⟩ := hs.slot ch (c := Config.nextSlot E (cfg t) (slotEntry env (t + 1)))
        hTo (hs.open_next hT hF _)
      obtain rfl := (hu _).mp (hb.2 t)
      exact ⟨ha, hT', by rw [hv]; exact hs.idem _ (hs.typedI _ hTo)⟩

/-- `closeOf` closes a slot `slot` covers, settled. -/
theorem closeOf_slot (hs : SingleE E body I F W) (ch : Choice) {c : Config} (hT : E.Typed c.store)
    (hc : (c.active = [] ∧ F (E.view c.store) = E.view c.store) ∨ c.active = [0]) :
    SlotCloses E ch c (closeOf E ch c) ∧ (closeOf E ch c).active = [] ∧
      E.Typed (closeOf E ch c).store ∧
      F (E.view (closeOf E ch c).store) = E.view (closeOf E ch c).store := by
  obtain ⟨c', hu, ha, hT', hv⟩ := hs.slot ch hT hc
  have h := closeOf_spec ⟨c', (hu c').mpr rfl⟩
  obtain rfl := (hu _).mp h
  exact ⟨h, ha, hT', by rw [hv, hs.idem _ (hs.typedI _ hT)]⟩

theorem runCfg_inv (hs : SingleE E body I F W) (ch : Choice) (env : List SvState) :
    ∀ t, (runCfg E ch env t).active = [] ∧ E.Typed (runCfg E ch env t).store ∧
      F (E.view (runCfg E ch env t).store) = E.view (runCfg E ch env t).store
  | 0 => (hs.closeOf_slot ch (c := Config.start E (slotEntry env 0))
      ((Elab.typed_initStore E).applyInputs _) (.inr (hs.start_active _))).2
  | t + 1 => by
      obtain ⟨-, hT, hF⟩ := hs.runCfg_inv ch env t
      exact (hs.closeOf_slot ch (c := Config.nextSlot E (runCfg E ch env t) (slotEntry env (t + 1)))
        (hT.applyInputs _) (hs.open_next hT hF _)).2

/-- **Every choice and environment has a behaviour** (no certificate). -/
theorem exists_behaves (hs : SingleE E body I F W) (ch : Choice) (env : List SvState) :
    Behaves0 E env ch (runCfg E ch env) :=
  ⟨(hs.closeOf_slot ch (c := Config.start E (slotEntry env 0))
      ((Elab.typed_initStore E).applyInputs _) (.inr (hs.start_active _))).1, fun t =>
    have h := hs.runCfg_inv ch env t
    (hs.closeOf_slot ch (c := Config.nextSlot E (runCfg E ch env t) (slotEntry env (t + 1)))
      (h.2.1.applyInputs _) (hs.open_next h.2.1 h.2.2 _)).1⟩

/-- The sample slot of a cycle is its edge slot again: nothing happens in a quiet slot. -/
theorem post_eq_pre (hs : SingleE E body I F W) {env : List SvState} {ch : Choice}
    {cfg : Nat → Config} (hb : Behaves0 E env ch cfg) (c : Nat) : cfg (2 * c + 1) = cfg (2 * c) := by
  have h := hb.2 (2 * c)
  rw [show slotEntry env (2 * c + 1) = [] by simp [slotEntry, Nat.add_mod],
    nextSlot_nil (hs.behaves hb (2 * c)).1] at h
  exact (closes_nil (hs.behaves hb (2 * c)).1 _).mp h

/-- The edge slot's closed view is `F` of the opening, whose inputs are the entry's. -/
theorem pre_view (hs : SingleE E body I F W) {env : List SvState} {ch : Choice} {cfg : Nat → Config}
    (hb : Behaves0 E env ch cfg) (t : Nat) :
    ∃ σ, E.Typed σ ∧ E.view (cfg t).store = F (E.view (E.applyInputs σ (slotEntry env t))) := by
  cases t with
  | zero =>
      have hT0 := (Elab.typed_initStore E).applyInputs (slotEntry env 0)
      obtain ⟨c', hu, -, -, hv⟩ :=
        hs.slot ch (c := Config.start E (slotEntry env 0)) hT0 (.inr (hs.start_active _))
      obtain rfl := (hu _).mp hb.1
      exact ⟨_, Elab.typed_initStore E, hv⟩
  | succ t =>
      obtain ⟨-, hT, hF⟩ := hs.behaves hb t
      obtain ⟨c', hu, -, -, hv⟩ := hs.slot ch (c := Config.nextSlot E (cfg t) (slotEntry env (t + 1)))
        (hT.applyInputs _) (hs.open_next hT hF _)
      obtain rfl := (hu _).mp (hb.2 t)
      exact ⟨_, hT, hv⟩

end SingleE

end LeanModels.Sv.Loop2

#pin_axioms LeanModels.Sv.Loop2.valE_congr LeanModels.Sv.Loop2.agree_set_both
  LeanModels.Sv.Loop2.Stmt2.frag_local LeanModels.Sv.Loop2.Stmt2.frag_targets
  LeanModels.Sv.Loop2.ReadWin.name_of_overlaps LeanModels.Sv.Loop2.sens_of_read
  LeanModels.Sv.Loop2.settled_of_quiet LeanModels.Sv.Loop2.SingleE.triggered_cases
  LeanModels.Sv.Loop2.SingleE.triggered_self LeanModels.Sv.Loop2.SingleE.closes_nil
  LeanModels.Sv.Loop2.SingleE.closes_next LeanModels.Sv.Loop2.SingleE.step_active
  LeanModels.Sv.Loop2.SingleE.slot LeanModels.Sv.Loop2.SingleE.open_next
  LeanModels.Sv.Loop2.SingleE.start_active LeanModels.Sv.Loop2.SingleE.behaves
  LeanModels.Sv.Loop2.SingleE.closeOf_slot LeanModels.Sv.Loop2.SingleE.runCfg_inv
  LeanModels.Sv.Loop2.SingleE.exists_behaves LeanModels.Sv.Loop2.SingleE.post_eq_pre
  LeanModels.Sv.Loop2.SingleE.pre_view
