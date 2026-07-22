/-
Proof module for `Examples/xsel/spec.lean` (three-file example layout,
SV lane) — gallery example 5 (`docs/sv-spec-surface.md`): the `always_comb`
if/else mux, with the gallery's two theorem shapes:

* known select (`xsel_known`): an embedded `Bool` select settles `y` to
  `if sel then a else b`;
* X-optimism (`xsel_x_else`): a `sel` of `x` — or `z`, the gallery's
  "identical `Logic.lz` twin", folded in as the `v = lx ∨ v = lz`
  hypothesis — takes the ELSE branch (`y = b`), per LRM §12.4 (zero, x, or
  z is not-true). Simulation picks `b` outright; it does NOT merge `a`/`b`
  bitwise. That this is provable is a feature: it is the truth about
  simulation, stated honestly.

`xsel` is the second comb-phase design after `adder`, and the first whose
comb process is an `always_comb` *statement* (blocking assign under an
`if`) rather than a continuous assign. The settle-loop architecture is
identical (one `combPass` computes `y := sel ? a : b`, the pass is
idempotent, `combSettle_idem` — shared in
`LeanModels/Sv/ToggleExample.lean` — closes the fixpoint in ≤ 2 passes);
the per-pass symbolic execution case-splits on `sel.condTrue`, the §12.4
truthiness the interpreter's `if` uses.

The rest is the house architecture (`Examples/adder/proof.lean`): one
symbolic cycle, one induction over the stimulus, cross-fuel determinism
(`run_det`) to pin any hypothesis trace to the canonical one, then pure
list mathematics about the canonical trace.

The design literal below is a hand-built copy of the extracted envelope;
`spec.lean` certifies (at elab time, from disk) that it is node-for-node
equal to `Examples/xsel/xsel.sv.json`.
-/
import LeanModels.Sv.ToggleExample

namespace Examples.xsel.proof

open LeanModels.Sv

/-- `Examples/xsel/xsel.sv` (`always_comb` if/else mux on `sel`),
hand-transcribed. -/
def xselDesign : Design :=
  { name := "xsel"
    decls := #[
      { name := "sel", width := 1, isInput := true },
      { name := "a", width := 8, isInput := true },
      { name := "b", width := 8, isInput := true },
      { name := "y", width := 8, isOutput := true }]
    processes := #[
      .alwaysComb (.ifStmt (.ident "sel")
        (.blockingAssign "y" (.ident "a"))
        (some (.blockingAssign "y" (.ident "b"))))] }

/-! ### Design-index facts (`rfl`; what σ's `choose` gets applied to) -/

theorem xsel_inputNames : xselDesign.inputNames = #["sel", "a", "b"] := rfl
theorem xsel_combIndices : xselDesign.combIndices = [0] := rfl
theorem xsel_edgeIndices : xselDesign.edgeIndices = [] := rfl
theorem xsel_p0 :
    xselDesign.processes[0]? =
      some (.alwaysComb (.ifStmt (.ident "sel")
        (.blockingAssign "y" (.ident "a"))
        (some (.blockingAssign "y" (.ident "b"))))) := rfl

theorem initState_xsel :
    initState xselDesign =
      [("sel", LVec.xVec 1), ("a", LVec.xVec 8), ("b", LVec.xVec 8),
       ("y", LVec.xVec 8)] := rfl

/-! ## Applied inputs -/

theorem applyInputs_xsel (inputs : SvState) (s a b y : LVec) :
    applyInputs xselDesign inputs [("sel", s), ("a", a), ("b", b), ("y", y)] =
      [("sel", appIn inputs "sel" s), ("a", appIn inputs "a" a),
       ("b", appIn inputs "b" b), ("y", y)] := by
  cases hsel : SvState.lookup inputs "sel" <;>
    cases ha : SvState.lookup inputs "a" <;>
      cases hb : SvState.lookup inputs "b" <;>
        simp [applyInputs, xsel_inputNames, appIn, hsel, ha, hb, SvState.set]

/-! ## The settle loop

Same shape as `Examples/adder/proof.lean`: one pass computes the mux, the
pass is idempotent, so the shared `combSettle_idem`
(`LeanModels/Sv/ToggleExample.lean`) closes the fixpoint in at most two
passes. The pass itself case-splits on the §12.4 truthiness of `sel` —
`condTrue`, which is `false` for `x`/`z`, is exactly where X-optimism
enters the semantics. -/

/-- One comb pass on the xsel state shape computes `y := sel ? a : b` in
the `if (sel)` §12.4 sense (threshold form, slack 4 — the statement
depth). -/
theorem xsel_combPass (s a b y : LVec) : ∀ g, 4 ≤ g →
    combPass xselDesign g [("sel", s), ("a", a), ("b", b), ("y", y)] [0] =
      .ok [("sel", s), ("a", a), ("b", b),
           ("y", if s.condTrue then a else b)] := by
  intro g hg
  obtain ⟨g', rfl⟩ := Nat.exists_eq_add_of_le hg
  rw [Nat.add_comm]
  by_cases hsel : s.condTrue <;> sv_simp [xsel_p0, hsel]

/-- `xsel` settles to `y = if sel then a else b` in at most two passes,
∀ σ (threshold form, slack 8): the comb ready list is the singleton `[0]`,
so σ is irrelevant (`choose_singleton`), and the pass is idempotent. -/
theorem xsel_combSettle (σ : ScheduleOracle) (s a b y : LVec) (k : Nat) :
    ∀ F, 8 ≤ F → ∃ k',
      combSettle xselDesign σ F [("sel", s), ("a", a), ("b", b), ("y", y)] k =
        .ok ([("sel", s), ("a", a), ("b", b),
              ("y", if s.condTrue then a else b)], k') := by
  intro F hF
  obtain ⟨f, rfl⟩ := Nat.exists_eq_add_of_le hF
  rw [Nat.add_comm]
  refine combSettle_idem xselDesign σ ?_ ?_ <;>
    rw [xsel_combIndices, σ.choose_singleton] <;>
      exact xsel_combPass _ _ _ _ _ (by omega)

/-! ## The canonical trace -/

/-- Canonical `xsel` trace: `sel`/`a`/`b` follow the stimulus, `y` settles
to the §12.4 mux every cycle (X-optimism included: an `x`/`z` select is
not-true, so `y` follows `b`). -/
def xselTrace (s a b : LVec) : List SvState → List SvState
  | [] => []
  | inp :: rest =>
      let s' := appIn inp "sel" s
      let a' := appIn inp "a" a
      let b' := appIn inp "b" b
      [("sel", s'), ("a", a'), ("b", b'),
       ("y", if s'.condTrue then a' else b')] :: xselTrace s' a' b' rest

/-- One symbolic `xsel` cycle, ∀ σ (threshold form, slack 8): apply the
inputs, settle (≤ 2 passes), empty edge phase (`choose_nil`), empty NBA
commit, settle again (already a fixpoint — 1 pass). The exit counter `k'`
depends on whether the first settle's pass changed `y`, hence the ∃. -/
theorem xsel_cycleStep (σ : ScheduleOracle) (inputs : SvState) (s a b y : LVec)
    (k : Nat) : ∀ F, 8 ≤ F → ∃ k',
    cycleStep xselDesign σ F inputs [("sel", s), ("a", a), ("b", b), ("y", y)] k =
      .ok ([("sel", appIn inputs "sel" s), ("a", appIn inputs "a" a),
            ("b", appIn inputs "b" b),
            ("y", if (appIn inputs "sel" s).condTrue then appIn inputs "a" a
                  else appIn inputs "b" b)], k') := by
  intro F hF
  obtain ⟨k1, h1⟩ := xsel_combSettle σ (appIn inputs "sel" s) (appIn inputs "a" a)
    (appIn inputs "b" b) y k F hF
  obtain ⟨k2, h2⟩ := xsel_combSettle σ (appIn inputs "sel" s) (appIn inputs "a" a)
    (appIn inputs "b" b)
    (if (appIn inputs "sel" s).condTrue then appIn inputs "a" a
     else appIn inputs "b" b) (k1 + 1) F hF
  refine ⟨k2, ?_⟩
  simp only [cycleStep, applyInputs_xsel, h1, Res.ok_bind, xsel_edgeIndices,
    σ.choose_nil, edgePass, commitNba, List.foldl_nil, h2]

/-- The canonical run, ∀ σ ∀ stimulus (threshold form). -/
theorem xsel_runFrom (σ : ScheduleOracle) :
    ∀ (stim : List SvState) (s a b y : LVec) (k F : Nat), 8 ≤ F →
      runFrom xselDesign σ F [("sel", s), ("a", a), ("b", b), ("y", y)] k stim =
        .ok (xselTrace s a b stim) := by
  intro stim
  induction stim with
  | nil => intro s a b y k F hF; simp [runFrom, xselTrace]
  | cons inp rest ih =>
    intro s a b y k F hF
    obtain ⟨k', hcyc⟩ := xsel_cycleStep σ inp s a b y k F hF
    simp only [runFrom, xselTrace]
    rw [hcyc]
    simp only [Res.ok_bind]
    rw [ih _ _ _ _ k' F hF]
    simp

/-- `xsel`'s full trace characterization: for EVERY schedule and EVERY
stimulus, any fuel ≥ 8 completes with the canonical trace (x startup
included). -/
theorem xsel_run (σ : ScheduleOracle) (stim : List SvState) :
    ∀ F, 8 ≤ F →
      run xselDesign σ F stim =
        .ok (xselTrace (LVec.xVec 1) (LVec.xVec 8) (LVec.xVec 8) stim) := by
  intro F hF
  rw [run, initState_xsel]
  exact xsel_runFrom σ stim _ _ _ _ 0 F hF

/-- Non-vacuity: every schedule and stimulus yields the canonical trace. -/
theorem xsel_total (σ : ScheduleOracle) (stim : List SvState) :
    Runs xselDesign σ stim (xselTrace (LVec.xVec 1) (LVec.xVec 8) (LVec.xVec 8) stim) :=
  ⟨8, xsel_run σ stim 8 (Nat.le_refl 8)⟩

/-- Bonus: `xsel` is schedule-deterministic (singleton comb phase). -/
theorem xsel_det : Deterministic xselDesign := by
  sv_prove [xsel_total]

/-! ## Snapshot shape (pure list mathematics) -/

/-- Snapshot-shape helpers (the canonical trace has one fixed shape). -/
@[simp] theorem lookup_sel_state (s a b y : LVec) :
    SvState.lookup [("sel", s), ("a", a), ("b", b), ("y", y)] "sel" = some s := by
  simp [SvState.lookup]

@[simp] theorem lookup_a_state (s a b y : LVec) :
    SvState.lookup [("sel", s), ("a", a), ("b", b), ("y", y)] "a" = some a := by
  simp [SvState.lookup]

@[simp] theorem lookup_b_state (s a b y : LVec) :
    SvState.lookup [("sel", s), ("a", a), ("b", b), ("y", y)] "b" = some b := by
  simp [SvState.lookup]

@[simp] theorem lookup_y_state (s a b y : LVec) :
    SvState.lookup [("sel", s), ("a", a), ("b", b), ("y", y)] "y" = some y := by
  simp [SvState.lookup]

/-- Every canonical-trace snapshot is a settled
`[sel, a, b, y = if sel then a else b]` state — the M0 rendering of "after
combinational settling" (`Sv.comb` is still design-target; see spec.lean). -/
theorem xselTrace_snapshots :
    ∀ (stim : List SvState) (s a b : LVec) (i : Nat) (st : SvState),
      (xselTrace s a b stim)[i]? = some st →
      ∃ s' a' b', st = [("sel", s'), ("a", a'), ("b", b'),
                        ("y", if s'.condTrue then a' else b')] := by
  intro stim
  induction stim with
  | nil => intro s a b i st h; simp [xselTrace] at h
  | cons inp rest ih =>
    intro s a b i st h
    cases i with
    | zero =>
      simp only [xselTrace, List.getElem?_cons_zero, Option.some.injEq] at h
      exact ⟨_, _, _, h.symm⟩
    | succ j =>
      simp only [xselTrace, List.getElem?_cons_succ] at h
      exact ih _ _ _ j st h

/-! ## The two gallery theorems, raw (hypothesis) form -/

/-- **Known select** (raw form): on every completed run, any snapshot whose
settled `sel` is an embedded `Bool` and whose settled data inputs are
embedded `BitVec 8` values shows the Lean-level mux on `y`. -/
theorem xsel_known_raw (σ : ScheduleOracle) {fuel : Nat} {stim tr : List SvState}
    (h : run xselDesign σ fuel stim = .ok tr) (s : Bool) (a b : BitVec 8) :
    ∀ (i : Nat) (st : SvState), tr[i]? = some st →
      SvState.lookup st "sel" = some (LVec.ofBool s) →
      SvState.lookup st "a" = some (LVec.ofBitVec a) →
      SvState.lookup st "b" = some (LVec.ofBitVec b) →
      SvState.lookup st "y" = some (LVec.ofBitVec (if s then a else b)) := by
  have htr : tr = xselTrace (LVec.xVec 1) (LVec.xVec 8) (LVec.xVec 8) stim :=
    run_det h (xsel_run σ stim 8 (Nat.le_refl 8))
  subst htr
  intro i st hi hsel ha hb
  obtain ⟨s', a', b', rfl⟩ := xselTrace_snapshots stim _ _ _ i st hi
  simp only [lookup_sel_state, lookup_a_state, lookup_b_state, lookup_y_state,
    Option.some.injEq] at hsel ha hb ⊢
  subst hsel ha hb
  rw [LVec.condTrue_ofBool]
  cases s <;> simp

/-- **X-optimism** (raw form, LRM §12.4): on every completed run, any
snapshot whose settled `sel` is a single `x` — or `z`, the identical twin —
bit shows `y = b` (the ELSE branch), whatever `b` holds. -/
theorem xsel_x_raw (σ : ScheduleOracle) {fuel : Nat} {stim tr : List SvState}
    (h : run xselDesign σ fuel stim = .ok tr) (v : Logic)
    (hv : v = Logic.lx ∨ v = Logic.lz) :
    ∀ (i : Nat) (st : SvState) (vb : LVec), tr[i]? = some st →
      SvState.lookup st "sel" = some (LVec.ofLogic v) →
      SvState.lookup st "b" = some vb →
      SvState.lookup st "y" = some vb := by
  have htr : tr = xselTrace (LVec.xVec 1) (LVec.xVec 8) (LVec.xVec 8) stim :=
    run_det h (xsel_run σ stim 8 (Nat.le_refl 8))
  subst htr
  intro i st vb hi hsel hb
  obtain ⟨s', a', b', rfl⟩ := xselTrace_snapshots stim _ _ _ i st hi
  simp only [lookup_sel_state, lookup_b_state, lookup_y_state,
    Option.some.injEq] at hsel hb ⊢
  subst hsel hb
  rw [LVec.condTrue_ofLogic]
  rcases hv with rfl | rfl <;> simp

/-! ## The surface forms (spec.lean's statements; `sv_prove` corollaries) -/

/-- **Gallery example 5, known-select form** (`xsel_known`): for every
legal schedule and every stimulus, any settled snapshot with an embedded
`Bool` select and embedded `BitVec 8` data shows
`y = if sel then a else b`. -/
theorem xsel_known (s : Bool) (a b : BitVec 8) :
    xselDesign ⊨ spec fun _stim tr =>
      ∀ (i : Nat) (st : SvState), tr[i]? = some st →
        SvState.lookup st "sel" = some (LVec.ofBool s) →
        SvState.lookup st "a" = some (LVec.ofBitVec a) →
        SvState.lookup st "b" = some (LVec.ofBitVec b) →
        SvState.lookup st "y" = some (LVec.ofBitVec (if s then a else b)) := by
  sv_prove [xsel_known_raw]

/-- **Gallery example 5, X-optimism form** (`xsel_x_else`): a `sel` of `x`
or `z` takes the ELSE branch — `y = b`, never a bitwise `a`/`b` merge
(LRM §12.4: zero, x, or z is not-true). The `v = lx ∨ v = lz` hypothesis
folds the gallery's `Logic.lz` twin into one statement. -/
theorem xsel_x_else (v : Logic) (hv : v = Logic.lx ∨ v = Logic.lz) :
    xselDesign ⊨ spec fun _stim tr =>
      ∀ (i : Nat) (st : SvState) (vb : LVec), tr[i]? = some st →
        SvState.lookup st "sel" = some (LVec.ofLogic v) →
        SvState.lookup st "b" = some vb →
        SvState.lookup st "y" = some vb := by
  sv_prove [xsel_x_raw]

/-- `xsel` really runs, under every schedule (= `xsel_total`). -/
theorem xsel_runs (σ : ScheduleOracle) (stim : List SvState) :
    xselDesign / stim ⇓[σ] xselTrace (LVec.xVec 1) (LVec.xVec 8) (LVec.xVec 8) stim := by
  sv_prove [xsel_total σ stim]

/-! ## Non-vacuity pins (`#guard`)

The canonical trace reproduces the Xcelium-verified outcomes (same values
as `Tests.lean`/the differential harness). -/

private def xselCyc (sel : LVec) : SvState :=
  [("sel", sel), ("a", LVec.ofNat 8 0xAA), ("b", LVec.ofNat 8 0x55)]

-- known select: sel = 1 takes a, sel = 0 takes b
#guard (xselTrace (LVec.xVec 1) (LVec.xVec 8) (LVec.xVec 8)
    [xselCyc (LVec.ofNat 1 1)]).map (SvState.showSignal · "y") == ["10101010"]
#guard (xselTrace (LVec.xVec 1) (LVec.xVec 8) (LVec.xVec 8)
    [xselCyc (LVec.ofNat 1 0)]).map (SvState.showSignal · "y") == ["01010101"]

-- X-optimism: sel = x and sel = z both take the ELSE branch (y = b)
#guard (xselTrace (LVec.xVec 1) (LVec.xVec 8) (LVec.xVec 8)
    [xselCyc (LVec.lit "x")]).map (SvState.showSignal · "y") == ["01010101"]
#guard (xselTrace (LVec.xVec 1) (LVec.xVec 8) (LVec.xVec 8)
    [xselCyc (LVec.lit "z")]).map (SvState.showSignal · "y") == ["01010101"]

end Examples.xsel.proof
