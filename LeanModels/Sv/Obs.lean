import LeanModels.Sv.Semantics

/-!
# Fuel monotonicity, determinism, and the observation spine (`LeanModels.Sv`)

The SV lane's proof-infrastructure layer, built to the Python lane's
ergonomics standard (`LeanModels/Python/Obs.lean`): adding fuel never changes
a decided (non-`timeout`) interpreter result, so the fuel parameter is a pure
implementation detail; at fixed schedule σ the run is deterministic across
fuels; and theorems consume interpreter facts in **threshold form**
(`… ∀ F, f₀ ≤ F → …`) with generous slack constants — never exact-offset
fuel arithmetic.

Structure:

* `Res` monad normalization simp lemmas (`Res.ok_bind`, `Res.bind_eq_ok`, …)
  — the do-notation stepping rules `sv_simp` (end of this file) relies on.
* **Value-core lemma layer** (logically Basic.lean material, kept here so the
  Basic → Ast → Semantics files stay byte-untouched): `LawfulBEq Logic` /
  `LawfulBEq LVec` (hence `LawfulBEq SvState` via the core `Prod`/`List`
  instances — what makes `combSettle`'s `st' == st` check provable on
  *symbolic* states), and the `LVec.ofNat`/`BitVec` bridge
  (`LVec.toNat_ofNat`, `LVec.add_ofBitVec`, …) that lets golden models speak
  `BitVec 8` while the interpreter speaks `LVec`.
* **Schedule-oracle facts**: `Perm` inversion helpers and
  `ScheduleOracle.choose_nil`/`choose_singleton`/`choose_pair` — how `∀ σ`
  proofs case-split the finitely many legal orders; `combSettle_nil` — on a
  design with no comb-phase processes a settle pass is the identity (all five
  M0 designs with comb logic settle in one pass; the three theorem-bearing
  ones have *no* comb processes at all).
* `Res.le` (`x ⊑ y`) — the flat approximation order: `x` is `timeout` or
  already equals `y`. Fuel-indexed runs form a chain in it.
* `fuelMono` — THE theorem: one conjunction over the four functions of the
  interpreter's mutual block (`evalExpr`, `evalExprs`, `execStmt`,
  `execStmts`), proved by a single induction on fuel, glued by the
  congruence lemmas `Res.le_bind`/`Res.le_ite`.
* The scheduler layer's `⊑`-chain (`runCombProcess_le` … `run_le`) — the
  scheduler consumes fuel only through the mutual block and `combSettle`'s
  pass counter, so monotonicity lifts compositionally; `combSettle_le` is
  its own small fuel induction (the settle loop is the scheduler-level fuel
  consumer).
* Per-function `_mono` corollaries in implication form
  (`F fuel = r → r ≠ .timeout → ∀ fuel' ≥ fuel, F fuel' = r`) and
  `_at_least` threshold forms (the `CallsTo.at_least` analogs — destructure
  and splice with `simp (disch := omega) only [h]` / conditional `rw [h]`).
* **Cross-fuel determinism at fixed σ**: `run_det`, and the fuel-abstracted
  judgment `Runs d σ stim tr` (`∃ fuel, run … = .ok tr` — the `⇓[σ]` of
  `docs/sv-spec-surface.md` at cycle level) with `Runs.functional` /
  `Runs.at_least`; `Deterministic d` = all schedules yield the same trace
  (the gallery's `Sv.Deterministic` at M0's cycle level).
* `SvOut` / `Obs` — the observation spine: the three-way outcome partition
  of a run (`yields`/`diverges`/`stuck`), fuel confined inside the
  judgment; `Obs.det` (at most one outcome, stuck *messages* included) and
  `Obs.total` (at least one, classically), hence `Obs.existsUnique`.
-/

namespace LeanModels.Sv

/-! ## `Res` monad normalization

The do-notation stepping rules (global simp lemmas, mirroring the Python
lane's): `bind` on a decided constructor reduces, and `Res.bind_eq_ok` turns
`x >>= f = .ok r` in hypothesis position into an existential nest whose
atoms are the frozen recursive calls. -/

/-- `pure` on `Res` is `Res.ok` (do-notation normalization). -/
@[simp] theorem Res.pure_eq {α : Type} (a : α) : (pure a : Res α) = .ok a := rfl

/-- Bind on an `ok` result steps into the continuation (this is what
advances symbolic execution). -/
@[simp] theorem Res.ok_bind {α β : Type} (a : α) (f : α → Res β) :
    (Res.ok a >>= f) = f a := rfl

/-- Timeouts short-circuit bind (this closes small-fuel goals). -/
@[simp] theorem Res.timeout_bind {α β : Type} (f : α → Res β) :
    ((Res.timeout : Res α) >>= f) = .timeout := rfl

/-- `unsupported` short-circuits bind. -/
@[simp] theorem Res.unsupported_bind {α β : Type} (msg : String) (f : α → Res β) :
    ((Res.unsupported msg : Res α) >>= f) = .unsupported msg := rfl

/-- Inversion of a successful bind: the intermediate result must itself be
`ok`. Under `simp` this turns a symbolically-executed hypothesis into a nest
of existentials — `obtain` them and feed each to the relevant lemma. -/
@[simp] theorem Res.bind_eq_ok {α β : Type} {x : Res α} {f : α → Res β} {b : β} :
    x >>= f = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp

/-! ## Value-core lemma layer

Logically `Basic.lean` material (it mentions only `Logic`/`LVec`); kept here
so `Basic.lean` stays byte-untouched during the concurrent workflows.

The `LawfulBEq` instances make `x == x` provable for *symbolic* values —
`combSettle` compares whole states with `==`, so without them no forward
execution of a settle pass on a symbolic state is possible. The
`ofNat`/`BitVec` bridge is what lets spec-side golden models use `BitVec w`
(where `bv_decide`-style automation lives, per the gallery) while the
interpreter computes on `LVec`. -/

instance : LawfulBEq Logic where
  eq_of_beq {a b} h := by
    cases a <;> cases b <;> first | rfl | exact absurd h (by decide)
  rfl {a} := by cases a <;> decide

/-- The derived `BEq LVec` is bit-array equality (definitional unfold). -/
theorem LVec.beq_def (a b : LVec) : (a == b) = (a.bits == b.bits) := rfl

instance : LawfulBEq LVec where
  eq_of_beq {a b} h := by
    cases a; cases b
    rw [LVec.beq_def] at h
    exact congrArg LVec.mk (eq_of_beq h)
  rfl {a} := by rw [LVec.beq_def]; exact beq_self_eq_true a.bits

/-- The LSB-peeling decomposition of `% 2 ^ (w + 1)` (the core library's
`Nat.mod_pow_succ` peels the MSB instead). -/
private theorem two_pow_succ_mod (w n : Nat) :
    n % 2 ^ (w + 1) = 2 * (n / 2 % 2 ^ w) + n % 2 := by
  have hm : 0 < 2 ^ w := Nat.two_pow_pos w
  have hpow : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [Nat.pow_succ, Nat.mul_comm]
  conv => lhs; rw [← Nat.div_add_mod n 2]; rw [← Nat.div_add_mod (n / 2) (2 ^ w)]
  rw [hpow, Nat.mul_add, ← Nat.mul_assoc, Nat.add_assoc, Nat.mul_add_mod]
  have hs : n / 2 % 2 ^ w < 2 ^ w := Nat.mod_lt _ hm
  have hr : n % 2 < 2 := Nat.mod_lt _ (by decide)
  exact Nat.mod_eq_of_lt (by omega)

/-- `LVec.ofNat` really is the binary representation: its unsigned value is
`n % 2 ^ w`. -/
theorem LVec.toNat_ofNat (w n : Nat) : (LVec.ofNat w n).toNat = n % 2 ^ w := by
  suffices h : ∀ (w n : Nat),
      (List.ofFn (n := w) fun i => if n.testBit i then Logic.l1 else Logic.l0).foldr
        (fun b acc => 2 * acc + (if b == .l1 then 1 else 0)) 0 = n % 2 ^ w by
    have h' := h w n
    simp only [LVec.ofNat, LVec.toNat]
    rw [← Array.foldr_toList, Array.toList_ofFn]
    exact h'
  intro w
  induction w with
  | zero => intro n; simp [List.ofFn, Nat.mod_one]
  | succ w ih =>
    intro n
    rw [List.ofFn_succ, List.foldr_cons]
    simp only [Fin.val_succ, Nat.testBit_add_one]
    rw [ih (n / 2), two_pow_succ_mod]
    rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [Nat.testBit_zero, h]

/-- `LVec.ofNat` vectors are fully known (no `x`/`z` bits). -/
theorem LVec.allKnown_ofNat (w n : Nat) : (LVec.ofNat w n).allKnown = true := by
  simp only [LVec.ofNat, LVec.allKnown]
  rw [← Array.all_toList, Array.toList_ofFn, List.all_eq_true]
  intro b hb
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
  by_cases h : n.testBit i <;> simp [h, Logic.isKnown]

theorem LVec.width_ofNat (w n : Nat) : (LVec.ofNat w n).width = w := by
  simp [LVec.ofNat, LVec.width]

theorem LVec.toNat?_ofNat (w n : Nat) :
    (LVec.ofNat w n).toNat? = some (n % 2 ^ w) := by
  simp [LVec.toNat?, LVec.allKnown_ofNat, LVec.toNat_ofNat]

/-- `LVec.ofNat w` only sees its argument mod `2 ^ w`. -/
theorem LVec.ofNat_emod (w n : Nat) : LVec.ofNat w (n % 2 ^ w) = LVec.ofNat w n := by
  simp only [LVec.ofNat]
  congr 1
  apply congrArg
  funext i
  rw [Nat.testBit_mod_two_pow]
  simp [i.isLt]

/-- The `BitVec` bridge for `+`: on embedded (fully known) vectors,
`LVec.add` is `BitVec` addition — the lemma that turns interpreter
arithmetic into golden-model arithmetic (`counterModel`-style specs). -/
theorem LVec.add_ofBitVec {w : Nat} (x y : BitVec w) :
    (LVec.ofBitVec x).add (LVec.ofBitVec y) = LVec.ofBitVec (x + y) := by
  simp only [LVec.ofBitVec, LVec.add, LVec.toNat?_ofNat, LVec.arithWidth,
    LVec.width_ofNat, Nat.max_self, Nat.mod_eq_of_lt x.isLt, Nat.mod_eq_of_lt y.isLt]
  rw [← LVec.ofNat_emod, ← BitVec.toNat_add]

/-! ## Schedule-oracle facts

`choose_perm` pins each oracle invocation to a permutation of the ready
list; for the M0 designs the ready lists have 0, 1, or 2 elements, so these
inversions turn `∀ σ` into a finite case split (`choose_pair` is the whole
schedule freedom of `race_blk`/`swap_nba`; `choose_singleton` is the
σ-irrelevance of single-process designs like `counter`). -/

/-- A permutation of `[]` is `[]`. -/
theorem perm_nil_inv {α : Type} {l : List α} (h : l.Perm []) : l = [] := by
  have := h.length_eq
  simp at this
  simp [this]

/-- A permutation of a singleton is that singleton. -/
theorem perm_singleton_inv {α : Type} {l : List α} {a : α} (h : l.Perm [a]) :
    l = [a] := by
  match l, h.length_eq with
  | [x], _ =>
    have hx : x ∈ [a] := h.mem_iff.mp (List.mem_cons_self ..)
    simp at hx
    simp [hx]

/-- A permutation of a pair is one of the two orders. -/
theorem perm_pair_inv {α : Type} {l : List α} {a b : α} (h : l.Perm [a, b]) :
    l = [a, b] ∨ l = [b, a] := by
  match l, h.length_eq with
  | [x, y], _ =>
    have hx : x ∈ [a, b] := h.mem_iff.mp (by simp)
    have hy : y ∈ [a, b] := h.mem_iff.mp (by simp)
    have ha : a ∈ [x, y] := h.mem_iff.mpr (by simp)
    have hb : b ∈ [x, y] := h.mem_iff.mpr (by simp)
    simp at hx hy ha hb
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp_all

/-- Every legal schedule leaves the empty ready list empty. -/
theorem ScheduleOracle.choose_nil (σ : ScheduleOracle) (k : Nat) :
    σ.choose k [] = [] :=
  perm_nil_inv (σ.choose_perm k [])

/-- Every legal schedule runs a single ready process — σ-irrelevance of
singleton phases (e.g. `counter`'s edge phase). -/
theorem ScheduleOracle.choose_singleton (σ : ScheduleOracle) (k a : Nat) :
    σ.choose k [a] = [a] :=
  perm_singleton_inv (σ.choose_perm k [a])

/-- A two-process ready list runs in one of exactly two orders — the whole
schedule freedom of `race_blk`/`swap_nba`. -/
theorem ScheduleOracle.choose_pair (σ : ScheduleOracle) (k a b : Nat) :
    σ.choose k [a, b] = [a, b] ∨ σ.choose k [a, b] = [b, a] :=
  perm_pair_inv (σ.choose_perm k [a, b])

/-- On a design with no comb-phase processes, comb settle is the identity in
one pass (at any successor fuel): the pass runs nothing, the state is
unchanged, the fixpoint check succeeds. All three theorem-bearing M0 designs
(`counter`, `race_blk`, `swap_nba`) have `combIndices = []`. -/
theorem combSettle_nil {d : Design} (hd : d.combIndices = []) (σ : ScheduleOracle)
    (fuel : Nat) (st : SvState) (k : Nat) :
    combSettle d σ (fuel + 1) st k = .ok (st, k + 1) := by
  simp only [combSettle, hd, σ.choose_nil, combPass]
  simp

/-! ## The approximation order on results -/

/-- Flat approximation order on interpreter results: `x ⊑ y` iff `x` is
`timeout` (the run gave up) or `x = y` (the run decided, and `y` agrees).
`fuelMono` shows every interpreter function is monotone in fuel wrt `⊑`. -/
protected def Res.le {α : Type} (x y : Res α) : Prop :=
  x = .timeout ∨ x = y

@[inherit_doc] scoped infix:50 " ⊑ " => Res.le

theorem Res.le_iff {α : Type} {x y : Res α} :
    x ⊑ y ↔ (x = .timeout ∨ x = y) := Iff.rfl

theorem Res.le_refl {α : Type} (x : Res α) : x ⊑ x := Or.inr rfl

theorem Res.timeout_le {α : Type} (y : Res α) : (.timeout : Res α) ⊑ y :=
  Or.inl rfl

/-- A decided (non-`timeout`) lower bound is already the value: `⊑` collapses
to equality. This is the extraction step of every `_mono` corollary. -/
theorem Res.le_eq {α : Type} {x y : Res α} (h : x ⊑ y) (hx : x ≠ .timeout) :
    x = y := (Res.le_iff.mp h).resolve_left hx

/-- Congruence of `⊑` under `bind`: run the prefix, then the continuation
pointwise (each by its own proof, or reflexivity for fuel-free tails). -/
theorem Res.le_bind {α β : Type} {x x' : Res α} {f f' : α → Res β}
    (hx : x ⊑ x') (hf : ∀ a, f a ⊑ f' a) : (x >>= f) ⊑ (x' >>= f') := by
  rcases hx with h | h
  · subst h; exact Or.inl rfl
  · subst h
    cases x with
    | ok a => exact hf a
    | timeout => exact Or.inl rfl
    | unsupported msg => exact Or.inr rfl

/-- Congruence of `⊑` under `if`: same condition on both sides, each branch
by its own proof. -/
theorem Res.le_ite {α : Type} {c : Prop} [Decidable c] {x x' y y' : Res α}
    (hx : x ⊑ x') (hy : y ⊑ y') :
    (if c then x else y) ⊑ (if c then x' else y') := by
  by_cases h : c
  · simpa only [if_pos h] using hx
  · simpa only [if_neg h] using hy

/-! ## Fuel monotonicity — the enabling theorem -/

/-- **Fuel monotonicity**, one conjunction over the whole mutual block, by
induction on fuel: for every interpreter function `F` and `fuel ≤ fuel'`,
`F fuel ⊑ F fuel'` — a run that decided keeps its exact result at any higher
fuel. Conjunct order: `evalExpr`, `evalExprs`, `execStmt`, `execStmts` (the
order of `Semantics.lean`'s mutual block). Consume it through the
per-function `_le`/`_mono` corollaries below. -/
theorem fuelMono (fuel : Nat) :
    (∀ (st : SvState) (e : Expr) (fuel' : Nat), fuel ≤ fuel' →
      evalExpr fuel st e ⊑ evalExpr fuel' st e) ∧
    (∀ (st : SvState) (es : List Expr) (fuel' : Nat), fuel ≤ fuel' →
      evalExprs fuel st es ⊑ evalExprs fuel' st es) ∧
    (∀ (st : SvState) (nba : NbaQueue) (s : Stmt) (fuel' : Nat), fuel ≤ fuel' →
      execStmt fuel st nba s ⊑ execStmt fuel' st nba s) ∧
    (∀ (st : SvState) (nba : NbaQueue) (ss : List Stmt) (fuel' : Nat), fuel ≤ fuel' →
      execStmts fuel st nba ss ⊑ execStmts fuel' st nba ss) := by
  induction fuel with
  | zero =>
    -- Fuel 0 is `.timeout` everywhere, the bottom of `⊑`.
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact fun st e fuel' _ => Or.inl (by simp [evalExpr])
    · exact fun st es fuel' _ => Or.inl (by simp [evalExprs])
    · exact fun st nba s fuel' _ => Or.inl (by simp [execStmt])
    · exact fun st nba ss fuel' _ => Or.inl (by simp [execStmts])
  | succ fuel ih =>
    obtain ⟨ihE, ihEs, ihS, ihSs⟩ := ih
    refine ⟨?_, ?_, ?_, ?_⟩
    -- evalExpr
    · intro st e fuel' hf
      cases fuel' with
      | zero => exact absurd hf (Nat.not_succ_le_zero fuel)
      | succ k =>
        have hk : fuel ≤ k := Nat.le_of_succ_le_succ hf
        cases e with
        | lit v => simp only [evalExpr]; exact Res.le_refl _
        | ident name => simp only [evalExpr]; exact Res.le_refl _
        | unary op a =>
          simp only [evalExpr]
          exact Res.le_bind (ihE st a k hk) fun v => Res.le_refl _
        | binary op l r =>
          simp only [evalExpr]
          exact Res.le_bind (ihE st l k hk) fun a =>
            Res.le_bind (ihE st r k hk) fun b => Res.le_refl _
        | ternary c t f =>
          simp only [evalExpr]
          exact Res.le_bind (ihE st c k hk) fun cv =>
            Res.le_bind (ihE st t k hk) fun tv =>
              Res.le_bind (ihE st f k hk) fun fv => Res.le_refl _
        | concat parts =>
          simp only [evalExpr]
          exact Res.le_bind (ihEs st parts.toList k hk) fun vs => Res.le_refl _
        | unsupported svKind text => simp only [evalExpr]; exact Res.le_refl _
    -- evalExprs
    · intro st es fuel' hf
      cases fuel' with
      | zero => exact absurd hf (Nat.not_succ_le_zero fuel)
      | succ k =>
        have hk : fuel ≤ k := Nat.le_of_succ_le_succ hf
        cases es with
        | nil => simp only [evalExprs]; exact Res.le_refl _
        | cons e rest =>
          simp only [evalExprs]
          exact Res.le_bind (ihE st e k hk) fun v =>
            Res.le_bind (ihEs st rest k hk) fun vs => Res.le_refl _
    -- execStmt
    · intro st nba s fuel' hf
      cases fuel' with
      | zero => exact absurd hf (Nat.not_succ_le_zero fuel)
      | succ k =>
        have hk : fuel ≤ k := Nat.le_of_succ_le_succ hf
        cases s with
        | blockingAssign target value =>
          simp only [execStmt]
          exact Res.le_bind (ihE st value k hk) fun v => Res.le_refl _
        | nbaAssign target value =>
          simp only [execStmt]
          exact Res.le_bind (ihE st value k hk) fun v => Res.le_refl _
        | ifStmt cond thenB elseB =>
          simp only [execStmt]
          refine Res.le_bind (ihE st cond k hk) fun c => ?_
          refine Res.le_ite (ihS st nba thenB k hk) ?_
          cases elseB with
          | some s => exact ihS st nba s k hk
          | none => exact Res.le_refl _
        | block body =>
          simp only [execStmt]
          exact ihSs st nba body.toList k hk
        | unsupported svKind text => simp only [execStmt]; exact Res.le_refl _
    -- execStmts
    · intro st nba ss fuel' hf
      cases fuel' with
      | zero => exact absurd hf (Nat.not_succ_le_zero fuel)
      | succ k =>
        have hk : fuel ≤ k := Nat.le_of_succ_le_succ hf
        cases ss with
        | nil => simp only [execStmts]; exact Res.le_refl _
        | cons s rest =>
          simp only [execStmts]
          refine Res.le_bind (ihS st nba s k hk) fun p => ?_
          obtain ⟨st', nba'⟩ := p
          exact ihSs st' nba' rest k hk

/-! ## The `⊑`-chain through the scheduler

The scheduler layer consumes fuel only through the mutual block and
`combSettle`'s pass counter, so `⊑`-monotonicity lifts compositionally.
These are the building-block forms; the implication-form `_mono` and the
threshold-form `_at_least` corollaries below are what proofs consume. -/

theorem evalExpr_le {fuel fuel' : Nat} (h : fuel ≤ fuel') (st : SvState) (e : Expr) :
    evalExpr fuel st e ⊑ evalExpr fuel' st e :=
  (fuelMono fuel).1 st e fuel' h

theorem evalExprs_le {fuel fuel' : Nat} (h : fuel ≤ fuel') (st : SvState)
    (es : List Expr) : evalExprs fuel st es ⊑ evalExprs fuel' st es :=
  (fuelMono fuel).2.1 st es fuel' h

theorem execStmt_le {fuel fuel' : Nat} (h : fuel ≤ fuel') (st : SvState)
    (nba : NbaQueue) (s : Stmt) : execStmt fuel st nba s ⊑ execStmt fuel' st nba s :=
  (fuelMono fuel).2.2.1 st nba s fuel' h

theorem execStmts_le {fuel fuel' : Nat} (h : fuel ≤ fuel') (st : SvState)
    (nba : NbaQueue) (ss : List Stmt) :
    execStmts fuel st nba ss ⊑ execStmts fuel' st nba ss :=
  (fuelMono fuel).2.2.2 st nba ss fuel' h

theorem runCombProcess_le {fuel fuel' : Nat} (h : fuel ≤ fuel') (st : SvState)
    (p : Process) : runCombProcess fuel st p ⊑ runCombProcess fuel' st p := by
  cases p with
  | alwaysFF clock body => exact Res.le_refl _
  | alwaysPlain clock body => exact Res.le_refl _
  | alwaysComb body =>
    simp only [runCombProcess]
    exact Res.le_bind (execStmt_le h st [] body) fun p => Res.le_refl _
  | assign target value =>
    simp only [runCombProcess]
    exact Res.le_bind (evalExpr_le h st value) fun v => Res.le_refl _
  | unsupported svKind text => exact Res.le_refl _

theorem combPass_le (d : Design) {fuel fuel' : Nat} (h : fuel ≤ fuel') :
    ∀ (is : List Nat) (st : SvState), combPass d fuel st is ⊑ combPass d fuel' st is := by
  intro is
  induction is with
  | nil => intro st; exact Res.le_refl _
  | cons i rest ih =>
    intro st
    simp only [combPass]
    cases d.processes[i]? with
    | some p => exact Res.le_bind (runCombProcess_le h st p) fun st' => ih st'
    | none => exact Res.le_bind (Res.le_refl _) fun st' => ih st'

/-- `combSettle` is the scheduler-level fuel consumer (fuel bounds the pass
count), so its monotonicity is its own small induction on fuel. -/
theorem combSettle_le (d : Design) (σ : ScheduleOracle) :
    ∀ {fuel fuel' : Nat}, fuel ≤ fuel' → ∀ (st : SvState) (k : Nat),
      combSettle d σ fuel st k ⊑ combSettle d σ fuel' st k := by
  intro fuel
  induction fuel with
  | zero => intro fuel' h st k; exact Or.inl (by simp [combSettle])
  | succ f ih =>
    intro fuel' h st k
    cases fuel' with
    | zero => exact absurd h (Nat.not_succ_le_zero f)
    | succ f' =>
      have hf : f ≤ f' := Nat.le_of_succ_le_succ h
      simp only [combSettle]
      refine Res.le_bind (combPass_le d hf _ st) fun st' => ?_
      exact Res.le_ite (Res.le_refl _) (ih hf st' (k + 1))

theorem runEdgeProcess_le {fuel fuel' : Nat} (h : fuel ≤ fuel') (st : SvState)
    (nba : NbaQueue) (p : Process) :
    runEdgeProcess fuel st nba p ⊑ runEdgeProcess fuel' st nba p := by
  cases p with
  | alwaysFF clock body => exact execStmt_le h st nba body
  | alwaysPlain clock body => exact execStmt_le h st nba body
  | alwaysComb body => exact Res.le_refl _
  | assign target value => exact Res.le_refl _
  | unsupported svKind text => exact Res.le_refl _

theorem edgePass_le (d : Design) {fuel fuel' : Nat} (h : fuel ≤ fuel') :
    ∀ (is : List Nat) (st : SvState) (nba : NbaQueue),
      edgePass d fuel st nba is ⊑ edgePass d fuel' st nba is := by
  intro is
  induction is with
  | nil => intro st nba; exact Res.le_refl _
  | cons i rest ih =>
    intro st nba
    simp only [edgePass]
    cases d.processes[i]? with
    | some p => exact Res.le_bind (runEdgeProcess_le h st nba p) fun q => ih q.1 q.2
    | none => exact Res.le_bind (Res.le_refl _) fun q => ih q.1 q.2

theorem cycleStep_le (d : Design) (σ : ScheduleOracle) {fuel fuel' : Nat}
    (h : fuel ≤ fuel') (inputs st : SvState) (k : Nat) :
    cycleStep d σ fuel inputs st k ⊑ cycleStep d σ fuel' inputs st k := by
  simp only [cycleStep]
  refine Res.le_bind (combSettle_le d σ h _ _) fun p => ?_
  obtain ⟨st1, k1⟩ := p
  refine Res.le_bind (edgePass_le d h _ _ _) fun q => ?_
  obtain ⟨st2, nba⟩ := q
  exact combSettle_le d σ h _ _

theorem runFrom_le (d : Design) (σ : ScheduleOracle) {fuel fuel' : Nat}
    (h : fuel ≤ fuel') :
    ∀ (stim : List SvState) (st : SvState) (k : Nat),
      runFrom d σ fuel st k stim ⊑ runFrom d σ fuel' st k stim := by
  intro stim
  induction stim with
  | nil => intro st k; exact Res.le_refl _
  | cons inputs rest ih =>
    intro st k
    simp only [runFrom]
    refine Res.le_bind (cycleStep_le d σ h inputs st k) fun p => ?_
    obtain ⟨st', k'⟩ := p
    exact Res.le_bind (ih st' k') fun tr => Res.le_refl _

theorem run_le (d : Design) (σ : ScheduleOracle) {fuel fuel' : Nat}
    (h : fuel ≤ fuel') (stim : List SvState) :
    run d σ fuel stim ⊑ run d σ fuel' stim :=
  runFrom_le d σ h stim (initState d) 0

/-! ## Per-function corollaries (implication and threshold forms) -/

private theorem mono_of_le {α : Type} {x y r : Res α}
    (hle : x ⊑ y) (h : x = r) (hr : r ≠ .timeout) : y = r := by
  subst h; exact (Res.le_eq hle hr).symm

/-- Fuel monotonicity for `evalExpr`: a decided result survives any fuel
increase, exactly. -/
theorem evalExpr_mono {fuel : Nat} {st : SvState} {e : Expr} {r : Res LVec}
    (h : evalExpr fuel st e = r) (hr : r ≠ .timeout) :
    ∀ fuel' ≥ fuel, evalExpr fuel' st e = r := fun fuel' hf =>
  mono_of_le (evalExpr_le (fuel' := fuel') hf st e) h hr

/-- Fuel monotonicity for `evalExprs`. -/
theorem evalExprs_mono {fuel : Nat} {st : SvState} {es : List Expr}
    {r : Res (List LVec)} (h : evalExprs fuel st es = r) (hr : r ≠ .timeout) :
    ∀ fuel' ≥ fuel, evalExprs fuel' st es = r := fun fuel' hf =>
  mono_of_le (evalExprs_le (fuel' := fuel') hf st es) h hr

/-- Fuel monotonicity for `execStmt`. -/
theorem execStmt_mono {fuel : Nat} {st : SvState} {nba : NbaQueue} {s : Stmt}
    {r : Res (SvState × NbaQueue)} (h : execStmt fuel st nba s = r)
    (hr : r ≠ .timeout) : ∀ fuel' ≥ fuel, execStmt fuel' st nba s = r :=
  fun fuel' hf => mono_of_le (execStmt_le (fuel' := fuel') hf st nba s) h hr

/-- Fuel monotonicity for `execStmts`. -/
theorem execStmts_mono {fuel : Nat} {st : SvState} {nba : NbaQueue}
    {ss : List Stmt} {r : Res (SvState × NbaQueue)}
    (h : execStmts fuel st nba ss = r) (hr : r ≠ .timeout) :
    ∀ fuel' ≥ fuel, execStmts fuel' st nba ss = r := fun fuel' hf =>
  mono_of_le (execStmts_le (fuel' := fuel') hf st nba ss) h hr

/-- Fuel monotonicity for `combSettle`: a settled state (and pass counter)
survives any fuel increase. -/
theorem combSettle_mono {d : Design} {σ : ScheduleOracle} {fuel : Nat}
    {st : SvState} {k : Nat} {r : Res (SvState × Nat)}
    (h : combSettle d σ fuel st k = r) (hr : r ≠ .timeout) :
    ∀ fuel' ≥ fuel, combSettle d σ fuel' st k = r := fun fuel' hf =>
  mono_of_le (combSettle_le (fuel' := fuel') d σ hf st k) h hr

/-- Fuel monotonicity for `cycleStep`. -/
theorem cycleStep_mono {d : Design} {σ : ScheduleOracle} {fuel : Nat}
    {inputs st : SvState} {k : Nat} {r : Res (SvState × Nat)}
    (h : cycleStep d σ fuel inputs st k = r) (hr : r ≠ .timeout) :
    ∀ fuel' ≥ fuel, cycleStep d σ fuel' inputs st k = r := fun fuel' hf =>
  mono_of_le (cycleStep_le (fuel' := fuel') d σ hf inputs st k) h hr

/-- Fuel monotonicity for `runFrom`. -/
theorem runFrom_mono {d : Design} {σ : ScheduleOracle} {fuel : Nat}
    {st : SvState} {k : Nat} {stim : List SvState} {r : Res (List SvState)}
    (h : runFrom d σ fuel st k stim = r) (hr : r ≠ .timeout) :
    ∀ fuel' ≥ fuel, runFrom d σ fuel' st k stim = r := fun fuel' hf =>
  mono_of_le (runFrom_le (fuel' := fuel') d σ hf stim st k) h hr

/-- Fuel monotonicity for `run`: a decided trace (`ok` or `unsupported`) is
the same at every larger fuel. -/
theorem run_mono {d : Design} {σ : ScheduleOracle} {fuel : Nat}
    {stim : List SvState} {r : Res (List SvState)}
    (h : run d σ fuel stim = r) (hr : r ≠ .timeout) :
    ∀ fuel' ≥ fuel, run d σ fuel' stim = r := fun fuel' hf =>
  mono_of_le (run_le (fuel' := fuel') d σ hf stim) h hr

/-- Threshold form of a completed `cycleStep`: succeed once, succeed at every
sufficiently large fuel. The resulting `h : ∀ F, f₀ ≤ F → cycleStep … F … =
.ok p` is a *conditional rewrite rule* — splice it into a symbolic execution
with `simp (disch := omega) only [h]` (or a conditional `rw [h]` + `omega`),
with no exact-offset fuel bookkeeping. -/
theorem cycleStep_at_least {d : Design} {σ : ScheduleOracle} {inputs st : SvState}
    {k : Nat} {p : SvState × Nat}
    (h : ∃ fuel, cycleStep d σ fuel inputs st k = .ok p) :
    ∃ f₀, ∀ F, f₀ ≤ F → cycleStep d σ F inputs st k = .ok p := by
  obtain ⟨fuel, hf⟩ := h
  exact ⟨fuel, fun F hF => cycleStep_mono hf (by simp) F hF⟩

/-- Threshold form of a completed `combSettle` (the loop-lemma analog:
comb-settle is the fixpoint recursion `sv_simp` freezes). -/
theorem combSettle_at_least {d : Design} {σ : ScheduleOracle} {st : SvState}
    {k : Nat} {p : SvState × Nat}
    (h : ∃ fuel, combSettle d σ fuel st k = .ok p) :
    ∃ f₀, ∀ F, f₀ ≤ F → combSettle d σ F st k = .ok p := by
  obtain ⟨fuel, hf⟩ := h
  exact ⟨fuel, fun F hF => combSettle_mono hf (by simp) F hF⟩

/-- Threshold form of a completed `run`. -/
theorem run_at_least {d : Design} {σ : ScheduleOracle} {stim tr : List SvState}
    (h : ∃ fuel, run d σ fuel stim = .ok tr) :
    ∃ f₀, ∀ F, f₀ ≤ F → run d σ F stim = .ok tr := by
  obtain ⟨fuel, hf⟩ := h
  exact ⟨fuel, fun F hF => run_mono hf (by simp) F hF⟩

/-! ## Cross-fuel determinism at fixed σ -/

/-- Any two decided (non-`timeout`) results of the same run, at *any* two
fuels, are equal — messages included. Fuel is an implementation detail. -/
theorem run_res_det {d : Design} {σ : ScheduleOracle} {stim : List SvState}
    {fuel₁ fuel₂ : Nat} {r₁ r₂ : Res (List SvState)}
    (h₁ : run d σ fuel₁ stim = r₁) (h₂ : run d σ fuel₂ stim = r₂)
    (hr₁ : r₁ ≠ .timeout) (hr₂ : r₂ ≠ .timeout) : r₁ = r₂ := by
  rcases Nat.le_total fuel₁ fuel₂ with hle | hle
  · exact (run_mono h₁ hr₁ fuel₂ hle).symm.trans h₂
  · exact h₁.symm.trans (run_mono h₂ hr₂ fuel₁ hle)

/-- **Cross-fuel determinism**: two successful traces of the same design,
stimulus, and schedule are equal, whatever the fuels. -/
theorem run_det {d : Design} {σ : ScheduleOracle} {stim : List SvState}
    {fuel₁ fuel₂ : Nat} {tr₁ tr₂ : List SvState}
    (h₁ : run d σ fuel₁ stim = .ok tr₁) (h₂ : run d σ fuel₂ stim = .ok tr₂) :
    tr₁ = tr₂ :=
  Res.ok.inj (run_res_det h₁ h₂ (by simp) (by simp))

/-! ## The run judgment and the observation spine -/

/-- The fuel-abstracted run judgment — `docs/sv-spec-surface.md`'s
`m / stim ⇓[σ] tr` at M0's cycle level: *some* fuel completes the run with
trace `tr` (fuel monotonicity then makes every larger fuel agree). -/
def Runs (d : Design) (σ : ScheduleOracle) (stim tr : List SvState) : Prop :=
  ∃ fuel, run d σ fuel stim = .ok tr

theorem Runs.intro {d : Design} {σ : ScheduleOracle} {stim tr : List SvState}
    (fuel : Nat) (h : run d σ fuel stim = .ok tr) : Runs d σ stim tr :=
  ⟨fuel, h⟩

/-- `Runs` is functional: at fixed σ the trace is unique across all fuels. -/
theorem Runs.functional {d : Design} {σ : ScheduleOracle} {stim tr₁ tr₂ : List SvState}
    (h₁ : Runs d σ stim tr₁) (h₂ : Runs d σ stim tr₂) : tr₁ = tr₂ := by
  obtain ⟨fuel₁, hf₁⟩ := h₁
  obtain ⟨fuel₂, hf₂⟩ := h₂
  exact run_det hf₁ hf₂

/-- Threshold form of `Runs` (the `CallsTo.at_least` analog). -/
theorem Runs.at_least {d : Design} {σ : ScheduleOracle} {stim tr : List SvState}
    (h : Runs d σ stim tr) : ∃ f₀, ∀ F, f₀ ≤ F → run d σ F stim = .ok tr :=
  run_at_least h

/-- All legal schedules yield the same trace — the gallery's
`Sv.Deterministic` at M0's cycle level. `swap_nba` satisfies it, `race_blk`
refutes it (`Examples/swap_nba/proof.lean`, `Examples/race_blk/proof.lean`). -/
def Deterministic (d : Design) : Prop :=
  ∀ (σ₁ σ₂ : ScheduleOracle) (stim tr₁ tr₂ : List SvState),
    Runs d σ₁ stim tr₁ → Runs d σ₂ stim tr₂ → tr₁ = tr₂

/-- Everything a (σ-fixed) SV run can be observed to do — the outcome
alphabet of the `Obs` judgment. -/
inductive SvOut where
  /-- Completes, with the cycle-snapshot trace `tr`. -/
  | yields (tr : List SvState)
  /-- Never settles: every fuel times out (combinational loop). -/
  | diverges
  /-- Leaves the supported semantic tier (`Res.unsupported msg`) — loud,
  and distinct from `diverges`. -/
  | stuck (msg : String)
deriving Repr, Inhabited, BEq

/-- The observation judgment: running `d` under stimulus `stim` and schedule
σ is observed to do `o`. This is the fuel boundary: no judgment built on
`Obs` mentions fuel again. -/
def Obs (d : Design) (σ : ScheduleOracle) (stim : List SvState) : SvOut → Prop
  | .yields tr => ∃ fuel, run d σ fuel stim = .ok tr
  | .diverges => ∀ fuel, run d σ fuel stim = .timeout
  | .stuck msg => ∃ fuel, run d σ fuel stim = .unsupported msg

/-- `yields` is exactly the spec-layer `Runs`. -/
@[simp] theorem Obs.yields_iff {d : Design} {σ : ScheduleOracle}
    {stim tr : List SvState} : Obs d σ stim (.yields tr) ↔ Runs d σ stim tr :=
  Iff.rfl

@[simp] theorem Obs.diverges_iff {d : Design} {σ : ScheduleOracle}
    {stim : List SvState} :
    Obs d σ stim .diverges ↔ ∀ fuel, run d σ fuel stim = .timeout := Iff.rfl

@[simp] theorem Obs.stuck_iff {d : Design} {σ : ScheduleOracle}
    {stim : List SvState} {msg : String} :
    Obs d σ stim (.stuck msg) ↔ ∃ fuel, run d σ fuel stim = .unsupported msg :=
  Iff.rfl

/-- The decided `Res` value an outcome asserts (`diverges ↦ .timeout` — note
the readings differ: `Obs`'s `diverges` is "timeout at *every* fuel").
Injective, which is what reduces `Obs.det` to `run_res_det`. -/
def SvOut.asRes : SvOut → Res (List SvState)
  | .yields tr => .ok tr
  | .diverges => .timeout
  | .stuck msg => .unsupported msg

theorem SvOut.asRes_inj {o₁ o₂ : SvOut} (h : o₁.asRes = o₂.asRes) : o₁ = o₂ := by
  cases o₁ <;> cases o₂ <;> simp_all [SvOut.asRes]

theorem SvOut.asRes_ne_timeout {o : SvOut} (h : o ≠ .diverges) :
    o.asRes ≠ .timeout := by
  cases o <;> first | exact absurd rfl h | simp [SvOut.asRes]

/-- A non-`diverges` outcome carries a fuel witness deciding exactly its
`asRes` value. -/
theorem Obs.decided {d : Design} {σ : ScheduleOracle} {stim : List SvState}
    {o : SvOut} (h : Obs d σ stim o) (hd : o ≠ .diverges) :
    ∃ fuel, run d σ fuel stim = o.asRes := by
  cases o with
  | yields tr => exact h
  | diverges => exact absurd rfl hd
  | stuck msg => exact h

/-- **Outcome determinism** at fixed σ: a run has at most one observable
outcome — traces and stuck *messages* included. Decided-vs-decided is
`run_res_det` (fuel monotonicity) through the injection `SvOut.asRes`;
decided-vs-`diverges` is a direct contradiction at the deciding fuel. -/
theorem Obs.det {d : Design} {σ : ScheduleOracle} {stim : List SvState}
    {o₁ o₂ : SvOut} (h₁ : Obs d σ stim o₁) (h₂ : Obs d σ stim o₂) : o₁ = o₂ := by
  by_cases d₁ : o₁ = .diverges <;> by_cases d₂ : o₂ = .diverges
  · rw [d₁, d₂]
  · subst d₁
    obtain ⟨fuel, hf⟩ := h₂.decided d₂
    exact absurd (hf.symm.trans (Obs.diverges_iff.mp h₁ fuel))
      (SvOut.asRes_ne_timeout d₂)
  · subst d₂
    obtain ⟨fuel, hf⟩ := h₁.decided d₁
    exact absurd (hf.symm.trans (Obs.diverges_iff.mp h₂ fuel))
      (SvOut.asRes_ne_timeout d₁)
  · obtain ⟨fuel₁, hf₁⟩ := h₁.decided d₁
    obtain ⟨fuel₂, hf₂⟩ := h₂.decided d₂
    exact SvOut.asRes_inj (run_res_det hf₁ hf₂
      (SvOut.asRes_ne_timeout d₁) (SvOut.asRes_ne_timeout d₂))

/-- **Outcome totality** (classical): every run observes *some* outcome —
the three `SvOut` cases partition behaviours. -/
theorem Obs.total (d : Design) (σ : ScheduleOracle) (stim : List SvState) :
    ∃ o, Obs d σ stim o := by
  by_cases h : ∀ fuel, run d σ fuel stim = .timeout
  · exact ⟨.diverges, h⟩
  · obtain ⟨fuel, hf⟩ := Classical.not_forall.mp h
    cases hr : run d σ fuel stim with
    | ok tr => exact ⟨.yields tr, fuel, hr⟩
    | timeout => exact absurd hr hf
    | unsupported msg => exact ⟨.stuck msg, fuel, hr⟩

/-- The outcome of a run is a well-defined denotation of
`(design, stimulus, σ)`: exactly one `SvOut` observes. -/
theorem Obs.existsUnique (d : Design) (σ : ScheduleOracle) (stim : List SvState) :
    ∃ o, Obs d σ stim o ∧ ∀ o', Obs d σ stim o' → o' = o := by
  obtain ⟨o, ho⟩ := Obs.total d σ stim
  exact ⟨o, ho, fun o' ho' => Obs.det ho' ho⟩

/-! ## `sv_simp` — one stack frame of symbolic execution

Shared per-design proof kit (used by every `Examples/<design>/proof.lean`
and `ToggleExample.lean`). Mirror of the Python lane's `py_simp` freeze
discipline: simp with every interpreter equation EXCEPT the recursion
points, which stay frozen so threshold/inversion lemmas can be applied to
them:

* `combSettle` — the comb-settle fixpoint loop (resolve with
  `combSettle_nil` on comb-free designs, or `combSettle_at_least`);
* `runFrom` — `run`'s stimulus recursion (resolve by induction over the
  stimulus, or `run_at_least`/`Runs.at_least`).

`Design.combIndices`/`Design.edgeIndices` are also left out: for a concrete
design they are decided by a one-line `rfl` lemma (see
`swapNba_edgeIndices` in `Examples/swap_nba/proof.lean`), which keeps goals
free of `List.range`/`filter` noise. Pass design-specific facts
(`swapNba_p0`, …) as extras, exactly like passing the program literal to
`py_simp`. -/

open Lean Lean.Parser.Tactic in
/-- `sv_simp [extra, lemmas] (at h)?` — one stack frame's worth of symbolic
execution of the SV interpreter: simp with every interpreter equation except
the frozen recursion points `combSettle` and `runFrom` (see the section
comment above). Pass design-specific facts (`swapNba_p0`, program literals,
branch hypotheses) as extras. -/
macro (name := svSimpTactic) "sv_simp" "[" args:(simpStar <|> simpErase <|> simpLemma),*
    "]" loc:(location)? : tactic => do
  let extra : Syntax.TSepArray
      [`Lean.Parser.Tactic.simpStar, `Lean.Parser.Tactic.simpErase,
       `Lean.Parser.Tactic.simpLemma] "," := ⟨args.elemsAndSeps⟩
  `(tactic| set_option linter.unusedSimpArgs false in
      simp [execStmts, execStmt, evalExpr, evalExprs, evalUnaryOp, evalBinOp,
            readSignal, SvState.lookup, SvState.set, SvState.showSignal,
            runCombProcess, combPass, runEdgeProcess, edgePass, commitNba,
            applyInputs, initState, cycleStep, run, Process.isCombPhase,
            Process.isEdgePhase, Design.inputNames, Design.outputNames,
            and_assoc, $extra,*] $(loc)?)

@[inherit_doc svSimpTactic]
macro "sv_simp" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| sv_simp [] $(loc)?)

/-! ## Applied inputs (shared canonical-trace vocabulary) -/

/-- The value an input port holds after sub-step 1 of a cycle: the stimulus
entry's value if present, else the held previous value. Canonical traces are
written in terms of `appIn`, so they are exact for *every* stimulus (partial
entries included). -/
def appIn (inputs : SvState) (name : String) (old : LVec) : LVec :=
  (SvState.lookup inputs name).getD old

/-! ## M0 theorem 1: `run` is a function of `(design, σ, fuel, stimulus)`

Stated to pin it, per the contract ("should be `rfl`-adjacent"). The
substantive determinism facts are `run_det`/`Runs.functional` above
(cross-fuel at fixed σ) and the per-design `swap_nba_det`/`counter_det`
(cross-schedule, `Examples/<design>/proof.lean`). -/

theorem run_deterministic (d : Design) (σ : ScheduleOracle) (fuel : Nat)
    (stim : List SvState) : run d σ fuel stim = run d σ fuel stim := rfl

end LeanModels.Sv
