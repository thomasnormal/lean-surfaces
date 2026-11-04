/-
**The mvcgen pilot's experiment file** — docs/mvcgen-pilot.md is its report.

**OUT OF THE PINNED BUILD BY CONSTRUCTION.** `lakefile.toml`'s globs are the
`LeanModels` lib root and `Examples.+`; nothing under `docs/` is either, so
`lake build` never sees this file and eleven other lanes are unaffected by it.
Run it directly:

    lake env lean docs/mvcgen-pilot.lean

**THE IMPORT BOUNDARY.** `@[spec]` is a builtin attribute and needs no import
(which is why `LeanModels/Python/Logic.lean` can already use it). `Std.Do.Triple`
and the `mvcgen` tactic do: `import Std.Do` and `import Std.Tactic.Do`, both
CORE modules on the pinned toolchain — no package, no `lakefile.toml` edit, no
`lake-manifest.json` edit. Measured: `import LeanModels.Python.Semantics` alone
answers ``to use `mvcgen`, please include `import Std.Tactic.Do` ``.

Zero `sorry`. Zero `native_decide`. Every theorem here is checked by
`#print axioms` at the foot of its section.
-/
import LeanModels.Python.Semantics
import Std.Do
import Std.Tactic.Do

open Std.Do LeanModels LeanModels.Python
set_option mvcgen.warning false
set_option linter.unusedSimpArgs false

namespace MvcgenPilot

/-! # §1 THE LAYER ORDER IS FORCED, and it is measured

`Run σ α` retains its state on `.exn` (docs/memory-model.md v2) and discards it
on `.timeout`/`.unsupported`. Only ONE of the two candidate stacks can say that:
`ExceptConds` for a `.arg` layer ABOVE the `.except` layer forgets the state in
the failure barrel. So the substrate's monad is `ExceptT ρ (StateT W Halt)`,
not `StateT W (ExceptT ρ Halt)` — the two are not interchangeable, and the
wrong one cannot state `PyPost.err : PyErr → FrameState → Prop`. -/

section LayerOrder
variable (W ρ L : Type)

/-- `StateT W (ExceptT ρ (Except L))` — the state is GONE in the `ρ` barrel. -/
example : ExceptConds (.arg W (.except ρ (.except L .pure)))
    = ((ρ → ULift Prop) × (L → ULift Prop) × Unit) := rfl

/-- `ExceptT ρ (StateT W (Except L))` — the `ρ` barrel SEES the world. -/
example : ExceptConds (.except ρ (.arg W (.except L .pure)))
    = ((ρ → W → ULift Prop) × (L → ULift Prop) × Unit) := rfl

/-! Both stacks synthesize a `WPMonad` with ZERO instances written. -/
#synth WPMonad (StateT W (ExceptT ρ (Except L))) (.arg W (.except ρ (.except L .pure)))
#synth WPMonad (ExceptT ρ (StateT W (Except L))) (.except ρ (.arg W (.except L .pure)))

end LayerOrder

/-! # §2 `Run σ` IS THAT STACK — an isomorphism, not an analogy -/

/-- `Run`'s two state-DISCARDING arms: `.timeout` and `.unsupported msg`. -/
abbrev Loud := Unit ⊕ String

/-- The substrate monad, at any World type. -/
abbrev PM (σ : Type) := ExceptT PyErr (StateT σ (Except Loud))

/-- Its `PostShape`. No instance is written for it anywhere. -/
abbrev PS (σ : Type) : PostShape := .except PyErr (.arg σ (.except Loud .pure))

def ofRun (r : σ → Run σ α) : PM σ α := fun s =>
  match r s with
  | .ok s' a       => .ok (.ok a, s')
  | .exn s' e      => .ok (.error e, s')
  | .timeout       => .error (.inl ())
  | .unsupported m => .error (.inr m)

def toRun (x : PM σ α) : σ → Run σ α := fun s =>
  match x s with
  | .ok (.ok a, s')    => .ok s' a
  | .ok (.error e, s') => .exn s' e
  | .error (.inl ())   => .timeout
  | .error (.inr m)    => .unsupported m

theorem toRun_ofRun (r : σ → Run σ α) : toRun (ofRun r) = r := by
  funext s; simp only [toRun, ofRun]; cases r s <;> rfl

theorem ofRun_toRun (x : PM σ α) : ofRun (toRun x) = x := by
  funext s
  rcases h : x s with l | ⟨v, s'⟩
  · rcases l with ⟨⟩ | m <;> simp [toRun, ofRun, h]
  · rcases v with a | e <;> simp [toRun, ofRun, h]

#print axioms toRun_ofRun
#print axioms ofRun_toRun

/-! # §3 THE FUEL QUESTION — the one shape `mvcgen` walks natively

Fuel cannot be a monad LAYER: hidden in the state, it is not a recursion
argument, and the definition does not elaborate at all. The measured error is
quoted in docs/mvcgen-pilot.md §3; it is a definability failure, not a proof
failure, so the offending `def` cannot be landed here.

Fuel as an explicit ARGUMENT (today's shape) is definable, but at a SYMBOLIC
fuel `mvcgen` makes no progress — also quoted in the report.

The route `mvcgen` DOES walk is the fuel-free one: an unbounded `while` in
do-notation, made total by a MEASURE. `Spec.repeatM`'s `WhileVariant` /
`WhileInvariant` pair is one-to-one with `py_vcgen`'s `(dec := …)` /
`(inv := …)` clauses. Here it is, closed. -/

section FuelFree

structure TW where dummy : Unit := ()
deriving Inhabited

inductive TR where | oops
deriving Repr

abbrev TM := StateT TW (Except TR)

/-- The `tri` of `Examples/python/tri`, as a Lean monadic program. -/
def tri (n : Int) : TM Int := do
  let mut total : Int := 0
  let mut i : Int := 1
  while i ≤ n do
    total := total + i
    i := i + 1
  return total

theorem tri_spec (n : Int) (hn : 0 ≤ n) :
    ⦃fun _ => ⌜True⌝⦄ tri n ⦃⇓ r => fun _ => ⌜2 * r = n * (n + 1)⌝⦄ := by
  mvcgen [tri] invariants
    · fun b _ => ⟨(n + 1 - b.2).toNat⟩
    · ⇓ x => fun _ => match x with
        | .inl (total, i) => ⌜1 ≤ i ∧ i ≤ n + 1 ∧ 2 * total = i * (i - 1)⌝
        | .inr (total, _) => ⌜2 * total = n * (n + 1)⌝
  case vc2.step.isFalse =>
    rename_i b mb total i hcont s2 hinv
    obtain ⟨-, hi1, hi2, hi3⟩ := hinv
    have he : b.2 = n + 1 := by omega
    show 2 * b.1 = n * (n + 1)
    rw [hi3, he]; grind
  all_goals simp_all [WhileVariant.eval]
  all_goals grind

#print axioms tri_spec

end FuelFree

/-! # §4 THE WORKED COMPARISON — GATE 3 (`value_scores`) through `mvcgen`

`Examples/python/sunfish/value_bound.lean`'s `value_scores` proves
`score = pst[p][j] - pst[p][i]` of the SHIPPED sunfish's `Position.value`,
through the real fuel-indexed interpreter, at `F + 10`. Below is the SAME
fact proved of a monadic shallow twin. The premises are the gate's, verbatim,
MINUS `pstG` — see §5 and the report's fidelity note. -/

abbrev FM := PM FrameState
abbrev FS : PostShape := PS FrameState

def loud (m : String) : FM α := fun _ => .error (.inr m)

def liftRes : Res RVal → FM RVal
  | .ok v          => pure v
  | .exn e         => throw e
  | .timeout       => fun _ => .error (.inl ())
  | .unsupported m => loud m

/-! ## The twin's PRIMITIVES — one per interpreter step the gate exercises. -/

/-- Name resolution: locals first, then the world's globals. The real
interpreter's `.name` arm consults the STATIC fold before the live view; the
twin does not, which is the one premise it drops. -/
def resolve (st : FrameState) (id : String) : Option RVal :=
  match Env.lookup st.locals id with
  | some v      => some v
  | Option.none => Env.lookup st.world.globals id

def lookupName (id : String) : FM RVal := do
  let st ← get
  match resolve st id with
  | some v      => pure v
  | Option.none => throw (.nameError id)

def indexM (c k : RVal) : FM RVal := do
  let st ← get
  liftRes (indexValH st.world.heap c k)

def binOpM (op : BinOp) (a b : RVal) : FM RVal := liftRes (evalBinOp op a b)

def bindLocal (n : String) (v : RVal) : FM Unit :=
  modify fun st => { st with locals := Env.set st.locals n v }

/-! ## The SPEC LEMMAS — this is the ALTITUDE LAYER, and `@[spec]` is its registry.

Every one is OUTPUT-DETERMINED: the answer is bound by the result binder `r`,
never taken as an input the caller must guess. Measured, both directions:
with the answer as an INPUT parameter the same gate leaves 23 verification
conditions including dependent metavariables (`?vc16 s h : RVal`); with the
primitives UNFOLDED instead of specified it leaves 259+ and `mvcgen_trivial`
fails outright. In the form below it leaves 12, all pure. -/

@[spec] theorem lookupName_spec (id : String) (st0 : FrameState)
    (h : (resolve st0 id).isSome) :
    ⦃fun st => ⌜st = st0⌝⦄ lookupName id
    ⦃⇓ r => fun st => ⌜resolve st0 id = some r ∧ st = st0⌝⦄ := by
  mvcgen [lookupName]
  all_goals grind

@[spec] theorem indexM_spec (c k : RVal) (st0 : FrameState)
    (h : ∃ v, indexValH st0.world.heap c k = .ok v) :
    ⦃fun st => ⌜st = st0⌝⦄ indexM c k
    ⦃⇓ r => fun st => ⌜indexValH st0.world.heap c k = .ok r ∧ st = st0⌝⦄ := by
  mvcgen [indexM, liftRes]
  all_goals grind

@[spec] theorem binOpM_spec (op : BinOp) (a b : RVal) (st0 : FrameState)
    (h : ∃ v, evalBinOp op a b = .ok v) :
    ⦃fun st => ⌜st = st0⌝⦄ binOpM op a b
    ⦃⇓ r => fun st => ⌜evalBinOp op a b = .ok r ∧ st = st0⌝⦄ := by
  mvcgen [binOpM, liftRes]
  all_goals grind

@[spec] theorem bindLocal_spec (n : String) (v : RVal) (st0 : FrameState) :
    ⦃fun st => ⌜st = st0⌝⦄ bindLocal n v
    ⦃⇓ _ => fun st => ⌜st = { st0 with locals := Env.set st0.locals n v }⌝⦄ := by
  mvcgen [bindLocal]
  all_goals grind

/-! ## The twin interpreter — the evalExpr path `vlScore` exercises.

`evalM` is STRUCTURAL on `Expr`: the slice this gate needs carries no fuel at
all. Fuel is owed only at `callIn`/`execWhile`/`execFor`/`heapEq`/generators. -/

def evalM : Expr → FM RVal
  | .name id _       => lookupName id
  | .subscript r k _ => do let c ← evalM r; let x ← evalM k; indexM c x
  | .binOp l op r _  => do let a ← evalM l; let b ← evalM r; binOpM op a b
  | _                => loud "outside the twin's slice"

def execM : Stmt → FM Unit
  | .assign tgts rhs _ =>
      match tgts.toList with
      | [.name n _] => do let v ← evalM rhs; bindLocal n v
      | _           => loud "outside the twin's slice"
  | _ => loud "outside the twin's slice"

/-- Exactly `value_bound.lean`'s `vlScore_lit` right-hand side — the shape
`value_scores` proves about after its one `rw [hlit]`. -/
def vlScoreLit (a b c d e f g h i k l m n : Span) : Stmt :=
    .assign #[.name "score" a]
      (.binOp (.subscript (.subscript (.name "pst" b) (.name "p" c) d) (.name "j" e) f)
        .sub
        (.subscript (.subscript (.name "pst" g) (.name "p" h) i) (.name "i" k) l) m) n

/-- **GATE 3, through `mvcgen`.** The premises are `value_scores`' own. -/
theorem value_scores_M (w : World) (e : REnv) (pa : Addr) (pc : String)
    (es : Array (RVal × RVal)) (sv : Nat) (xs : Array RVal) (i j zi zj : Int)
    (sa sb sc sd se sf sg sh si sk sl sm sn : Span)
    (hnp : Env.lookup e "pst" = Option.none)
    (hp : Env.lookup e "p" = some (.str pc))
    (hei : Env.lookup e "i" = some (.int i))
    (hej : Env.lookup e "j" = some (.int j))
    (hg : Env.lookup w.globals "pst" = some (.ref pa))
    (hd : Heap.get? w.heap pa = some (.dict es sv))
    (hrow : dictFind es.toList (.str pc) = some (.tuple xs))
    (hsz : xs.size = 120)
    (hi : 0 ≤ i) (hi' : i < 120) (hj : 0 ≤ j) (hj' : j < 120)
    (hxi : xs[i.toNat]?.getD .none = .int zi)
    (hxj : xs[j.toNat]?.getD .none = .int zj) :
    ⦃fun st => ⌜st = ⟨w, e⟩⌝⦄
      execM (vlScoreLit sa sb sc sd se sf sg sh si sk sl sm sn)
    ⦃⇓ _ => fun st => ⌜st = ⟨w, Env.set e "score" (.int (zj - zi))⟩⌝⦄ := by
  have hpst : resolve ⟨w, e⟩ "pst" = some (.ref pa) := by simp [resolve, hnp, hg]
  have hpp  : resolve ⟨w, e⟩ "p" = some (.str pc) := by simp [resolve, hp]
  have hii  : resolve ⟨w, e⟩ "i" = some (.int i) := by simp [resolve, hei]
  have hjj  : resolve ⟨w, e⟩ "j" = some (.int j) := by simp [resolve, hej]
  have hrowIdx : indexValH w.heap (.ref pa) (.str pc) = .ok (.tuple xs) := by
    simp [indexValH, heapIndex, hd, hrow, hashableKey]
  have hjIdx : indexValH w.heap (.tuple xs) (.int j) = .ok (.int zj) := by
    simp [indexValH, indexVal, asInt, normIndex, hsz, hxj,
      if_neg (show ¬ j < 0 by omega), if_pos (show (0 ≤ j ∧ j < (120:Int)) from ⟨hj, hj'⟩)]
  have hiIdx : indexValH w.heap (.tuple xs) (.int i) = .ok (.int zi) := by
    simp [indexValH, indexVal, asInt, normIndex, hsz, hxi,
      if_neg (show ¬ i < 0 by omega), if_pos (show (0 ≤ i ∧ i < (120:Int)) from ⟨hi, hi'⟩)]
  have hsub : evalBinOp .sub (.int zj) (.int zi) = .ok (.int (zj - zi)) := rfl
  mvcgen [execM, evalM, vlScoreLit]
  all_goals intros
  all_goals subst_vars
  all_goals simp_all [hpst, hpp, hii, hjj, hrowIdx, hjIdx, hiIdx, hsub]

/-! ## Non-vacuity FIRST — the twin RUNS on a fixture, and the fixture answers. -/

private def fxHeap : Heap := #[.dict #[(.str "P", .tuple #[.int 10, .int 20, .int 30])] 1]
private def fxW : World := { heap := fxHeap, globals := [("pst", .ref 0)] }
private def fxE : REnv := [("p", .str "P"), ("i", .int 0), ("j", .int 2)]
private def sp0 : Span := ⟨0, 0, 0, 0⟩

/-! `score = pst["P"][2] - pst["P"][0] = 30 - 10 = 20`, computed through `toRun`. -/
#guard (match toRun (execM (vlScoreLit sp0 sp0 sp0 sp0 sp0 sp0 sp0 sp0 sp0 sp0 sp0 sp0 sp0))
          ⟨fxW, fxE⟩ with
        | .ok st _ => Env.lookup st.locals "score" == some (.int 20)
        | _ => false)

#print axioms value_scores_M
#print axioms lookupName_spec
#print axioms indexM_spec
#print axioms binOpM_spec
#print axioms bindLocal_spec

end MvcgenPilot
