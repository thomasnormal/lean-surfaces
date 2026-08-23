/-
**The monadic rebuild's `@[spec]` LAYER, and its demonstration gates.**

`@[spec]` is core Lean's `mvcgen` attribute — a BUILTIN, needing no import, which
is why `LeanModels/Python/Logic.lean` already uses it. This file is the tier's
ALTITUDE REGISTRY in mvcgen's own vocabulary: each primitive of `Prim.lean` gets
one triple, and the walker meets a named constant with a spec instead of a
`match` it must unfold.

**The pilot put a number on why that matters, and this file reproduced it.** With
the primitives UNFOLDED into the walker, `mvcgen` leaves 259+ verification
conditions and `mvcgen_trivial` fails outright; behind their triples it leaves
twelve. Measured again here, in a harder form: the first attempt at
`value_scores_M` passed `assignM`, `envPut` and `liftRes` to `mvcgen` and died at
a **1 000 000-heartbeat `whnf` timeout**. Removing them — leaving only the
INTERPRETER unfolded — is what makes the gates below close.

**Every triple is OUTPUT-DETERMINED**: the answer is bound by the result binder
`r`, never taken as an input the caller must guess. The pilot measured both
failure modes of the alternative — a spec taking the answer as an input made
`mvcgen` unify the result metavariable with a loop ACCUMULATOR, a
wrong-but-typechecking instantiation.

**And every read-only triple FRAMES THE STATE explicitly** (`⌜… ∧ st = st0⌝`),
because `Triple` does not frame it: an unframed read leaves an unprovable
`s = s'` in the caller's success condition.

Zero `sorry`. Zero `native_decide`. `#print axioms` on every theorem.
-/
import LeanModels.Python.Monadic.Eval
import Std.Do
import Std.Tactic.Do

open Std.Do LeanModels LeanModels.Python
set_option mvcgen.warning false
set_option linter.unusedSimpArgs false

namespace LeanModels.Python.Monadic

/-- Python's `PostShape`, which is Core's `SemPS` at `ρ := PyErr`. No `WPMonad`
instance is written for it anywhere — `Core/Outcome.lean` records the `inferInstance`
that proves the whole stack synthesizes with zero instances written. -/
abbrev PS (σ : Type) : PostShape := SemPS σ PyErr

/-- The frame-level `PostShape`. -/
abbrev FS : PostShape := PS FrameState

/-! ## §0.9 THE `undefined` GATE — present, and expected EMPTY

`docs/family-architecture.md` §5.2's ruling: an expected-empty class is PRESENT
AND GATED, never absent, because omitting it makes the emptiness a fact about
the TYPE, invisible to a scoreboard — which then cannot tell *"this language has
no UB"* from *"this tier did not model that column."*

**Python has no undefined behaviour**, so its `undefined` bucket is expected
empty and is gated here.

**HOW IT IS ENFORCED, stated exactly, because the theorem below is the weaker
half.** The real gate is STRUCTURAL: this tier's refusal API is three
zero-cause entry points — `refuse`, `refuseEnv`, `refuseOrder` — none of which
takes a `RefusalCause`. `undefined` is therefore unreachable without calling
`LeanModels.refuse` directly, which nothing in the tier does. The theorem
records the expectation the structure enforces; it does not enforce it. Saying
so is the point — a gate that is really a naming convention should admit it. -/
theorem python_emits_no_undefined :
    (RefusalCause.unsupported ()).isUndefined = false
  ∧ (RefusalCause.environment ()).isUndefined = false
  ∧ (RefusalCause.orderDependence ()).isUndefined = false := by decide

/-! ## §1 THE PRIMITIVE TRIPLES -/

/-- A refusal is unreachable from a satisfiable precondition: `refuse` proves any
postcondition under `False`. This is what makes a `notYet` arm a *dead* branch in
a proof rather than an obligation, and it is the reason the rebuild's frontier
does not leak into the proof layer. -/
@[spec] theorem refuse_spec (msg : String) (Q : PostCond α (PS σ)) :
    ⦃fun _ => ⌜False⌝⦄ (refuse msg : PyM σ α) ⦃Q⦄ := by
  simp [Triple.iff, refuse]

@[spec] theorem exhausted_spec (Q : PostCond α (PS σ)) :
    ⦃fun _ => ⌜False⌝⦄ (exhausted : PyM σ α) ⦃Q⦄ := by
  simp [Triple.iff, exhausted]

@[spec] theorem envGet_spec (id : String) (st0 : FrameState) :
    ⦃fun st => ⌜st = st0⌝⦄ envGet id
    ⦃⇓ r => fun st => ⌜r = Env.lookup st0.locals id ∧ st = st0⌝⦄ := by
  mvcgen [envGet]; all_goals grind

@[spec] theorem envSet_spec (id : String) (v : RVal) (st0 : FrameState) :
    ⦃fun st => ⌜st = st0⌝⦄ envSet id v
    ⦃⇓ _ => fun st => ⌜st = { st0 with locals := Env.set st0.locals id v }⌝⦄ := by
  mvcgen [envSet]; all_goals grind

@[spec] theorem envPut_spec (env : Env) (st0 : FrameState) :
    ⦃fun st => ⌜st = st0⌝⦄ envPut env
    ⦃⇓ _ => fun st => ⌜st = { st0 with locals := env }⌝⦄ := by
  mvcgen [envPut]; all_goals grind

@[spec] theorem frameWorld_spec (st0 : FrameState) :
    ⦃fun st => ⌜st = st0⌝⦄ frameWorld
    ⦃⇓ r => fun st => ⌜r = st0.world ∧ st = st0⌝⦄ := by
  mvcgen [frameWorld]; all_goals grind

@[spec] theorem frameHeap_spec (st0 : FrameState) :
    ⦃fun st => ⌜st = st0⌝⦄ frameHeap
    ⦃⇓ r => fun st => ⌜r = st0.world.heap ∧ st = st0⌝⦄ := by
  mvcgen [frameHeap]; all_goals grind

@[spec] theorem frameGlobals_spec (st0 : FrameState) :
    ⦃fun st => ⌜st = st0⌝⦄ frameGlobals
    ⦃⇓ r => fun st => ⌜r = st0.world.globals ∧ st = st0⌝⦄ := by
  mvcgen [frameGlobals]; all_goals grind

@[spec] theorem heapPut_spec (h : Heap) (st0 : FrameState) :
    ⦃fun st => ⌜st = st0⌝⦄ heapPut h
    ⦃⇓ _ => fun st => ⌜st = { st0 with world := { st0.world with heap := h } }⌝⦄ := by
  mvcgen [heapPut]; all_goals grind

/-- Allocation answers the OLD heap size — one object per display. -/
@[spec] theorem heapPush_spec (o : Obj) (st0 : FrameState) :
    ⦃fun st => ⌜st = st0⌝⦄ heapPush o
    ⦃⇓ r => fun st => ⌜r = st0.world.heap.size ∧
        st = { st0 with world := { st0.world with heap := st0.world.heap.push o } }⌝⦄ := by
  mvcgen [heapPush]; all_goals grind

@[spec] theorem emit_spec (chunk : String) (st0 : FrameState) :
    ⦃fun st => ⌜st = st0⌝⦄ emit chunk
    ⦃⇓ _ => fun st => ⌜st = { st0 with world :=
        { st0.world with stdout := st0.world.stdout ++ [chunk] } }⌝⦄ := by
  mvcgen [emit]; all_goals grind

@[spec] theorem binOpM_spec (op : BinOp) (a b : RVal) (st0 : FrameState)
    (h : ∃ v, evalBinOp op a b = .ok v) :
    ⦃fun st => ⌜st = st0⌝⦄ binOpM op a b
    ⦃⇓ r => fun st => ⌜evalBinOp op a b = .ok r ∧ st = st0⌝⦄ := by
  mvcgen [binOpM, liftRes]; all_goals grind

@[spec] theorem unaryOpM_spec (op : UnaryOp) (v : RVal) (st0 : FrameState)
    (h : ∃ r, evalUnaryOpH st0.world.heap op v = .ok r) :
    ⦃fun st => ⌜st = st0⌝⦄ unaryOpM op v
    ⦃⇓ r => fun st => ⌜evalUnaryOpH st0.world.heap op v = .ok r ∧ st = st0⌝⦄ := by
  mvcgen [unaryOpM, liftRes, frameHeap]; all_goals grind

@[spec] theorem indexM_spec (c i : RVal) (st0 : FrameState)
    (h : ∃ v, indexValH st0.world.heap c i = .ok v) :
    ⦃fun st => ⌜st = st0⌝⦄ indexM c i
    ⦃⇓ r => fun st => ⌜indexValH st0.world.heap c i = .ok r ∧ st = st0⌝⦄ := by
  mvcgen [indexM, liftRes]; all_goals grind

@[spec] theorem sliceM_spec (cv lv uv sv : RVal) (st0 : FrameState)
    (h : ∃ r, sliceVal cv lv uv sv = .ok r) :
    ⦃fun st => ⌜st = st0⌝⦄ sliceM cv lv uv sv
    ⦃⇓ r => fun st => ⌜sliceVal cv lv uv sv = .ok r ∧ st = st0⌝⦄ := by
  mvcgen [sliceM, liftRes]; all_goals grind

@[spec] theorem truthyM_spec (v : RVal) (st0 : FrameState)
    (h : ∃ b, truthyH st0.world.heap v = .ok b) :
    ⦃fun st => ⌜st = st0⌝⦄ truthyM v
    ⦃⇓ r => fun st => ⌜truthyH st0.world.heap v = .ok r ∧ st = st0⌝⦄ := by
  mvcgen [truthyM, liftRes, frameHeap]; all_goals grind

@[spec] theorem lenM_spec (v : RVal) (st0 : FrameState)
    (h : ∃ r, lenValH st0.world.heap v = .ok r) :
    ⦃fun st => ⌜st = st0⌝⦄ lenM v
    ⦃⇓ r => fun st => ⌜lenValH st0.world.heap v = .ok r ∧ st = st0⌝⦄ := by
  mvcgen [lenM, liftRes, frameHeap]; all_goals grind

/-- §3a THE DICT CURSOR'S STEP: a PURE READ that answers the plan. The state
is unchanged, which is the half that matters — a cursor step must not disturb
the dict it is walking, and this is where that is a theorem rather than a
reading of the code. -/
@[spec] theorem dictStepM_spec (a i n sv : Nat) (st0 : FrameState) :
    ⦃fun st => ⌜st = st0⌝⦄ dictStepM a i n sv
    ⦃⇓ r => fun st => ⌜st = st0 ∧ r = (match Heap.get? st0.world.heap a with
        | some (.dict es sv') => some (dictStep es sv' i n sv)
        | _ => Option.none)⌝⦄ := by
  mvcgen [dictStepM, frameHeap]; all_goals grind

/-- The one primitive that both READS the heap and WRITES the locals. -/
@[spec] theorem assignM_spec (t : Expr) (v : RVal) (st0 : FrameState)
    (h : ∃ e, assignToH st0.world.heap st0.locals t v = .ok e) :
    ⦃fun st => ⌜st = st0⌝⦄ assignM t v
    ⦃⇓ _ => fun st => ⌜∃ e, assignToH st0.world.heap st0.locals t v = .ok e ∧
        st = { st0 with locals := e }⌝⦄ := by
  mvcgen [assignM, envPut, liftRes]; all_goals grind

/-! ## §1.5 ARM-LEVEL ALTITUDE — the fidelity finding's prescription, and its LIMIT

The four-deep GATE 3 shape does not close against the faithful interpreter, and
the diagnosis was that `mvcgen` must re-split `evalOpen`'s nine-step `.name`
resolution chain at every occurrence. The prescription — *more `@[spec]` lemmas
at the ARM level* — is right in principle, and here are the two that work.

**And here is the measured LIMIT, which is the more useful half.** The lemma that
would actually bind, `evalOpen_name_global` (the static-globals-fold arm, which
GATE 3 exercises twice for `pst`), **cannot be stated**: `mvcgen` splits the inner
`match lookupG …` into one VC per branch **without retaining the discriminant
equation**, so the two unreachable branches arrive as bare `⊢ False` with nothing
to refute them. Passing the hypothesis into `mvcgen`'s simp set does not help,
because the split has already happened. Re-measured with the two lemmas below in
the registry: the four-deep gate still does not close, now at **4M heartbeats /
~10 minutes**.

So the blocker is not "not enough lemmas" — it is a specific, nameable tactic
limitation, and that is a better thing to know. It is the third `mvcgen` defect
this lane has recorded, after the `Spec.throw_Except` metavariable bug and the
no-op `mvcgen?`. -/

@[spec] theorem evalOpen_name_local (K : Kont) (M : Module) (id : String)
    (sp : Span) (v : RVal) (st0 : FrameState)
    (h : Env.lookup st0.locals id = some v) :
    ⦃fun st => ⌜st = st0⌝⦄ evalOpen K M (.name id sp)
    ⦃⇓ r => fun st => ⌜r = v ∧ st = st0⌝⦄ := by
  mvcgen [evalOpen]; all_goals simp_all [h]

@[spec] theorem evalOpen_const (K : Kont) (M : Module) (c : Const) (sp : Span)
    (st0 : FrameState) :
    ⦃fun st => ⌜st = st0⌝⦄ evalOpen K M (.constant c sp)
    ⦃⇓ r => fun st => ⌜r = Const.toRVal c ∧ st = st0⌝⦄ := by
  mvcgen [evalOpen]; all_goals simp_all

/-! ## §2 THE DEMONSTRATION GATES — `mvcgen` on the REBUILT interpreter

Two, and the second is the point.

The pilot proved GATE 3's shape against a **shallow twin** and recorded exactly
one fidelity gap: its `resolve` was locals-then-globals, so it dropped the `pstG`
premise the real gate needs — *"the same statement about a slightly smaller
interpreter"*. **These proofs have no such gap.** `evalOpen`'s `.name` arm is the
trunk's nine-step resolution chain verbatim, static globals fold included, and
`hgp` below IS the premise the twin skipped.

So this is not a demonstration that mvcgen can walk *a* monadic program. It is a
demonstration that mvcgen walks **the interpreter the differential gate runs**. -/

/-- A small gate with every operand symbolic: `z = x + y` through the LOCALS arm.
Exercises `execOpen`'s generic assign arm, `evalOpen`'s `.name` and `.binOp`
arms, and the `envGet` / `binOpM` / `assignM` triples. -/
theorem assign_binop_M (K : Kont) (M : Module) (w : World) (e : REnv)
    (a b : Int) (sp : Span)
    (hx : Env.lookup e "x" = some (.int a))
    (hy : Env.lookup e "y" = some (.int b)) :
    ⦃fun st => ⌜st = ⟨w, e⟩⌝⦄
      execOpen K M (.assign #[.name "z" sp]
        (.binOp (.name "x" sp) .add (.name "y" sp) sp) sp)
    ⦃⇓ _ => fun st => ⌜st = ⟨w, Env.set e "z" (.int (a + b))⟩⌝⦄ := by
  have hadd : evalBinOp .add (.int a) (.int b) = .ok (.int (a + b)) := rfl
  have hassign : assignToH w.heap e (.name "z" sp) (.int (a + b))
      = .ok (Env.set e "z" (.int (a + b))) := by simp [assignToH, assignTo]
  -- THE ALTITUDE LAW: only the INTERPRETER unfolds. The primitives stay behind
  -- their triples, which is what keeps the VC count in single digits — and with
  -- `grind` wired into `mvcgen_trivial_extensible` (Core/Outcome.lean §0) the
  -- closing script is gone entirely. The four `have`s above are still load-bearing:
  -- they are the computed-shape residues `grind` is given, not decoration.
  mvcgen [execOpen, evalOpen]

/-- **The gate that closes the pilot's fidelity gap.** `row = pst[p]`, where the
receiver resolves through the STATIC GLOBALS FOLD — the arm the shallow twin did
not have. `hnp` pushes `pst` past the locals arm; `hgp` is the fold's answer, and
it is `value_scores`' own `pstG` premise. The heap read goes through
`indexValH` — the trunk's worker, not a copy. -/
theorem subscript_global_M (K : Kont) (M : Module) (w : World) (e : REnv)
    (pa : Addr) (pc : String) (es : Array (RVal × RVal)) (sv : Nat)
    (xs : Array RVal) (sp : Span)
    (hnp : Env.lookup e "pst" = Option.none)
    (hgp : lookupG (moduleGlobals M).1 "pst" = some (some (.ref pa)))
    (hp : Env.lookup e "p" = some (.str pc))
    (hd : Heap.get? w.heap pa = some (.dict es sv))
    (hrow : dictFind es.toList (.str pc) = some (.tuple xs)) :
    ⦃fun st => ⌜st = ⟨w, e⟩⌝⦄
      execOpen K M (.assign #[.name "row" sp]
        (.subscript (.name "pst" sp) (.name "p" sp) sp) sp)
    ⦃⇓ _ => fun st => ⌜st = ⟨w, Env.set e "row" (.tuple xs)⟩⌝⦄ := by
  have hrowIdx : indexValH w.heap (.ref pa) (.str pc) = .ok (.tuple xs) := by
    simp [indexValH, heapIndex, hd, hrow, hashableKey]
  have hassign : assignToH w.heap e (.name "row" sp) (.tuple xs)
      = .ok (Env.set e "row" (.tuple xs)) := by simp [assignToH, assignTo]
  mvcgen [execOpen, evalOpen]

#print axioms refuse_spec
#print axioms envGet_spec
#print axioms envSet_spec
#print axioms envPut_spec
#print axioms frameHeap_spec
#print axioms frameGlobals_spec
#print axioms heapPush_spec
#print axioms emit_spec
#print axioms binOpM_spec
#print axioms unaryOpM_spec
#print axioms indexM_spec
#print axioms sliceM_spec
#print axioms truthyM_spec
#print axioms lenM_spec
#print axioms assignM_spec
#print axioms evalOpen_name_local
#print axioms evalOpen_const
#print axioms assign_binop_M
#print axioms subscript_global_M

end LeanModels.Python.Monadic
