import LeanModels.Python.Ast

/-!
# The runtime core (docs/memory-model.md v2, normative)

The types the heap-threaded interpreter runs over, separated from the
frozen public boundary (`Val`, Ast.lean):

* `RVal` — runtime values: the `Val` scalars, tuples that MAY contain
  refs, transitional value-lists (`listV`, removed at H2), and `ref`
  (a heap address). Refs are untypeable in `Val`, so "addresses never
  escape the boundary" is a typing fact.
* `Obj`/`Heap` — identity-bearing objects; the address is the index.
* `World` (heap + globals) and `FrameState` (world + locals).
* `RFlow` — statement flow carrying runtime values.
* `Run σ α` — the interpreter outcome: state is RETAINED on `.ok` AND on
  `.exn` (mutations before a raise survive — observable once `try`
  lands, pinned by regression before that); `.timeout` is fuel
  exhaustion ONLY; `.unsupported` is the fuel-independent frontier.

Threading stage (H1-1): the types exist and the interpreter runs over
them, but NOTHING allocates yet — every reachable heap is `#[]`.
-/

namespace LeanModels.Python

/-- A heap address (the index into the heap array). -/
abbrev Addr := Nat

/-- Runtime values (docs/memory-model.md v2). -/
inductive RVal where
  | none
  | bool  (b : Bool)
  | int   (n : Int)
  | str   (s : String)
  /-- Tuples may contain refs: aliasing through a tuple is faithful. -/
  | tuple (xs : Array RVal)
  /-- TRANSITIONAL value-semantics lists (the current tier); they move to
  the heap (`Obj.list`) at H2 and this constructor is removed. -/
  | listV (xs : Array RVal)
  | ref   (a : Addr)
deriving Repr, Inhabited, BEq

/-- Heap objects — identity-bearing, mutated in place. `shapeVersion`
increments on key insertion/deletion (not value update): the live-iterator
invalidation counter. -/
inductive Obj where
  | dict (entries : Array (RVal × RVal)) (shapeVersion : Nat)
deriving Repr, Inhabited, BEq

/-- The heap: the address IS the index; allocation appends. -/
abbrev Heap := Array Obj

/-- Runtime environments (locals, and the globals slice of a `World`). -/
abbrev REnv := List (String × RVal)

/-- `Env` is the canonical environment name across the interpreter and the
proof layer; since the H1 core re-shape it IS the runtime environment
(envs describe locals and loop invariants only — the public boundary is
`CallsTo` over `Val`). -/
abbrev Env := REnv

/-- The mutable world of one public call: heap + module globals. -/
structure World where
  heap : Heap
  globals : REnv
deriving Repr, Inhabited, BEq

/-- One frame's full interpreter state: the shared world + this frame's
locals. Statement execution transforms a `FrameState`; a nested call
passes only the `world` through (`callIn`). -/
structure FrameState where
  world : World
  locals : REnv
deriving Repr, Inhabited, BEq

/-- Statement-level control flow over runtime values. -/
inductive RFlow where
  | next
  | ret (v : RVal)
  | brk
  | cont
deriving Repr, Inhabited, BEq

/-- Interpreter outcome (docs/memory-model.md v2): state is retained on
`.ok` and `.exn`; `.timeout` is fuel exhaustion only; `.unsupported` is
the loud, fuel-independent semantic frontier. -/
inductive Run (σ : Type) (α : Type) where
  | ok          (state : σ) (value : α)
  | exn         (state : σ) (error : PyErr)
  | timeout
  | unsupported (message : String)
deriving Repr, Inhabited, BEq

namespace Run

/-- Sequence two stateful steps: the continuation sees the new state and
the value; `.exn` PRESERVES its state and short-circuits; `.timeout` and
`.unsupported` short-circuit stateless. (Not a `Monad` instance: the
continuation is state-passing, `σ → α → Run σ β`.) -/
@[inline] def bind : Run σ α → (σ → α → Run σ β) → Run σ β
  | .ok s a, f => f s a
  | .exn s e, _ => .exn s e
  | .timeout, _ => .timeout
  | .unsupported msg, _ => .unsupported msg

@[inherit_doc bind]
scoped syntax:60 term:61 " ⤳ " term:60 : term
macro_rules | `($x ⤳ $f) => `(Run.bind $x $f)

/-- Lift a pure `Res` step (helpers: arithmetic, indexing, …) into a run
at the current state: errors carry the state, `unsupported` stays loud.
A helper `.timeout` cannot occur (helpers are fuel-free) but maps
faithfully anyway. -/
@[inline] def liftRes (s : σ) : Res α → Run σ α
  | .ok a => .ok s a
  | .exn e => .exn s e
  | .timeout => .timeout
  | .unsupported msg => .unsupported msg

/-- Run a `World`-typed step (a nested call, `callIn`) inside a frame: the
world is threaded, the frame's locals ride through unchanged — on `.ok`
AND on `.exn` (the caller's locals survive a callee raise; state retention
per docs/memory-model.md). -/
@[inline] def withLocals (locals : REnv) : Run World α → Run FrameState α
  | .ok w a => .ok ⟨w, locals⟩ a
  | .exn w e => .exn ⟨w, locals⟩ e
  | .timeout => .timeout
  | .unsupported msg => .unsupported msg

/-- Project a frame-typed run to its world (returning from a call: the
frame's locals die with the frame; the shared world survives — on `.ok`
AND on `.exn`). -/
@[inline] def toWorld : Run FrameState α → Run World α
  | .ok s a => .ok s.world a
  | .exn s e => .exn s.world e
  | .timeout => .timeout
  | .unsupported msg => .unsupported msg

/-- Inversion of a successful bind (the `Res.bind_eq_ok` analog): the
prefix decided with some intermediate state and value. -/
@[simp] theorem bind_eq_ok {x : Run σ α} {f : σ → α → Run σ β} {s : σ} {b : β} :
    x.bind f = .ok s b ↔ ∃ s' a, x = .ok s' a ∧ f s' a = .ok s b := by
  cases x <;> simp [bind] <;> grind

@[simp] theorem ok_bind {s : σ} {a : α} {f : σ → α → Run σ β} :
    (Run.ok s a).bind f = f s a := rfl
@[simp] theorem exn_bind {s : σ} {e : PyErr} {f : σ → α → Run σ β} :
    (Run.exn s e).bind f = .exn s e := rfl
@[simp] theorem timeout_bind {f : σ → α → Run σ β} :
    (Run.timeout : Run σ α).bind f = .timeout := rfl
@[simp] theorem unsupported_bind {msg : String} {f : σ → α → Run σ β} :
    (Run.unsupported msg : Run σ α).bind f = .unsupported msg := rfl

/-! Constructor-application lemmas for the state combinators (symbolic
execution steps through them), plus `.ok`-inversion for each. -/

@[simp] theorem liftRes_ok {s : σ} {a : α} :
    liftRes s (Res.ok a) = Run.ok s a := rfl
@[simp] theorem liftRes_exn {s : σ} {e : PyErr} :
    liftRes s (Res.exn e : Res α) = Run.exn s e := rfl
@[simp] theorem liftRes_timeout {s : σ} :
    liftRes s (Res.timeout : Res α) = (Run.timeout : Run σ α) := rfl
@[simp] theorem liftRes_unsupported {s : σ} {msg : String} :
    liftRes s (Res.unsupported msg : Res α) = (Run.unsupported msg : Run σ α) := rfl

@[simp] theorem liftRes_eq_ok {s s' : σ} {r : Res α} {a : α} :
    liftRes s r = .ok s' a ↔ s' = s ∧ r = .ok a := by
  cases r <;> simp [liftRes] <;> grind

@[simp] theorem withLocals_ok {l : REnv} {w : World} {a : α} :
    withLocals l (Run.ok w a) = Run.ok ⟨w, l⟩ a := rfl
@[simp] theorem withLocals_exn {l : REnv} {w : World} {e : PyErr} :
    withLocals l (Run.exn w e : Run World α) = Run.exn ⟨w, l⟩ e := rfl
@[simp] theorem withLocals_timeout {l : REnv} :
    withLocals l (Run.timeout : Run World α) = (Run.timeout : Run FrameState α) := rfl
@[simp] theorem withLocals_unsupported {l : REnv} {msg : String} :
    withLocals l (Run.unsupported msg : Run World α)
      = (Run.unsupported msg : Run FrameState α) := rfl

@[simp] theorem withLocals_eq_ok {l : REnv} {x : Run World α} {s : FrameState} {a : α} :
    withLocals l x = .ok s a ↔ ∃ w, x = .ok w a ∧ s = ⟨w, l⟩ := by
  cases x <;> simp [withLocals] <;> grind

@[simp] theorem toWorld_ok {s : FrameState} {a : α} :
    toWorld (Run.ok s a) = Run.ok s.world a := rfl
@[simp] theorem toWorld_exn {s : FrameState} {e : PyErr} :
    toWorld (Run.exn s e : Run FrameState α) = Run.exn s.world e := rfl
@[simp] theorem toWorld_timeout :
    toWorld (Run.timeout : Run FrameState α) = (Run.timeout : Run World α) := rfl
@[simp] theorem toWorld_unsupported {msg : String} :
    toWorld (Run.unsupported msg : Run FrameState α)
      = (Run.unsupported msg : Run World α) := rfl

@[simp] theorem toWorld_eq_ok {x : Run FrameState α} {w : World} {a : α} :
    toWorld x = .ok w a ↔ ∃ s, x = .ok s a ∧ s.world = w := by
  cases x <;> simp [toWorld] <;> grind

end Run

/-! ## Boundary marshalling (docs/memory-model.md v2, call layering)

Stage H1-1: `Val` has no dict form and nothing allocates, so thawing is
structural (no fresh materialization to do yet — the doc's
"fresh per occurrence" clause becomes operative when mutable containers
become heap-allocated: H1-proper for dicts arriving via globals, H2 for
lists), and freezing refuses refs loudly (none can exist). -/

/-! ### `Res` bind normalization (global simp; the do-notation of the
fuel-free helpers and the freeze below reduce through these) -/

/-- `pure` on `Res` is `Res.ok` (do-notation normalization). -/
@[simp] theorem Res.pure_eq {α} (a : α) : (pure a : Res α) = .ok a := rfl

/-- Bind on an `ok` result steps into the continuation (do-notation
normalization; this is what advances symbolic execution). -/
@[simp] theorem Res.ok_bind {α β} (a : α) (f : α → Res β) :
    (Res.ok a >>= f) = f a := rfl

/-- Exceptions short-circuit bind. -/
@[simp] theorem Res.exn_bind {α β} (e : PyErr) (f : α → Res β) :
    ((Res.exn e : Res α) >>= f) = .exn e := rfl

/-- Timeouts short-circuit bind (this closes the small-fuel goals). -/
@[simp] theorem Res.timeout_bind {α β} (f : α → Res β) :
    ((Res.timeout : Res α) >>= f) = .timeout := rfl

/-- `unsupported` short-circuits bind. -/
@[simp] theorem Res.unsupported_bind {α β} (msg : String) (f : α → Res β) :
    ((Res.unsupported msg : Res α) >>= f) = .unsupported msg := rfl

/-- Inversion of a successful bind: the intermediate result must itself be
`ok`. Under `simp` this turns a symbolically-executed hypothesis into a nest
of existentials whose atoms are the frozen recursive calls — `obtain` them
and feed each to the induction hypothesis. -/
@[simp] theorem Res.bind_eq_ok {α β} {x : Res α} {f : α → Res β} {b : β} :
    x >>= f = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp

mutual
  /-- Thaw a frozen boundary value into the runtime (stage H1-1:
  structural; allocating containers arrive with their tiers — H1-proper
  materializes every mutable-container occurrence freshly on the heap). -/
  def RVal.thaw : Val → RVal
    | .none => .none
    | .bool b => .bool b
    | .int n => .int n
    | .str s => .str s
    | .list xs => .listV (RVal.thawList xs.toList).toArray
    | .tuple xs => .tuple (RVal.thawList xs.toList).toArray

  /-- Elementwise `thaw` (structural twin, kernel-reducible). -/
  def RVal.thawList : List Val → List RVal
    | [] => []
    | v :: vs => RVal.thaw v :: RVal.thawList vs
end

mutual
  /-- Deep-freeze a runtime value into the boundary snapshot. Stage H1-1:
  refs are loudly unsupported (none can exist — nothing allocates); the
  H1-proper freeze walks the heap with active-path cycle detection
  (docs/memory-model.md v2 §call layering). -/
  def RVal.freeze : RVal → Res Val
    | .none => .ok .none
    | .bool b => .ok (.bool b)
    | .int n => .ok (.int n)
    | .str s => .ok (.str s)
    | .listV xs => do
        let vs ← RVal.freezeList xs.toList
        return .list vs.toArray
    | .tuple xs => do
        let vs ← RVal.freezeList xs.toList
        return .tuple vs.toArray
    | .ref _ =>
        .unsupported "returning a heap object through the call boundary is outside the tier (H1-proper freeze, docs/memory-model.md)"

  /-- Elementwise `freeze`, first refusal wins. -/
  def RVal.freezeList : List RVal → Res (List Val)
    | [] => .ok []
    | v :: vs => do
        let v' ← RVal.freeze v
        let vs' ← RVal.freezeList vs
        return v' :: vs'
end

/-! ### The stage-1 thaw/freeze roundtrip

On ref-free values (the only runtime values stage H1-1 can produce) thaw
and freeze are mutually inverse. These two lemma families are what let the
public wrapper's proofs move between the boundary `Val` and the runtime
`RVal` without ever inspecting the freeze computation. -/

mutual
  /-- `freeze ∘ thaw = ok` — thawing never manufactures a ref. -/
  theorem RVal.freeze_thaw : (v : Val) → RVal.freeze (RVal.thaw v) = .ok v
    | .none => rfl
    | .bool _ => rfl
    | .int _ => rfl
    | .str _ => rfl
    | .list xs => by
        simp [RVal.thaw, RVal.freeze, RVal.freezeList_thawList xs.toList]
    | .tuple xs => by
        simp [RVal.thaw, RVal.freeze, RVal.freezeList_thawList xs.toList]

  /-- Elementwise `freeze_thaw`. -/
  theorem RVal.freezeList_thawList :
      (l : List Val) → RVal.freezeList (RVal.thawList l) = .ok l
    | [] => rfl
    | v :: vs => by
        simp [RVal.thawList, RVal.freezeList, RVal.freeze_thaw v,
              RVal.freezeList_thawList vs]
end

mutual
  /-- Freeze inversion: a value that froze is exactly the thaw of its
  snapshot (freeze is injective on the ref-free fragment, with thaw as its
  section). -/
  theorem RVal.eq_thaw_of_freeze :
      (rv : RVal) → {v : Val} → RVal.freeze rv = .ok v → rv = RVal.thaw v
    | .none, v, h => by
        cases (Res.ok.inj h); rfl
    | .bool _, v, h => by
        cases (Res.ok.inj h); rfl
    | .int _, v, h => by
        cases (Res.ok.inj h); rfl
    | .str _, v, h => by
        cases (Res.ok.inj h); rfl
    | .listV xs, v, h => by
        simp only [RVal.freeze, Res.bind_eq_ok, Res.pure_eq] at h
        obtain ⟨vs, hl, hv⟩ := h
        cases (Res.ok.inj hv)
        have := RVal.eqList_thawList_of_freezeList xs.toList hl
        simp [RVal.thaw, ← this]
    | .tuple xs, v, h => by
        simp only [RVal.freeze, Res.bind_eq_ok, Res.pure_eq] at h
        obtain ⟨vs, hl, hv⟩ := h
        cases (Res.ok.inj hv)
        have := RVal.eqList_thawList_of_freezeList xs.toList hl
        simp [RVal.thaw, ← this]
    | .ref _, v, h => by
        cases h

  /-- Elementwise freeze inversion. -/
  theorem RVal.eqList_thawList_of_freezeList :
      (l : List RVal) → {vs : List Val} →
      RVal.freezeList l = .ok vs → l = RVal.thawList vs
    | [], vs, h => by
        cases (Res.ok.inj h); rfl
    | rv :: l, vs, h => by
        simp only [RVal.freezeList, Res.bind_eq_ok, Res.pure_eq] at h
        obtain ⟨v', hv, vs', hl, hcons⟩ := h
        cases (Res.ok.inj hcons)
        have h1 := RVal.eq_thaw_of_freeze rv hv
        have h2 := RVal.eqList_thawList_of_freezeList l hl
        simp [RVal.thawList, ← h1, ← h2]
end

mutual
  /-- Freezing never raises: its only refusal is the loud `unsupported`
  (a `.ref` in the result). What pins the public wrapper's `.exn` outcomes
  to the interpreter run, never to the freeze. -/
  theorem RVal.freeze_ne_exn : (rv : RVal) → ∀ e, RVal.freeze rv ≠ .exn e
    | .none, e => by simp [RVal.freeze]
    | .bool _, e => by simp [RVal.freeze]
    | .int _, e => by simp [RVal.freeze]
    | .str _, e => by simp [RVal.freeze]
    | .listV xs, e => by
        simp only [RVal.freeze]
        cases hl : RVal.freezeList xs.toList with
        | ok vs => simp
        | exn e' => exact absurd hl (RVal.freezeList_ne_exn xs.toList e')
        | timeout => simp
        | unsupported msg => simp
    | .tuple xs, e => by
        simp only [RVal.freeze]
        cases hl : RVal.freezeList xs.toList with
        | ok vs => simp
        | exn e' => exact absurd hl (RVal.freezeList_ne_exn xs.toList e')
        | timeout => simp
        | unsupported msg => simp
    | .ref _, e => by simp [RVal.freeze]

  /-- Elementwise `freeze_ne_exn`. -/
  theorem RVal.freezeList_ne_exn : (l : List RVal) → ∀ e, RVal.freezeList l ≠ .exn e
    | [], e => by simp [RVal.freezeList]
    | rv :: l, e => by
        simp only [RVal.freezeList]
        cases hv : RVal.freeze rv with
        | ok v' =>
          simp only [Res.ok_bind]
          cases hl : RVal.freezeList l with
          | ok vs => simp
          | exn e' => exact absurd hl (RVal.freezeList_ne_exn l e')
          | timeout => simp
          | unsupported msg => simp
        | exn e' => exact absurd hv (RVal.freeze_ne_exn rv e')
        | timeout => simp
        | unsupported msg => simp
end

/-- `thawList` is elementwise `thaw` (the `List.map` normal form symbolic
execution prefers). -/
theorem RVal.thawList_eq_map : (l : List Val) → RVal.thawList l = l.map RVal.thaw
  | [] => rfl
  | v :: vs => by simp [RVal.thawList, RVal.thawList_eq_map vs]

/-- `freeze (thaw v) = ok v` in iff-form: freezing decides `.ok v` exactly
on the thaw of `v` (both directions of the roundtrip in one simp-friendly
statement). -/
theorem RVal.freeze_eq_ok_iff {rv : RVal} {v : Val} :
    RVal.freeze rv = .ok v ↔ rv = RVal.thaw v :=
  ⟨RVal.eq_thaw_of_freeze rv, fun h => h ▸ RVal.freeze_thaw v⟩

end LeanModels.Python
