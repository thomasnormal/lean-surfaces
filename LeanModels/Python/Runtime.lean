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

end Run

/-! ## Boundary marshalling (docs/memory-model.md v2, call layering)

Stage H1-1: `Val` has no dict form and nothing allocates, so thawing is
structural (no fresh materialization to do yet — the doc's
"fresh per occurrence" clause becomes operative when mutable containers
become heap-allocated: H1-proper for dicts arriving via globals, H2 for
lists), and freezing refuses refs loudly (none can exist). -/

/-- Thaw a frozen boundary value into the runtime (stage H1-1:
structural; allocating containers arrive with their tiers). -/
def RVal.thaw : Val → RVal
  | .none => .none
  | .bool b => .bool b
  | .int n => .int n
  | .str s => .str s
  | .list xs => .listV (xs.attach.map fun ⟨v, _⟩ => RVal.thaw v)
  | .tuple xs => .tuple (xs.attach.map fun ⟨v, _⟩ => RVal.thaw v)

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
      let vs ← xs.attach.toList.mapM fun ⟨v, _⟩ => RVal.freeze v
      return .list vs.toArray
  | .tuple xs => do
      let vs ← xs.attach.toList.mapM fun ⟨v, _⟩ => RVal.freeze v
      return .tuple vs.toArray
  | .ref _ =>
      .unsupported "returning a heap object through the call boundary is outside the tier (H1-proper freeze, docs/memory-model.md)"

end LeanModels.Python
