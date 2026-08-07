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

H1-proper: the dict tier allocates (`Obj.dict`), mutates, and reads these
for real; module init (G1) seeds `initWorld`'s heap and globals.
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
invalidation counter. Lists (H2) need no version: list iteration is an
index cursor against the LIVE object (CPython `listiterator`), so there is
no invalidation to count. -/
inductive Obj where
  | dict (entries : Array (RVal × RVal)) (shapeVersion : Nat)
  | list (xs : Array RVal)
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

/-- The mutable world of one public call: heap + module globals + the
program's output. -/
structure World where
  heap : Heap
  globals : REnv
  /-- Accumulated stdout, as DATA (Thomas-directed addition, 2026-08-06,
  for the `leanpy` script runner): chunks in emission order, appended at
  the tail. `print` becomes a tier builtin appending here when module
  execution lands; nothing writes it yet (`print` arrives with `leanpy`
  module execution). Exit status and `argv` are
  RUNNER-boundary concerns (the exit code is the module run's outcome;
  `argv` arrives as a marshalled global), NOT world fields —
  docs/memory-model.md §effects. -/
  stdout : List String := []
deriving Repr, Inhabited, BEq

/-- One frame's full interpreter state: the shared world + this frame's
locals. Statement execution transforms a `FrameState`; a nested call
passes only the `world` through (`callIn`). -/
structure FrameState where
  world : World
  locals : REnv
deriving Repr, Inhabited, BEq

/-! ### Heap access (bounds-checked — docs/memory-model.md §heap WF)

Every semantic dereference goes through these: never `getD`, never an
`Inhabited` fallback. A `none` here is an interpreter invariant violation
(unreachable from well-formed worlds) and every caller reports it loudly. -/

/-- Bounds-checked heap read. Full name only (`Heap` is an abbrev, so dot
notation resolves into the `Array` namespace — same caveat as `Env.lookup`). -/
def Heap.get? (h : Heap) (a : Addr) : Option Obj :=
  if hlt : a < h.size then some (h[a]'hlt) else Option.none

/-- Bounds-checked heap write (same address, new object; size preserved). -/
def Heap.update (h : Heap) (a : Addr) (o : Obj) : Option Heap :=
  if hlt : a < h.size then some (h.set a o hlt) else Option.none

/-- Allocation: append; the fresh address is the old size. -/
def Heap.alloc (h : Heap) (o : Obj) : Heap × Addr :=
  (h.push o, h.size)

/-! ### Heap well-formedness (docs/memory-model.md §heap WF)

`RVal.WF h v`: every address in `v` is live in `h`. `Obj.WF`/`Heap.WF`
close the loop through stored objects. Preservation lemmas live with the
operations that need them (allocation/update below; the interpreter-wide
preservation statement is the dict tier's regression case 18). -/

mutual
  /-- Every `.ref` inside the value points below `h.size`. -/
  def RVal.WF (h : Heap) : RVal → Prop
    | .none | .bool _ | .int _ | .str _ => True
    | .tuple xs => RVal.WFList h xs.toList
    | .listV xs => RVal.WFList h xs.toList
    | .ref a => a < h.size

  /-- Elementwise `RVal.WF`. -/
  def RVal.WFList (h : Heap) : List RVal → Prop
    | [] => True
    | v :: vs => RVal.WF h v ∧ RVal.WFList h vs
end

/-- Every key and value stored in the object is WF w.r.t. `h`. -/
def Obj.WF (h : Heap) : Obj → Prop
  | .dict es _ => RVal.WFList h (es.toList.map Prod.fst)
      ∧ RVal.WFList h (es.toList.map Prod.snd)
  | .list xs => RVal.WFList h xs.toList

/-- Every stored object is WF w.r.t. the heap itself. -/
def Heap.WF (h : Heap) : Prop :=
  ∀ a (hlt : a < h.size), Obj.WF h (h[a]'hlt)

/-- The empty heap is WF (no addresses exist). -/
theorem Heap.WF.empty : Heap.WF #[] := fun a hlt => by simp at hlt

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

/-- Collapse the two-binder witness nest `bind_eq_ok` + `Run.ok.injEq`
leave behind: with ONE bound variable the core `exists_eq_left'` family
collapses `∃ a, A = a ∧ p a`, but the paired shape's leading `S = s`
conjunct blocks it under the inner binder — this is its two-variable
twin. -/
@[simp] theorem exists2_eq_left {σ' α' : Type} {P : σ' → α' → Prop}
    {S : σ'} {A : α'} :
    (∃ s a, (S = s ∧ A = a) ∧ P s a) ↔ P S A := by
  constructor
  · rintro ⟨s, a, ⟨rfl, rfl⟩, h⟩; exact h
  · intro h; exact ⟨S, A, ⟨rfl, rfl⟩, h⟩

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

/-! `Run.toPublic` lives after the freeze (below); forward declaration
order: the wrapper's erasure step needs `RVal.freeze`. -/

end LeanModels.Python

namespace LeanModels.Python

/-! ## Boundary marshalling (docs/memory-model.md v2, call layering)

`Val` has no dict form, so thawing stays structural (the doc's
"fresh per occurrence" clause becomes operative when a MARSHALLABLE
mutable container exists — H2 lists), and freezing refuses refs loudly:
a dict anywhere in a result is outside the public boundary until `Val`
gains a dict observation form (docs/memory-model.md §call layering). -/

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
  /-- Thaw a frozen boundary value into the runtime (structural: `Val`
  carries no mutable containers yet; H2's list snapshots materialize
  freshly on the heap per occurrence). -/
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
  /-- Deep-freeze a runtime value into the boundary snapshot. Refs are
  loudly unsupported — a dict anywhere in a result cannot cross the
  boundary until `Val` has a dict observation form; the structural walk
  reaches every ref (tuples/lists included), so the refusal is exact.
  Active-path cycle detection arrives WITH that observation form
  (docs/memory-model.md v2 §call layering) — today every cycle sits
  behind a ref and is already refused. -/
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

/-! ### The thaw/freeze roundtrip

On ref-free values (the only ones that cross the boundary) thaw and
freeze are mutually inverse. These two lemma families are what let the
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

/-- Thaw a public argument vector — the wrapper's marshalling step.
List-structural on purpose (the kernel reduces it): `Array.map` is a
`USize` loop the kernel cannot reduce, and `py_check`'s closing step is
kernel `rfl` on a whole `callFunction` run. -/
def RVal.thawArgs (args : Array Val) : Array RVal :=
  (RVal.thawList args.toList).toArray

/-- The `Array.map` reading of `thawArgs` (NOT simp: `Array.map` is
defeq-opaque — a `USize` loop — so the proof layer keeps the reducible
`thawArgs`/`thawList` forms as canonical and converts explicitly when a
mathematical map view is wanted). -/
theorem RVal.thawArgs_eq_map (args : Array Val) :
    RVal.thawArgs args = args.map RVal.thaw := by
  apply Array.toList_inj.mp
  simp [RVal.thawArgs, RVal.thawList_eq_map]

/-- Thawing preserves the argument count (the arity guards' normal form). -/
@[simp] theorem RVal.thawArgs_size (args : Array Val) :
    (RVal.thawArgs args).size = args.size := by
  simp [RVal.thawArgs, RVal.thawList_eq_map]

/-! Constructor-application lemmas for `thaw` (global simp: residual goals
and symbolic runs keep boundary values in runtime normal form). -/

@[simp] theorem RVal.thaw_none : RVal.thaw .none = .none := rfl
@[simp] theorem RVal.thaw_bool (b : Bool) : RVal.thaw (.bool b) = .bool b := rfl
@[simp] theorem RVal.thaw_int (n : Int) : RVal.thaw (.int n) = .int n := rfl
@[simp] theorem RVal.thaw_str (s : String) : RVal.thaw (.str s) = .str s := rfl
@[simp] theorem RVal.thaw_list (xs : Array Val) :
    RVal.thaw (.list xs) = .listV ((xs.toList.map RVal.thaw).toArray) := by
  simp [RVal.thaw, RVal.thawList_eq_map]
@[simp] theorem RVal.thaw_tuple (xs : Array Val) :
    RVal.thaw (.tuple xs) = .tuple ((xs.toList.map RVal.thaw).toArray) := by
  simp [RVal.thaw, RVal.thawList_eq_map]

/-- `freeze (thaw v) = ok v` in iff-form: freezing decides `.ok v` exactly
on the thaw of `v` (both directions of the roundtrip in one simp-friendly
statement). -/
theorem RVal.freeze_eq_ok_iff {rv : RVal} {v : Val} :
    RVal.freeze rv = .ok v ↔ rv = RVal.thaw v :=
  ⟨RVal.eq_thaw_of_freeze rv, fun h => h ▸ RVal.freeze_thaw v⟩

/-! ## H2: the heap-aware boundary (lists on the heap)

At H2 `Val.list` marshals to a HEAP OBJECT (`Obj.list`): thawing a
boundary argument allocates — every mutable-container occurrence in the
marshalled tree is freshly materialized, so distinct occurrences are
distinct objects (docs/memory-model.md §call layering) — and a returned
list freezes to a `Val.list` SNAPSHOT (the observation deliberately
forgets identity). The pure `RVal.thaw`/`RVal.freeze` pair above remains
the PROOF-LAYER VOCABULARY for the list-free fragment (`Val.listFree`):
on it the heap-threading thaw allocates nothing and agrees with the pure
thaw (`thawH_of_listFree`), which is how every existing boundary lemma
keeps its statement. The freeze side mirrors the `heapEq` doctrine: the
public wrapper takes the PURE fast path on ref-free results, and only
ref-carrying results enter the FUELED `freezeH` (a frozen recursion
point — exhaustion is `.timeout`; cycle detection is by the active
recursion path, fuel-independent). -/

mutual
  /-- No `Val.list` anywhere inside the boundary value (tuples searched
  recursively). On this fragment thawing is pure — the bridge every
  pre-H2 boundary statement rides. Kernel-computable (list-structural). -/
  def Val.listFree : Val → Bool
    | .none | .bool _ | .int _ | .str _ => true
    | .list _ => false
    | .tuple xs => Val.listFreeList xs.toList

  /-- Elementwise `Val.listFree`. -/
  def Val.listFreeList : List Val → Bool
    | [] => true
    | v :: vs => Val.listFree v && Val.listFreeList vs
end

/-- Every argument is list-free (the arity-style guard of the pure-thaw
bridge at the argument vector). -/
def Val.listFreeArgs (args : Array Val) : Bool :=
  Val.listFreeList args.toList

mutual
  /-- Heap-threading thaw (H2): scalars pass through, tuples stay
  immediate (elements threaded), a `Val.list` ALLOCATES a fresh
  `Obj.list` — one fresh object per occurrence in the marshalled tree,
  inner lists allocated before their container (CPython builds bottom-up;
  identity-free observations cannot tell anyway). -/
  def RVal.thawH (h : Heap) : Val → Heap × RVal
    | .none => (h, .none)
    | .bool b => (h, .bool b)
    | .int n => (h, .int n)
    | .str s => (h, .str s)
    | .tuple xs =>
      match RVal.thawListH h xs.toList with
      | (h, vs) => (h, .tuple vs.toArray)
    | .list xs =>
      match RVal.thawListH h xs.toList with
      | (h, vs) => (h.push (.list vs.toArray), .ref h.size)

  /-- Elementwise `thawH`, threading the heap left to right. -/
  def RVal.thawListH (h : Heap) : List Val → Heap × List RVal
    | [] => (h, [])
    | v :: vs =>
      match RVal.thawH h v with
      | (h, rv) =>
        match RVal.thawListH h vs with
        | (h, rvs) => (h, rv :: rvs)
end

/-- Thaw a public argument vector, threading the heap (the H2 wrapper's
marshalling step; list-structural so the kernel reduces it). -/
def RVal.thawArgsH (h : Heap) (args : Array Val) : Heap × Array RVal :=
  match RVal.thawListH h args.toList with
  | (h, rvs) => (h, rvs.toArray)

mutual
  /-- On list-free values the heap-threading thaw allocates nothing and
  agrees with the pure thaw — the bridge that keeps every pre-H2 boundary
  statement (which speaks `RVal.thaw`) true of the H2 wrapper. -/
  theorem RVal.thawH_of_listFree : (v : Val) → Val.listFree v = true →
      ∀ h, RVal.thawH h v = (h, RVal.thaw v)
    | .none, _, h => rfl
    | .bool _, _, h => rfl
    | .int _, _, h => rfl
    | .str _, _, h => rfl
    | .tuple xs, hf, h => by
        simp only [RVal.thawH, RVal.thaw,
          RVal.thawListH_of_listFree xs.toList (by simpa [Val.listFree] using hf) h]
    | .list xs, hf, h => by
        simp [Val.listFree] at hf

  /-- Elementwise `thawH_of_listFree`. -/
  theorem RVal.thawListH_of_listFree : (l : List Val) → Val.listFreeList l = true →
      ∀ h, RVal.thawListH h l = (h, RVal.thawList l)
    | [], _, h => rfl
    | v :: vs, hf, h => by
        simp only [Val.listFreeList, Bool.and_eq_true] at hf
        simp only [RVal.thawListH, RVal.thawList,
          RVal.thawH_of_listFree v hf.1 h,
          RVal.thawListH_of_listFree vs hf.2 h]
end

/-- Argument-vector form of the pure-thaw bridge. -/
theorem RVal.thawArgsH_of_listFree {args : Array Val}
    (hf : Val.listFreeArgs args = true) (h : Heap) :
    RVal.thawArgsH h args = (h, RVal.thawArgs args) := by
  simp only [RVal.thawArgsH, RVal.thawArgs,
    RVal.thawListH_of_listFree args.toList hf h]

mutual
  /-- Deep-freeze over the heap (H2) — the FUELED boundary walk for
  ref-carrying results (the public wrapper's `refFree` fast path keeps it
  out of every list-free observation): a list object freezes to a
  `Val.list` snapshot of its (recursively frozen) elements; a dict stays
  loudly outside the boundary (no `Val` dict observation form); a
  repeated address on the ACTIVE RECURSION PATH is a cycle — loudly
  unsupported, decided by detection, never by exhaustion; a repeated
  address NOT on the path is sharing, legitimately duplicated in the
  snapshot. Fuel exhaustion is `.timeout` only (docs/memory-model.md
  §fuel vs frontier). -/
  def RVal.freezeH (h : Heap) (fuel : Nat) (path : List Addr) (v : RVal) : Res Val :=
      match fuel with
      | 0 => .timeout
      | fuel + 1 =>
        match v with
        | .none => .ok .none
        | .bool b => .ok (.bool b)
        | .int n => .ok (.int n)
        | .str s => .ok (.str s)
        | .listV xs => do
            let vs ← RVal.freezeListH h fuel path xs.toList
            return .list vs.toArray
        | .tuple xs => do
            let vs ← RVal.freezeListH h fuel path xs.toList
            return .tuple vs.toArray
        | .ref a =>
          if path.contains a then
            .unsupported "returning a CYCLIC heap object through the call boundary is outside the tier (no cyclic observation form in `Val`; docs/memory-model.md §call layering)"
          else
            match Heap.get? h a with
            | some (.list xs) => do
                let vs ← RVal.freezeListH h fuel (a :: path) xs.toList
                return .list vs.toArray
            | some (.dict _ _) =>
                .unsupported "returning a dict through the call boundary is outside the tier (no dict observation form in `Val`; docs/memory-model.md)"
            | Option.none => .unsupported
                "internal: dangling heap address (heap well-formedness violation — report this)"

  /-- Elementwise `freezeH`, first refusal wins. -/
  def RVal.freezeListH (h : Heap) (fuel : Nat) (path : List Addr)
      (l : List RVal) : Res (List Val) :=
      match fuel with
      | 0 => .timeout
      | fuel + 1 =>
        match l with
        | [] => .ok []
        | v :: vs => do
            let v' ← RVal.freezeH h fuel path v
            let vs' ← RVal.freezeListH h fuel path vs
            return v' :: vs'
end

/-- Erase the world from a public outcome: `.ok` deep-freezes the value,
`.exn` forgets its (retained, but boundary-invisible) state. A NAMED
projection rather than an inline match so that symbolic goals keep it as
an application — the `split`-based branch recipes must find a body's
surviving `ite`, not the wrapper (`py_prove`'s branch alternative). -/
def Run.toPublic : Run World RVal → Res Val
  | .ok _ v => v.freeze
  | .exn _ e => .exn e
  | .timeout => .timeout
  | .unsupported msg => .unsupported msg

@[simp] theorem Run.toPublic_ok {w : World} {v : RVal} :
    Run.toPublic (.ok w v) = v.freeze := rfl
@[simp] theorem Run.toPublic_exn {w : World} {e : PyErr} :
    Run.toPublic (.exn w e) = .exn e := rfl
@[simp] theorem Run.toPublic_timeout :
    Run.toPublic .timeout = .timeout := rfl
@[simp] theorem Run.toPublic_unsupported {msg : String} :
    Run.toPublic (.unsupported msg) = .unsupported msg := rfl

end LeanModels.Python
