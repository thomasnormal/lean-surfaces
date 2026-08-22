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
  /-- A namedtuple instance (docs/memory-model.md §class semantics — the
  recorded VALUE-like decision): an IMMEDIATE value, never a heap object.
  It carries its own class name (`tname`, error messages) and field names
  (attribute reads desugar to indexing), so no module table is consulted
  at access time. Equality/hashing erase the class entirely — CPython
  namedtuples compare as plain tuples (`Move(1,2,'') == (1,2,'')`), which
  is exactly what keeps sunfish's `tp_score` keys in the pure `keyEq`
  tier. No `Val` observation form exists: the boundary freeze refuses
  namedtuple results LOUDLY (a `Val.tuple` snapshot would silently forget
  the class AND falsify freeze inversion — recorded decision). -/
  | ntuple (tname : String) (fields : Array String) (xs : Array RVal)
  /-- A `range(lo, hi, step)` object as an IMMEDIATE value (pass 3,
  docs/memory-model.md §module-init execution): a range is IMMUTABLE and
  re-iterable, so materialization-per-use is exact and the value form
  avoids heap identity and boundary churn entirely. Iteration and the
  draining consumers materialize FUEL-BOUNDED (`rangeVals`); `len` and
  truthiness are exact; `==`, dict-key/set-element (ranges ARE hashable
  in CPython — `keyRefusal`, never a fake unhashable `TypeError`), and
  the public boundary stay LOUD. `step ≠ 0` by construction (the builtin
  raises the faithful `ValueError` first). -/
  | rangeV (lo hi step : Int)
  | ref   (a : Addr)
deriving Repr, Inhabited, BEq

/-- Runtime environments (locals, and the globals slice of a `World`). -/
abbrev REnv := List (String × RVal)

/-- `Env` is the canonical environment name across the interpreter and the
proof layer; since the H1 core re-shape it IS the runtime environment
(envs describe locals and loop invariants only — the public boundary is
`CallsTo` over `Val`). -/
abbrev Env := REnv

/-- A class identity (docs/memory-model.md H3): the INDEX into
`Module.classes` — a unique id, never the class name (with duplicate
names the last definition wins consistently; see `ClassDefn`). -/
abbrev ClassId := Nat

/-- A generator's execution status (CPython's `gi_frame_state`).
`running` is what makes re-entering a generator that is currently
executing the faithful `ValueError` instead of a silent re-entry;
`closed` is exhaustion (every further `next` is `StopIteration`). -/
inductive GenStatus where
  | created | suspended | running | closed
deriving Repr, Inhabited, BEq, DecidableEq

/-- One frame of a generator's **defunctionalized continuation** (H4,
docs/memory-model.md §generator semantics — the recorded decision).

A suspended generator must remember "where in the body it is", and the
tier represents that as DATA rather than as a Lean closure: the
continuation is a STACK of frames, innermost first, each a first-order
representative of one pending control construct. `block rest` is "finish
these statements"; a loop frame is "re-enter this loop", carrying exactly
the residual state that CPython's frame carries (a value iterator's
remaining elements, a list iterator's cursor, a sub-generator's address,
a `while`'s test/body/orelse). The statements are structural SUFFIXES of
the function body, so a frame is a structural PATH into it — never an
arbitrary expression context, which is why `yield` is admitted in
statement position only.

Loop frames carry no "rest of the enclosing block": the frames BELOW
already are it. That single choice makes the three exits uniform —
normal exhaustion and `break` both POP the loop frame, `continue`
re-enters it (which advances the cursor), and `while`'s `orelse` is
simply pushed on normal exit and skipped on `break`. -/
inductive GenFrame where
  /-- Finish these statements, then continue with the frames below. -/
  | block (rest : List Stmt)
  /-- `for target in <value sequence>`: `remaining` are the elements not
  yet taken (a str/tuple/namedtuple/boundary-list snapshot — immutable,
  so a snapshot IS the live semantics). -/
  | forSeq (target : Expr) (remaining : List RVal) (body : List Stmt)
  /-- `for target in <heap list at `a`>` with the LIVE cursor `i` — the
  object is re-read every step, exactly as `execForList` does. -/
  | forList (target : Expr) (a : Addr) (i : Nat) (body : List Stmt)
  /-- `for target in <dict at `a`>` with the LIVE cursor `i`, carrying the
  size `n` and the `shapeVersion` `sv` the loop STARTED with. The object is
  re-read every step, exactly as `forList` does; the two extra fields are
  what let the cursor tell CPython's two mutation regimes apart — a SIZE
  change is the faithful `RuntimeError`, while a same-size key-set change is
  REFUSED, because CPython's answer there depends on its entries-array
  layout and its compaction schedule (docs/memory-model.md §dict iteration).

  Constructed only by `LeanModels/Python/Monadic/` — the trunk interpreter
  refuses it by the no-backwards-compat ruling (it never builds one). -/
  | forDict (target : Expr) (a : Addr) (i : Nat) (n : Nat) (sv : Nat)
      (body : List Stmt)
  /-- `for target in <generator at `a`>` — a generator consuming a
  generator; re-entering the frame steps the inner one. -/
  | forGen (target : Expr) (a : Addr) (body : List Stmt)
  /-- `while test: body else: orelse` — re-entering re-tests. -/
  | whileLoop (test : Expr) (body : List Stmt) (orelse : List Stmt)
  -- The BUILTIN iterators (H4). They are generator frames rather than a
  -- separate object kind, so `stepIter`/`for`/`next` consume them through
  -- exactly one mechanism — `enumerate(s)` is as lazy as a `def` with a
  -- `yield`, and `count` is genuinely infinite.
  /-- `enumerate(<value sequence>, start)` at index `i`: a str/tuple/
  namedtuple/boundary-list snapshot IS the live semantics (all immutable
  in tier), like `forSeq`. -/
  | enumSeq (i : Int) (remaining : List RVal)
  /-- `enumerate(<heap list>, start)` at index `i`, cursor `cur`: the
  object is re-read every step, like `forList`. -/
  | enumList (i : Int) (a : Addr) (cur : Nat)
  /-- `itertools.count(start, step)` — never exhausts. -/
  | countFrom (cur : Int) (step : Int)
deriving Repr, Inhabited, BEq

/-- A suspended generator's continuation: the frame stack, innermost
first. `[]` means the body has run off its end (exhaustion). -/
abbrev GenCont := List GenFrame

/-- Heap objects — identity-bearing, mutated in place. `shapeVersion`
increments on key insertion/deletion (not value update): the live-iterator
invalidation counter. Lists (H2) need no version: list iteration is an
index cursor against the LIVE object (CPython `listiterator`), so there is
no invalidation to count. Instances (H3) carry their `ClassId` and their
attribute table (`__dict__` insertion order preserved, like dict entries);
mutable self IS this object — `self.x = v` updates `attrs` in place.
Instances exist only for DEFAULT-PROTOCOL classes (no bases, no dunder
methods beyond `__init__` — instantiation guards this loudly), so default
object semantics (identity `==`, truthy, unhashability-free attr access)
are faithful wherever an instance can appear. -/
inductive Obj where
  | dict (entries : Array (RVal × RVal)) (shapeVersion : Nat)
  | list (xs : Array RVal)
  | instance (cls : ClassId) (attrs : Array (String × RVal))
  /-- A GENERATOR object (H4): the suspended frame AS DATA — the
  generator function's (possibly qualified) name, its locals at the
  suspension point, the defunctionalized continuation, and the status.
  It lives on the HEAP because a generator is IDENTITY, not a value:
  `h = g; next(g); next(h)` advances one shared frame (`gen_lab.aliased`
  pins it differentially), and a `for` loop that abandons a generator by
  `break` must leave the very object the next consumer resumes
  (`gen_lab.two_phase`) — an immediate value would silently restart. -/
  | generator (qname : String) (locals : REnv) (cont : GenCont)
      (status : GenStatus)
  /-- A CLOSURE object (H7, docs/memory-model.md §nested defs and
  closures): the nested function carried INLINE (params, own-scope
  censuses, generator flag, body) plus the SNAPSHOT of its captured
  names, taken when the `def` statement executed. On the HEAP because
  functions are identity in CPython (`==` between distinct closures is
  `False` however equal their parts); under the never-rebound admission
  the snapshot is observationally CPython's cell. Calling it builds the
  callee env as parameters-then-snapshot (parameters shadow); a
  generator closure allocates the H4 generator with the snapshot inside
  its stored locals, so resume-time capture reads ride the stepper
  unchanged. -/
  | closure (name : String) (params : Array Param) (argsOk localsOk : Bool)
      (hasGlobal : Bool) (isGenerator : Bool) (body : Array Stmt)
      (captured : REnv)
  /-- A SET object (H7+, the honest subset for `self.history`):
  construction from an iterable (deduplicated by value equality, first
  occurrence kept) and `in` MEMBERSHIP, `len`, truthiness — nothing
  else. Iteration, `add`/`remove`/`pop`, `==`, `sorted(set)` are all
  LOUD: a set's iteration order is hash-order in CPython and is never
  guessed. Membership and len are order-independent, which is exactly
  why they are the admitted surface. -/
  | pyset (xs : Array RVal)
  /-- A CLOSURE CELL (H7 cells, docs/memory-model.md §nested defs and
  closures): the shared mutable location CPython gives a local that a
  nested def captures and the enclosing frame REBINDS after the `def`.
  A cell is a heap slot the closure body reads THROUGH — the closure's
  captured env holds `("<cell>x", .ref a)` instead of a value, so a read
  of `x` in the nested body resolves at CALL time, not at def time.
  `none` is the UNBOUND cell (CPython's empty cell: reading it raises
  the free-variable `NameError`, which is exactly what the name arm
  answers). A cell is never a Python VALUE: every value-position
  consumer refuses it loudly rather than treating it as an object. -/
  | cell (value : Option RVal)
deriving Repr, Inhabited, BEq

/-- The heap: the address IS the index; allocation appends. -/
abbrev Heap := Array Obj

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
  /-- THE CLOCK TRACE (pass 6, docs/memory-model.md §the trace clock):
  time as an INPUT, not an effect. Opaque integer readings, consumed in
  order — evaluating exactly `time.time()` (unshadowed, benign-import
  census — `isClockCall`, Semantics.lean) pops the head; an empty trace
  is the LOUD underrun refusal, fuel-independent (a spec error in the
  run's input, never a silent 0). The default `[]` is the pinned file's
  regime: nothing is read until a boundary (`callFunctionClock`, a
  batch job's `"clock"`, a spec's `{ w with clock := … }`) seeds it.
  Readings are unit-agnostic ℤ; the record-replay harness convention is
  integer microseconds (`time.time_ns() // 1000` on the CPython side,
  which CONSUMES what it records — both sides see the same integers). -/
  clock : List Int := []
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
    | .none | .bool _ | .int _ | .str _ | .rangeV .. => True
    | .tuple xs => RVal.WFList h xs.toList
    | .listV xs => RVal.WFList h xs.toList
    | .ntuple _ _ xs => RVal.WFList h xs.toList
    | .ref a => a < h.size

  /-- Elementwise `RVal.WF`. -/
  def RVal.WFList (h : Heap) : List RVal → Prop
    | [] => True
    | v :: vs => RVal.WF h v ∧ RVal.WFList h vs
end

/-- Every value a suspended frame holds is WF (the pending elements of a
value-iterator frame; loop-frame addresses are checked at the read). -/
def GenFrame.WF (h : Heap) : GenFrame → Prop
  | .forSeq _ xs _ => RVal.WFList h xs
  | .forList _ a _ _ => a < h.size
  | .forDict _ a _ _ _ _ => a < h.size
  | .forGen _ a _ => a < h.size
  | .enumSeq _ xs => RVal.WFList h xs
  | .enumList _ a _ => a < h.size
  | .block _ => True
  | .whileLoop .. => True
  | .countFrom .. => True

/-- Elementwise `GenFrame.WF`. -/
def GenCont.WF (h : Heap) : GenCont → Prop
  | [] => True
  | f :: k => GenFrame.WF h f ∧ GenCont.WF h k

/-- Every key and value stored in the object is WF w.r.t. `h`. -/
def Obj.WF (h : Heap) : Obj → Prop
  | .dict es _ => RVal.WFList h (es.toList.map Prod.fst)
      ∧ RVal.WFList h (es.toList.map Prod.snd)
  | .list xs => RVal.WFList h xs.toList
  | .instance _ attrs => RVal.WFList h (attrs.toList.map Prod.snd)
  | .closure _ _ _ _ _ _ _ captured => RVal.WFList h (captured.map Prod.snd)
  | .pyset xs => RVal.WFList h xs.toList
  | .cell v => RVal.WFList h v.toList
  | .generator _ lo k _ =>
      RVal.WFList h (lo.map Prod.snd) ∧ GenCont.WF h k


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

/-- `bind` with an explicit EXN continuation (the exceptions tier,
docs/memory-model.md §exceptions as-built): `ok` and `exn` both carry
their state into their continuation; `timeout`/`unsupported` pass
through. The one consumer is `stepIter` — an exception propagating out
of a generator resume must CLOSE the object (CPython marks the frame
finished), and this combinator lets that heap update compose without
restructuring the stepper (`Run.le_bindE` is its `fuelMono` glue). -/
@[inline] def bindE : Run σ α → (σ → α → Run σ β) → (σ → PyErr → Run σ β) →
    Run σ β
  | .ok s a, f, _ => f s a
  | .exn s e, _, g => g s e
  | .timeout, _, _ => .timeout
  | .unsupported msg, _, _ => .unsupported msg

@[simp] theorem ok_bindE {s : σ} {a : α} {f : σ → α → Run σ β}
    {g : σ → PyErr → Run σ β} : (Run.ok s a).bindE f g = f s a := rfl
@[simp] theorem exn_bindE {s : σ} {e : PyErr} {f : σ → α → Run σ β}
    {g : σ → PyErr → Run σ β} : (Run.exn s e).bindE f g = g s e := rfl
@[simp] theorem timeout_bindE {f : σ → α → Run σ β}
    {g : σ → PyErr → Run σ β} :
    (Run.timeout : Run σ α).bindE f g = .timeout := rfl
@[simp] theorem unsupported_bindE {msg : String} {f : σ → α → Run σ β}
    {g : σ → PyErr → Run σ β} :
    (Run.unsupported msg : Run σ α).bindE f g = .unsupported msg := rfl

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
    | .ntuple _ _ _ =>
        .unsupported "returning a namedtuple through the call boundary is outside the tier (no namedtuple observation form in `Val`; a tuple snapshot would silently forget the class — docs/memory-model.md §class semantics)"
    | .rangeV .. =>
        .unsupported "returning a range through the call boundary is outside the tier (no range observation form in `Val`; docs/memory-model.md §module-init execution)"
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
    | .ntuple _ _ _, v, h => by
        cases h
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
    | .rangeV .., e => by simp [RVal.freeze]
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
    | .ntuple _ _ _, e => by simp [RVal.freeze]
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
  /-- No `.ref` anywhere inside the value. The `==` fast path (and, at H2,
  the public wrapper's FREEZE fast path): ref-free pairs decide by the
  PURE `valEq`/`RVal.freeze` (fuel-independent), so symbolic execution
  never opens the fueled `heapEq`/`freezeH` on ordinary values — both are
  frozen recursion points (their fueled unfolding on symbolic operands is
  unbounded, the `execWhile` situation exactly). -/
  def RVal.refFree : RVal → Bool
    | .none | .bool _ | .int _ | .str _ | .rangeV .. => true
    | .tuple xs => RVal.refFreeList xs.toList
    | .listV xs => RVal.refFreeList xs.toList
    | .ntuple _ _ xs => RVal.refFreeList xs.toList
    | .ref _ => false

  /-- Elementwise `RVal.refFree`. -/
  def RVal.refFreeList : List RVal → Bool
    | [] => true
    | v :: vs => RVal.refFree v && RVal.refFreeList vs
end

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
        | .ntuple _ _ _ =>
            .unsupported "returning a namedtuple through the call boundary is outside the tier (no namedtuple observation form in `Val`; a tuple snapshot would silently forget the class — docs/memory-model.md §class semantics)"
        | .rangeV .. =>
            .unsupported "returning a range through the call boundary is outside the tier (no range observation form in `Val`; docs/memory-model.md §module-init execution)"
        | .ref a =>
          if path.contains a then
            .unsupported "returning a CYCLIC heap object through the call boundary is outside the tier (no cyclic observation form in `Val`; docs/memory-model.md §call layering)"
          else
            match Heap.get? h a with
            | some (.cell _) =>
                .unsupported "internal: a closure CELL crossed the call boundary (unreachable — report this)"
            | some (.list xs) => do
                let vs ← RVal.freezeListH h fuel (a :: path) xs.toList
                return .list vs.toArray
            | some (.dict _ _) =>
                .unsupported "returning a dict through the call boundary is outside the tier (no dict observation form in `Val`; docs/memory-model.md)"
            | some (.closure ..) =>
                .unsupported "returning a closure through the call boundary is outside the tier (a snapshot would forget function identity; docs/memory-model.md §nested defs and closures)"
            | some (.pyset _) =>
                .unsupported "returning a set through the call boundary is outside the tier (no set observation form in `Val`; a list snapshot would invent an iteration order)"
            | some (.instance _ _) =>
                .unsupported "returning a class instance through the call boundary is outside the tier (no instance observation form in `Val`; docs/memory-model.md H3)"
            | some (.generator ..) =>
                .unsupported "returning a GENERATOR through the call boundary is outside the tier (no generator observation form in `Val`; a snapshot of its yields would run the body eagerly, which is exactly what laziness forbids — docs/memory-model.md §generator semantics)"
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

mutual
  /-- The BOUNDARY freeze (H2): structural on the value — scalars, tuples,
  and (transitional) value-lists reduce per constructor exactly like the
  pure `RVal.freeze`, consuming NO fuel, so every list-free observation and
  its proof machinery behaves as at H1 — and ONLY a `.ref` enters the
  fueled heap walk (`freezeH`: list snapshots, cycle refusal, dict
  refusal). The `heapEq` fast-path doctrine, realized structurally: no
  `refFree` test, no conditional lemmas — simp reduces the constructor
  arms and the heap argument is dropped on every ref-free path. -/
  def RVal.freezeB (h : Heap) (fuel : Nat) : RVal → Res Val
    | .none => .ok .none
    | .bool b => .ok (.bool b)
    | .int n => .ok (.int n)
    | .str s => .ok (.str s)
    | .listV xs => do
        let vs ← RVal.freezeListB h fuel xs.toList
        return .list vs.toArray
    | .tuple xs => do
        let vs ← RVal.freezeListB h fuel xs.toList
        return .tuple vs.toArray
    | .ntuple _ _ _ =>
        .unsupported "returning a namedtuple through the call boundary is outside the tier (no namedtuple observation form in `Val`; a tuple snapshot would silently forget the class — docs/memory-model.md §class semantics)"
    | .rangeV .. =>
        .unsupported "returning a range through the call boundary is outside the tier (no range observation form in `Val`; docs/memory-model.md §module-init execution)"
    | .ref a => RVal.freezeH h fuel [] (.ref a)

  /-- Elementwise `freezeB`, first refusal wins. -/
  def RVal.freezeListB (h : Heap) (fuel : Nat) : List RVal → Res (List Val)
    | [] => .ok []
    | v :: vs => do
        let v' ← RVal.freezeB h fuel v
        let vs' ← RVal.freezeListB h fuel vs
        return v' :: vs'
end

mutual
  /-- `freezeB ∘ thaw = ok`, fuel-free — the pure `freeze_thaw` roundtrip
  survives at the H2 boundary verbatim (thaw never manufactures a ref, so
  the fueled ref arm is never entered). Cited by name in the value-side
  bridges; NOT simp (the `thaw ?v` pattern is defeq-expensive against
  captured runtime values). -/
  theorem RVal.freezeB_thaw (h : Heap) (fuel : Nat) :
      (v : Val) → RVal.freezeB h fuel (RVal.thaw v) = .ok v
    | .none => rfl
    | .bool _ => rfl
    | .int _ => rfl
    | .str _ => rfl
    | .list xs => by
        simp only [RVal.thaw, RVal.freezeB,
          RVal.freezeListB_thawList h fuel xs.toList, Res.ok_bind, Res.pure_eq]
    | .tuple xs => by
        simp only [RVal.thaw, RVal.freezeB,
          RVal.freezeListB_thawList h fuel xs.toList, Res.ok_bind, Res.pure_eq]

  /-- Elementwise `freezeB_thaw`. -/
  theorem RVal.freezeListB_thawList (h : Heap) (fuel : Nat) :
      (l : List Val) → RVal.freezeListB h fuel (RVal.thawList l) = .ok l
    | [] => rfl
    | v :: vs => by
        simp only [RVal.thawList, RVal.freezeListB,
          RVal.freezeB_thaw h fuel v, RVal.freezeListB_thawList h fuel vs,
          Res.ok_bind, Res.pure_eq]
end

/-- Erase the world from a public outcome: `.ok` deep-freezes the value
through the boundary freeze (`freezeB` — structural; refs enter the
fueled heap walk), `.exn` forgets its (retained, but boundary-invisible)
state. A NAMED projection rather than an inline match so that symbolic
goals keep it as an application — the `split`-based branch recipes must
find a body's surviving `ite`, not the wrapper. -/
def Run.toPublic (fuel : Nat) : Run World RVal → Res Val
  | .ok w v => RVal.freezeB w.heap fuel v
  | .exn _ e => .exn e
  | .timeout => .timeout
  | .unsupported msg => .unsupported msg

@[simp] theorem Run.toPublic_ok {fuel : Nat} {w : World} {v : RVal} :
    Run.toPublic fuel (.ok w v) = RVal.freezeB w.heap fuel v := rfl
@[simp] theorem Run.toPublic_exn {fuel : Nat} {w : World} {e : PyErr} :
    Run.toPublic fuel (.exn w e) = .exn e := rfl
@[simp] theorem Run.toPublic_timeout {fuel : Nat} :
    Run.toPublic fuel .timeout = .timeout := rfl
@[simp] theorem Run.toPublic_unsupported {fuel : Nat} {msg : String} :
    Run.toPublic fuel (.unsupported msg) = .unsupported msg := rfl

/-- The wrapper's erasure on a THAWED value (`freezeB_thaw` at the
`toPublic` shape; cited by name — not simp, see `freezeB_thaw`). -/
theorem Run.toPublic_thaw {fuel : Nat} {w : World} {v : Val} :
    Run.toPublic fuel (.ok w (RVal.thaw v)) = .ok v := by
  rw [Run.toPublic_ok, RVal.freezeB_thaw]

mutual
  /-- The pure thaw never manufactures a ref — the fact that keeps thawed
  results on the fuel-free structural paths of `freezeB`. -/
  theorem RVal.refFree_thaw : (v : Val) → RVal.refFree (RVal.thaw v) = true
    | .none => rfl
    | .bool _ => rfl
    | .int _ => rfl
    | .str _ => rfl
    | .list xs => by
        simpa [RVal.thaw, RVal.refFree] using
          RVal.refFreeList_thawList xs.toList
    | .tuple xs => by
        simpa [RVal.thaw, RVal.refFree] using
          RVal.refFreeList_thawList xs.toList

  /-- Elementwise `refFree_thaw`. -/
  theorem RVal.refFreeList_thawList :
      (l : List Val) → RVal.refFreeList (RVal.thawList l) = true
    | [] => rfl
    | v :: vs => by
        simp [RVal.thawList, RVal.refFreeList, RVal.refFree_thaw v,
              RVal.refFreeList_thawList vs]
end

/-- `freezeH` never raises (its refusals are loud, its exhaustion is
`.timeout`) — paired with its elementwise form, by induction on fuel:
the raise-side twin of `RVal.freeze_ne_exn`, so a public `.exn` outcome
always names an interpreter raise, never the freeze. -/
theorem RVal.freezeH_ne_exn_pair (h : Heap) (fuel : Nat) :
    (∀ (path : List Addr) (v : RVal) (e : PyErr),
      RVal.freezeH h fuel path v ≠ .exn e) ∧
    (∀ (path : List Addr) (l : List RVal) (e : PyErr),
      RVal.freezeListH h fuel path l ≠ .exn e) := by
  induction fuel with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro path v e hc; simp [RVal.freezeH] at hc
    · intro path l e hc; simp [RVal.freezeListH] at hc
  | succ fuel ih =>
    obtain ⟨ihV, ihL⟩ := ih
    refine ⟨?_, ?_⟩
    · intro path v e hc
      cases v with
      | none => simp [RVal.freezeH] at hc
      | bool b => simp [RVal.freezeH] at hc
      | int n => simp [RVal.freezeH] at hc
      | str s => simp [RVal.freezeH] at hc
      | rangeV lo hi step => simp [RVal.freezeH] at hc
      | listV xs =>
        simp only [RVal.freezeH] at hc
        cases hl : RVal.freezeListH h fuel path xs.toList with
        | ok vs => rw [hl] at hc; simp at hc
        | exn e' => exact ihL path xs.toList e' hl
        | timeout => rw [hl] at hc; simp at hc
        | unsupported msg => rw [hl] at hc; simp at hc
      | tuple xs =>
        simp only [RVal.freezeH] at hc
        cases hl : RVal.freezeListH h fuel path xs.toList with
        | ok vs => rw [hl] at hc; simp at hc
        | exn e' => exact ihL path xs.toList e' hl
        | timeout => rw [hl] at hc; simp at hc
        | unsupported msg => rw [hl] at hc; simp at hc
      | ntuple tn fs xs => simp [RVal.freezeH] at hc
      | ref a =>
        simp only [RVal.freezeH] at hc
        by_cases hp : path.contains a = true
        · rw [if_pos hp] at hc; simp at hc
        · rw [if_neg hp] at hc
          cases hget : Heap.get? h a with
          | none => rw [hget] at hc; simp at hc
          | some o =>
            rw [hget] at hc
            cases o with
            | dict es ver => simp at hc
            | «instance» cls attrs => simp at hc
            | generator qn lo k st => simp at hc
            | closure nm ps ao lo' hg ig bd cap => simp at hc
            | cell v => simp at hc
            | pyset xs => simp at hc
            | list xs =>
              cases hl : RVal.freezeListH h fuel (a :: path) xs.toList with
              | ok vs => simp [hl] at hc
              | exn e' => exact ihL (a :: path) xs.toList e' hl
              | timeout => simp [hl] at hc
              | unsupported msg => simp [hl] at hc
    · intro path l e hc
      cases l with
      | nil => simp [RVal.freezeListH] at hc
      | cons v vs =>
        simp only [RVal.freezeListH] at hc
        cases hv : RVal.freezeH h fuel path v with
        | ok v' =>
          rw [hv] at hc
          simp only [Res.ok_bind] at hc
          cases hvs : RVal.freezeListH h fuel path vs with
          | ok vs' => rw [hvs] at hc; simp at hc
          | exn e' => exact ihL path vs e' hvs
          | timeout => rw [hvs] at hc; simp at hc
          | unsupported msg => rw [hvs] at hc; simp at hc
        | exn e' => exact ihV path v e' hv
        | timeout => rw [hv] at hc; simp at hc
        | unsupported msg => rw [hv] at hc; simp at hc

/-- Value-form corollary of `freezeH_ne_exn_pair`. -/
theorem RVal.freezeH_ne_exn {h : Heap} {fuel : Nat} {path : List Addr}
    {v : RVal} {e : PyErr} : RVal.freezeH h fuel path v ≠ .exn e :=
  (RVal.freezeH_ne_exn_pair h fuel).1 path v e

mutual
  /-- `freezeB` never raises (both legs are raise-free) — a public `.exn`
  outcome always names an interpreter raise, never the freeze. -/
  theorem RVal.freezeB_ne_exn (h : Heap) (fuel : Nat) :
      (v : RVal) → ∀ e, RVal.freezeB h fuel v ≠ .exn e
    | .rangeV .., e => by simp [RVal.freezeB]
    | .none, e => by simp [RVal.freezeB]
    | .bool b, e => by simp [RVal.freezeB]
    | .int n, e => by simp [RVal.freezeB]
    | .str s, e => by simp [RVal.freezeB]
    | .listV xs, e => by
        simp only [RVal.freezeB]
        cases hl : RVal.freezeListB h fuel xs.toList with
        | ok vs => simp [hl]
        | exn e' => exact absurd hl (RVal.freezeListB_ne_exn h fuel xs.toList e')
        | timeout => simp [hl]
        | unsupported msg => simp [hl]
    | .tuple xs, e => by
        simp only [RVal.freezeB]
        cases hl : RVal.freezeListB h fuel xs.toList with
        | ok vs => simp [hl]
        | exn e' => exact absurd hl (RVal.freezeListB_ne_exn h fuel xs.toList e')
        | timeout => simp [hl]
        | unsupported msg => simp [hl]
    | .ntuple _ _ _, e => by simp [RVal.freezeB]
    | .ref a, e => RVal.freezeH_ne_exn

  /-- Elementwise `freezeB_ne_exn`. -/
  theorem RVal.freezeListB_ne_exn (h : Heap) (fuel : Nat) :
      (l : List RVal) → ∀ e, RVal.freezeListB h fuel l ≠ .exn e
    | [], e => by simp [RVal.freezeListB]
    | v :: vs, e => by
        simp only [RVal.freezeListB]
        cases hv : RVal.freezeB h fuel v with
        | ok v' =>
          simp only [hv, Res.ok_bind]
          cases hl : RVal.freezeListB h fuel vs with
          | ok vs' => simp [hl]
          | exn e' => exact absurd hl (RVal.freezeListB_ne_exn h fuel vs e')
          | timeout => simp [hl]
          | unsupported msg => simp [hl]
        | exn e' => exact absurd hv (RVal.freezeB_ne_exn h fuel v e')
        | timeout => simp [hv]
        | unsupported msg => simp [hv]
end

/-- A decided `.ok` run never erases to `.exn` (`freezeB_ne_exn` at the
`toPublic` shape) — what pins public `.exn` outcomes to the interpreter
run, never to the freeze. -/
theorem Run.toPublic_ok_ne_exn {fuel : Nat} {w : World} {rv : RVal}
    {e : PyErr} : Run.toPublic fuel (.ok w rv) ≠ .exn e := by
  rw [Run.toPublic_ok]
  exact RVal.freezeB_ne_exn w.heap fuel rv e

/-- Freeze inversion THROUGH the heap, on list-free snapshots: if the
fueled freeze decided `.ok v` and `v` carries no list, then no ref was
ever frozen (a ref freezes to a `.list` somewhere or refuses), so the
runtime value is exactly the pure thaw of `v` — the H2 form of
`RVal.eq_thaw_of_freeze`, and what keeps the frame theorem's statement
at the pure-thaw vocabulary. Paired with its elementwise form, by
induction on fuel. -/
theorem RVal.eq_thaw_of_freezeH_pair (h : Heap) (fuel : Nat) :
    (∀ (path : List Addr) (rv : RVal) (v : Val),
      RVal.freezeH h fuel path rv = .ok v → Val.listFree v = true →
      rv = RVal.thaw v) ∧
    (∀ (path : List Addr) (l : List RVal) (vs : List Val),
      RVal.freezeListH h fuel path l = .ok vs → Val.listFreeList vs = true →
      l = RVal.thawList vs) := by
  induction fuel with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro path rv v hc _; simp [RVal.freezeH] at hc
    · intro path l vs hc _; simp [RVal.freezeListH] at hc
  | succ fuel ih =>
    obtain ⟨ihV, ihL⟩ := ih
    refine ⟨?_, ?_⟩
    · intro path rv v hc hlf
      cases rv with
      | none => simp only [RVal.freezeH] at hc; cases (Res.ok.inj hc); rfl
      | bool b => simp only [RVal.freezeH] at hc; cases (Res.ok.inj hc); rfl
      | int n => simp only [RVal.freezeH] at hc; cases (Res.ok.inj hc); rfl
      | str s => simp only [RVal.freezeH] at hc; cases (Res.ok.inj hc); rfl
      | rangeV lo hi step => simp [RVal.freezeH] at hc
      | listV xs =>
        -- the snapshot is a `.list` — excluded by `hlf`
        simp only [RVal.freezeH, Res.bind_eq_ok, Res.pure_eq] at hc
        obtain ⟨vs, _, hv⟩ := hc
        cases (Res.ok.inj hv)
        simp [Val.listFree] at hlf
      | tuple xs =>
        simp only [RVal.freezeH, Res.bind_eq_ok, Res.pure_eq] at hc
        obtain ⟨vs, hl, hv⟩ := hc
        cases (Res.ok.inj hv)
        have hlf' : Val.listFreeList vs = true := by
          simpa [Val.listFree] using hlf
        have := ihL path xs.toList vs hl hlf'
        simp [RVal.thaw, ← this]
      | ntuple tn fs xs => simp [RVal.freezeH] at hc
      | ref a =>
        simp only [RVal.freezeH] at hc
        by_cases hp : path.contains a = true
        · rw [if_pos hp] at hc; cases hc
        · rw [if_neg hp] at hc
          cases hget : Heap.get? h a with
          | none => rw [hget] at hc; cases hc
          | some o =>
            rw [hget] at hc
            cases o with
            | dict es ver => cases hc
            | «instance» cls attrs => cases hc
            | generator qn lo k st => cases hc
            | closure nm ps ao lo' hg ig bd cap => cases hc
            | cell v => cases hc
            | pyset xs => cases hc
            | list xs =>
              -- freezes to a `.list` snapshot — excluded by `hlf`
              simp only [Res.bind_eq_ok, Res.pure_eq] at hc
              obtain ⟨vs, _, hv⟩ := hc
              cases (Res.ok.inj hv)
              simp [Val.listFree] at hlf
    · intro path l vs hc hlf
      cases l with
      | nil =>
        simp only [RVal.freezeListH] at hc
        cases (Res.ok.inj hc); rfl
      | cons rv l' =>
        simp only [RVal.freezeListH, Res.bind_eq_ok, Res.pure_eq] at hc
        obtain ⟨v', hv, vs', hl, hcons⟩ := hc
        cases (Res.ok.inj hcons)
        simp only [Val.listFreeList, Bool.and_eq_true] at hlf
        have h1 := ihV path rv v' hv hlf.1
        have h2 := ihL path l' vs' hl hlf.2
        simp [RVal.thawList, ← h1, ← h2]

mutual
  /-- Freeze inversion at the BOUNDARY freeze, on list-free snapshots —
  the `freezeB` form of `eq_thaw_of_freeze` (the H2 frame theorem's
  engine): scalars invert directly, tuples elementwise, a `.listV`/`.ref`
  outcome is a `.list` snapshot somewhere in `v` and is excluded by
  `Val.listFree v`. -/
  theorem RVal.eq_thaw_of_freezeB (h : Heap) (fuel : Nat) :
      (rv : RVal) → {v : Val} → RVal.freezeB h fuel rv = .ok v →
      Val.listFree v = true → rv = RVal.thaw v
    | .none, v, hc, _ => by cases (Res.ok.inj hc); rfl
    | .bool _, v, hc, _ => by cases (Res.ok.inj hc); rfl
    | .int _, v, hc, _ => by cases (Res.ok.inj hc); rfl
    | .str _, v, hc, _ => by cases (Res.ok.inj hc); rfl
    | .listV xs, v, hc, hlf => by
        simp only [RVal.freezeB, Res.bind_eq_ok, Res.pure_eq] at hc
        obtain ⟨vs, _, hv⟩ := hc
        cases (Res.ok.inj hv)
        simp [Val.listFree] at hlf
    | .tuple xs, v, hc, hlf => by
        simp only [RVal.freezeB, Res.bind_eq_ok, Res.pure_eq] at hc
        obtain ⟨vs, hl, hv⟩ := hc
        cases (Res.ok.inj hv)
        have hlf' : Val.listFreeList vs = true := by
          simpa [Val.listFree] using hlf
        have := RVal.eqList_thawList_of_freezeListB h fuel xs.toList hl hlf'
        simp [RVal.thaw, ← this]
    | .ntuple _ _ _, v, hc, _ => by cases hc
    | .ref a, v, hc, hlf =>
        (RVal.eq_thaw_of_freezeH_pair h fuel).1 [] (.ref a) v hc hlf

  /-- Elementwise `eq_thaw_of_freezeB`. -/
  theorem RVal.eqList_thawList_of_freezeListB (h : Heap) (fuel : Nat) :
      (l : List RVal) → {vs : List Val} →
      RVal.freezeListB h fuel l = .ok vs → Val.listFreeList vs = true →
      l = RVal.thawList vs
    | [], vs, hc, _ => by cases (Res.ok.inj hc); rfl
    | rv :: l', vs, hc, hlf => by
        simp only [RVal.freezeListB, Res.bind_eq_ok, Res.pure_eq] at hc
        obtain ⟨v', hv, vs', hl, hcons⟩ := hc
        cases (Res.ok.inj hcons)
        simp only [Val.listFreeList, Bool.and_eq_true] at hlf
        have h1 := RVal.eq_thaw_of_freezeB h fuel rv hv hlf.1
        have h2 := RVal.eqList_thawList_of_freezeListB h fuel l' hl hlf.2
        simp [RVal.thawList, ← h1, ← h2]
end


end LeanModels.Python
