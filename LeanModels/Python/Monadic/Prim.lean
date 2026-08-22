/-
**The monadic rebuild's PRIMITIVES** — the `@[spec]`-shaped operations.

Two kinds of thing live here and the split is the architecture:

* **PRIMITIVES** — small, named, output-determined monadic steps over the
  substrate (`envGet`, `envSet`, `heapPush`, `binOpM`, `indexM`, …). Each is a
  thin monadic wrapper over a PURE worker the trunk already owns; the wrapper
  exists so `mvcgen` meets a named constant with an `@[spec]` lemma instead of
  a `match` it must unfold. The pilot measured the price of forgetting this:
  primitives UNFOLDED leave **259+** verification conditions and
  `mvcgen_trivial` fails outright; the same goal behind four `@[spec]` triples
  leaves **12**, all pure, and closes.

* **`Kont`** — the DEFUNCTIONALIZED FUEL BOUNDARY. See `Eval.lean`'s header for
  the ruling; in short, the fuel-free half of the interpreter takes the fueled
  operations as a parameter, which is what makes it structural on the syntax and
  therefore both kernel-reducible and walkable by `mvcgen`.

Every primitive is a `def`, never an `abbrev` (the def-not-abbrev law): an
`abbrev` is reducible and would be unfolded by the very tactics the `@[spec]`
registry exists to keep out.
-/
import LeanModels.Python.Monadic.Substrate

open LeanModels LeanModels.Python

namespace LeanModels.Python.Monadic

/-! ## §1 STATE PRIMITIVES -/

/-- Read this frame's locals. -/
def envGet (id : String) : SemF (Option RVal) := do
  let st ← get; pure (Env.lookup st.locals id)

/-- Bind a name in this frame's locals. -/
def envSet (id : String) (v : RVal) : SemF Unit :=
  modify fun st => { st with locals := Env.set st.locals id v }

/-- Replace this frame's locals wholesale (the `assignToH` family answers a new
`Env`, not a delta). -/
def envPut (env : Env) : SemF Unit :=
  modify fun st => { st with locals := env }

/-- Read the world out of the frame. -/
def frameWorld : SemF World := do
  let st ← get; pure st.world

/-- Read the heap out of the frame. -/
def frameHeap : SemF Heap := do
  let st ← get; pure st.world.heap

/-- §3a THE DICT CURSOR'S STEP, as ONE action: read the referent, decide the
pure `dictStep` plan. `none` means the address does not hold a dict — an
invariant break the callers refuse loudly rather than guess through.

It exists as a primitive so the cursor has ONE `@[spec]` lemma
(`dictStepM_spec`) instead of a heap read and a decision that `mvcgen` must
re-split at both call sites — `execGen`'s and the script shell's. -/
def dictStepM (a i n sv : Nat) : SemF (Option DictStep) := do
  match Heap.get? (← frameHeap) a with
  | some (.dict es sv') => pure (some (dictStep es sv' i n sv))
  | _ => pure Option.none

/-- Read the live module globals out of the frame. -/
def frameGlobals : SemF REnv := do
  let st ← get; pure st.world.globals

/-- Install a new heap. -/
def heapPut (h : Heap) : SemF Unit :=
  modify fun st => { st with world := { st.world with heap := h } }

/-- Allocate: append the object, answer its address (the OLD heap size — a list
display and a dict display both allocate exactly one object, per display). -/
def heapPush (o : Obj) : SemF Addr := do
  let st ← get
  let a := st.world.heap.size
  set { st with world := { st.world with heap := st.world.heap.push o } }
  pure a

/-- Append one chunk to the program's output. -/
def emit (chunk : String) : SemF Unit :=
  modify fun st => { st with world := { st.world with stdout := st.world.stdout ++ [chunk] } }

/-! ## §2 PURE-WORKER PRIMITIVES — the maximal trunk, one door each

Every one of these is `liftRes` over a worker that already exists and is already
differentially validated. The rebuild owns the CONTROL; the trunk owns the
arithmetic. A second `evalBinOp` would be a second thing to keep true. -/

def binOpM (op : BinOp) (a b : RVal) : SemF RVal := liftRes (evalBinOp op a b)

def unaryOpM (op : UnaryOp) (v : RVal) : SemF RVal := do
  liftRes (evalUnaryOpH (← frameHeap) op v)

def indexM (c i : RVal) : SemF RVal := do
  liftRes (indexValH (← frameHeap) c i)

def sliceM (cv lv uv sv : RVal) : SemF RVal := liftRes (sliceVal cv lv uv sv)

def truthyM (v : RVal) : SemF Bool := do
  liftRes (truthyH (← frameHeap) v)

def lenM (v : RVal) : SemF RVal := do
  liftRes (lenValH (← frameHeap) v)

/-- Store `env[target] := v` through the trunk's own target walker. -/
def assignM (target : Expr) (v : RVal) : SemF Unit := do
  let st ← get
  envPut (← liftRes (assignToH st.world.heap st.locals target v))

def dictBuildM (items : List (RVal × RVal)) : SemF (List (RVal × RVal)) := do
  liftRes (dictBuild (← frameHeap) [] items)

def ntupleAttrM (m : Module) (tn : String) (fields : Array String)
    (xs : Array RVal) (attr : String) : SemF RVal :=
  liftRes (ntupleAttr m tn fields xs attr)

/-! ## §3 THE FUEL BOUNDARY, DEFUNCTIONALIZED

`Kont` is the record of operations the fuel-free half may perform but cannot
define: they are the ones whose recursion is bounded by FUEL rather than by the
syntax. Making them a parameter is what lets `evalOpen`/`execOpen` be
`termination_by structural` on `Expr`/`Stmt` — measured: with the fuel matched
inside them instead, the interpreter is one `structural fuel` block again and
`mvcgen` makes no progress at a symbolic fuel (the pilot's Route B, 1 m 31 s to
return the goal unchanged).

`bottom` is the fuel-exhausted `Kont`: every operation answers `.timeout`. It is
what `kont m 0` is, and it is the reason a run out of fuel is loud rather than
wrong. -/
structure Kont where
  /-- The fuel level this `Kont` sits at. It is NOT a recursion argument here —
  the fueled recursion is on `kont`'s own `Nat` — but the trunk's fuel-TAKING
  pure workers (`evalCompareOpH`'s `heapEq`, `setDedup`) need a bound, and it
  must be the same one the trunk would have passed. -/
  fuel : Nat
  /-- Call a module-level function or method by qualified name. -/
  call : String → Array RVal → SemW RVal
  /-- Call a closure/nested def by its heap address. Takes the CALLER's locals
  because `cellsFor` resolves the snapshot's cell directory against them — the
  trunk passes `st.locals` here and dropping it would silently resolve captures
  against an empty frame. -/
  callClo : REnv → Addr → Array RVal → SemW RVal
  /-- `{k₁: v₁, k₂: v₂, …}` — the LOCKSTEP walk of two parallel expression
  lists. It rides here not because it needs fuel but because no single
  STRUCTURAL measure covers two parallel lists (Eval.lean §0.5); routing it
  through the record breaks the recursive knot and lets the walk be an ordinary
  structural definition below the block. -/
  dictItems : List Expr → List Expr → SemF (List (RVal × RVal))
  /-- `f(…, k=v, …)` — the call site's KEYWORD values, paired back with their
  names. Here for the SAME reason as `dictItems`: `kwargs.toList.map (·.2)` is a
  function APPLICATION, not a projection of the call node, so a block member
  cannot recurse on it. The knot boundary pays a third time. -/
  kwArgs : List (String × Expr) → SemF (List (String × RVal))
  /-- `while test: body else: orelse` — the non-structural statement. -/
  whileLoop : Expr → List Stmt → List Stmt → SemF RFlow
  /-- `for target in xs: body` over an already-materialized value sequence. -/
  forSeq : Expr → List RVal → List Stmt → SemF RFlow
  /-- `for target in <heap list at a>: body` — the LIVE index cursor. -/
  forList : Expr → Addr → Nat → List Stmt → SemF RFlow
  /-- Advance a generator one yield. -/
  stepIter : Addr → SemW (Option RVal)
  /-- THE CONTINUATION WALKER: run a generator body from its defunctionalized
  continuation to the next `yield`. Mutually fuel-recursive with `stepIter` — a
  generator consuming a generator re-enters through a `forGen` frame — so both
  ride the record and both step down one fuel level per re-entry, which is
  exactly the trunk's `execGen m fuel` / `stepIter m fuel` re-expressed. -/
  execGen : GenCont → SemF (Option (RVal × GenCont))
  /-- `for target in <generator>: body` — the LAZY cursor. -/
  forGen : Expr → Addr → List Stmt → SemF RFlow
  /-- Drain a generator to exhaustion (`sorted`/`max`/`min`/`sum`/`list`). -/
  drainIter : Addr → SemW (List RVal)
  /-- `any`/`all` over a generator: short-circuits, leaves it SUSPENDED. -/
  anyAllIter : Addr → Bool → SemW Bool

/-- The fuel-exhausted continuation: every fueled operation is `.timeout`.
This is `kont m 0`, and it is the ONLY source of `.timeout` in the rebuild —
which is exactly the property the plan's fuel ruling turns into a theorem. -/
def Kont.bottom : Kont where
  fuel        := 0
  call        := fun _ _   => exhausted
  callClo     := fun _ _ _ => exhausted
  dictItems   := fun _ _   => exhausted
  kwArgs      := fun _     => exhausted
  whileLoop   := fun _ _ _ => exhausted
  forSeq      := fun _ _ _ => exhausted
  forList     := fun _ _ _ _ => exhausted
  stepIter    := fun _     => exhausted
  execGen     := fun _     => exhausted
  forGen      := fun _ _ _ => exhausted
  drainIter   := fun _     => exhausted
  anyAllIter  := fun _ _   => exhausted

/-! ## §4 THE REBUILD FRONTIER

An arm the rebuild has NOT yet transliterated refuses with a message carrying
this prefix. It is deliberately DISTINGUISHABLE from every trunk refusal, and
that is the census instrument: `harness/monadic_gate.py` buckets the differential
battery's failures by arm, so the gate is a burn-down list rather than a number.

**This is not a semantic frontier and must never be confused with one.** A trunk
refusal is a statement about Python; one of these is a statement about the
rebuild's progress. They are spelled differently so no report can conflate
them. -/
def notYet (arm : String) : SemF α :=
  refuse s!"monadic-rebuild: arm not yet transliterated: {arm}"

def notYetW (arm : String) : SemW α :=
  refuse s!"monadic-rebuild: arm not yet transliterated: {arm}"

end LeanModels.Python.Monadic
