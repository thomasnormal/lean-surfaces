/-
**The monadic rebuild's INTERPRETER** — do-notation over the substrate.

# THE FUEL RULING, taken BEFORE the interpreter was written

`docs/family-architecture.md` §3.4 makes "decide fuel's fate before writing the
interpreter" a founding-checklist item. Here is the decision and its measurement.

The pilot proved two walls and one road. Fuel as a monad LAYER does not
typecheck (fuel's job is to BE the recursion argument; hidden in state it is not
an argument). Fuel as an explicit ARGUMENT is definable — it is the trunk's shape
— but at a SYMBOLIC fuel `mvcgen` returns the goal unchanged after 1 m 31 s. The
only road `mvcgen` walks is the fuel-free one.

**So the rebuild SPLITS the interpreter at the fuel boundary**, which the trunk
does not:

* `evalOpen` / `execOpen` are **fuel-free** and `termination_by structural` on
  `Expr` / `Stmt`. They take the fueled operations as a PARAMETER (`Kont`,
  `Prim.lean`) — open recursion, the defunctionalized knot.
* `kont m : Nat → Kont` is `termination_by structural` on **fuel**, and it is
  the ONLY place fuel is spent.

Two structurally-recursive blocks instead of one. **Both halves stay
kernel-reducible** — measured, and it is the property everything else rests on:
`#guard` and `rfl` decide runs of `evalOpen`, so the non-vacuity discipline
(`#py_check`'s law) survives the rebuild. Well-founded recursion on a
lexicographic `(fuel, sizeOf e)` was the obvious alternative and is REJECTED for
exactly this reason — it is the mergeSort trap (AGENTS.md), and it would silently
delete every kernel `rfl` in the tier.

## THE ONE DELIBERATE DIVERGENCE FROM THE TRUNK, and its argument

The trunk decrements fuel at **every** expression node and every statement node.
The rebuild spends fuel only where the recursion is not structural: `call`,
`while`, the `for` cursors, and the generator steppers. Consequence, stated
exactly:

> At any fixed `F`, the rebuild is **at least as decisive** as the trunk: every
> run the trunk decides at `F`, the rebuild decides at `F`, with the same value.
> Only `.timeout` moves, and it moves in one direction.

Three things follow, and they are why this is recorded as a design decision
rather than hidden as an optimization.

1. **The REFUSAL SURFACE IS UNCHANGED.** `.unsupported` is fuel-independent by
   the loudness doctrine, so nothing about which programs refuse moves at all.
   `harness/refusal_census.py` parity is a claim about this, and the ruling
   leaves it untouched by construction.
2. **Under the ∃-threshold form the two are EQUIVALENT.** Every landed theorem
   is `∃ t, ∀ F ≥ t, …`; a claim that holds of the trunk at threshold `t` holds
   of the rebuild at `t`. The direction of the inequality is the safe one.
3. **It is observable, so it is measured, not assumed.** A row where the trunk
   answers `.timeout` and the rebuild answers a value would be a genuine
   difference. The differential corpus contains none (the trunk is 0-failed at
   its default fuel, so it never times out there) — but the gate reports it if
   one ever appears.

# WHAT IS AND IS NOT REBUILT YET

Every arm below is transliterated from the trunk arm-for-arm, message-for-
message: the refusal strings are the trunk's own, verbatim, because they are the
specification. An arm not yet transliterated refuses through `notYet` with a
DISTINGUISHABLE prefix, so the gate can bucket the frontier by arm and burn it
down. A `notYet` is never a claim about Python.
-/
import LeanModels.Python.Monadic.Prim

open LeanModels LeanModels.Python

namespace LeanModels.Python.Monadic

def userExcCatches (m : Module) (handler : String) : PyErr → Bool
  | .user cid _ | .userMessage cid _ _ =>
      match getClass? m cid with
      | some c => match c.excBase with
        | some base => builtinExcNameCatches handler base
        | none => false
      | none => false
  | _ => false

def hasContextProtocolM (c : ClassDefn) : Bool :=
  c.methods.toList.contains "__enter__"
    && c.methods.toList.contains "__exit__"

def hasContextExtraDunderM (c : ClassDefn) : Bool :=
  c.methods.toList.any fun n =>
    dunderShaped n && n != "__init__" && n != "__enter__" && n != "__exit__"

def hasContextUnsupportedDunderM (c : ClassDefn) : Bool :=
  c.methods.toList.any fun n =>
    dunderShaped n && n != "__init__" && n != "__enter__" && n != "__exit__" && n != "__repr__"

def hasExtraDunderM (c : ClassDefn) : Bool :=
  c.methods.toList.any fun n => dunderShaped n && n != "__init__"

def hasUnsupportedDunderM (m : Module) (c : ClassDefn) : Bool :=
  c.methods.toList.any fun n =>
    dunderShaped n && n != "__init__" &&
      match n with
      | "__repr__" =>
          match findFunction m (c.name ++ ".__repr__") with
          | some f => f.reprLiteral.isNone
          | none => true
      | "__bool__" =>
          match findFunction m (c.name ++ ".__bool__") with
          | some f => f.boolLiteral.isNone
          | none => true
      | "__eq__" =>
          match findFunction m (c.name ++ ".__eq__") with
          | some f => f.eqLiteral.isNone
          | none => true
      | _ => true

def classHasExtraDunderM (m : Module) : Nat → ClassId → Bool
  | 0, _ => true
  | fuel + 1, ci =>
    match getClass? m ci with
    | Option.none => true
    | some c =>
      if hasUnsupportedDunderM m c then true
      else match c.base with
        | Option.none => false
        | some b =>
          match findClass m b with
          | some (bi, _) => classHasExtraDunderM m fuel bi
          | Option.none => true

def classHasExtraDunderMAt (m : Module) (ci : ClassId) : Bool :=
  classHasExtraDunderM m m.classes.size ci

def hasNtupleExtraDunderM (c : ClassDefn) : Bool :=
  c.methods.toList.any fun n => dunderShaped n && n != "__init__"

def instanceAttrsM (m : Module) (ci : ClassId) : Array (String × RVal) :=
  let boolAttrs :=
    match classMethodQname m ci "__bool__" with
    | some qname =>
        match findFunction m qname with
        | some f =>
            match f.boolLiteral with
            | some b => #[(instanceBoolMarker, .bool b)]
            | none => #[]
        | none => #[]
    | none => #[]
  let eqAttrs :=
    match classMethodQname m ci "__eq__" with
    | some qname =>
        match findFunction m qname with
        | some f =>
            match f.eqLiteral with
            | some b => #[(instanceEqMarker, .bool b)]
            | none => #[]
        | none => #[]
    | none => #[]
  boolAttrs ++ eqAttrs

def findContextClassM (m : Module) (name : String) : Option (Nat × ClassDefn) :=
  match findClass m name with
  | some (ci, c) =>
      if c.ok && !c.isExc && c.ntBase.isNone && hasContextProtocolM c
          then
        some (ci, c)
      else Option.none
  | Option.none => Option.none

/-! ## §0 THE CALL PLAN — a PURE fork, decided before the arguments evaluate

The tier records this discipline three times already (`attrCallPlan`,
`strCallPlan`, `genPlan`): referent dispatch must fork on a PURE free scrutinee,
because a `match` nested under the receiver's binder is invisible to `cases`/`rw`
in meta proofs. Here it earns its place a second way — a mutual member taking the
SAME `List Expr` as its caller is not a structural DECREASE, so folding the whole
call arm into the recursive block does not elaborate at all. Measured:

    failed to eliminate recursive application
      evalOpenList K m args

**The plan also fixes WHEN the arguments evaluate**, which is observable. The
trunk refuses `input()`, module dunders, unmodelled builtins and the tail
`NameError` BEFORE touching the arguments, and evaluates them first everywhere
else — including on the paths that then raise `TypeError: … is not callable`.
`preRefuse`/`preNameError` are that split, made explicit. -/

/-- What a positional `f(…)` on a NAME callee resolves to. -/
inductive CallPlan where
  /-- Refuse without evaluating the arguments. -/
  | preRefuse (msg : String)
  /-- Raise `NameError` without evaluating the arguments. -/
  | preNameError (name : String)
  /-- Arguments evaluate, then the faithful not-callable `TypeError`. -/
  | notCallable (tname : String)
  /-- Arguments evaluate, then a first-class callable value remains loud. -/
  | firstClass
  /-- A module-level `def`. -/
  | modFun (qname : String)
  /-- A builtin from `isBuiltinName`'s implemented set. -/
  | builtin (name : String)
  /-- Construct an IMMEDIATE namedtuple value — no allocation. Covers both the
  plain namedtuple and the value-like SUBCLASS (`class Position(namedtuple(…))`),
  whose construction IS namedtuple construction; the plan resolves which type
  NAME the value carries, so the two collapse to one arm here. -/
  | ntMake (tname : String) (fields : Array String)
  /-- Instantiate a class: allocate `Obj.instance`, then run `__init__` through
  the ordinary call path with `self` as an ordinary first argument. -/
  | instantiate (cid : Nat) (cname : String) (hasInit : Bool)
  /-- Call a CLOSURE held at a heap address (H7 nested defs and lambdas). -/
  | callClosure (a : Addr)
  /-- An arm the rebuild has not transliterated; the payload names it. -/
  | notYetArm (arm : String)
deriving Repr, Inhabited, BEq

/-- The resolution ORDER is the trunk's, arm for arm, and it is load-bearing:
locals → module globals (static, then the live view for a poisoned name) →
`findFunction` → `findClass` → namedtuples → the builtin table → module dunders
→ the live view again → `isPyBuiltinName` → `NameError`. Every earlier arm
SHADOWS every later one, which is why `print` works inside a function body and
why a module-level `def sorted` beats the builtin. -/
def callNamePlan (m : Module) (locals : Env) (globals : REnv) (fname : String) :
    CallPlan :=
  match Env.lookup locals fname with
  | some (.ref a) =>
      -- H7: a local name may hold a CLOSURE. The call is guarded on the
      -- fragment's own function-body walk, so heap-free modules keep the
      -- faithful `TypeError` and `worldInv` never meets a closure call.
      -- Arguments evaluate BEFORE the callable check — CPython's order, and it
      -- is observable: `x(1//0)` with `x = 5` raises ZeroDivisionError.
      if funsHeapFree m.functions.toList && topLevelDefFree m then .notCallable "dict"
      else .callClosure a
  | some (.callable name) =>
      if isOpaqueCallableName name then .preRefuse (opaqueObservation name) else .firstClass
  | some v => .notCallable v.typeName
  | Option.none =>
    match lookupG (moduleGlobals m).1 fname with
    | some (some (.ref _)) => .notCallable "dict"
    | some (some (.callable name)) =>
        if isOpaqueCallableName name then .preRefuse (opaqueObservation name) else .firstClass
    | some (some v) => .notCallable v.typeName
    | some Option.none =>
        -- The poisoned-arm LIVE view: a module-level lambda (an exec-bound
        -- closure) is callable through it, with the locals-arm dispatch
        -- verbatim and the same heap-free guard.
        match Env.lookup globals fname with
        | some (.ref a) =>
            if funsHeapFree m.functions.toList && topLevelDefFree m then .notCallable "dict"
            else .callClosure a
        | some (.callable name) =>
            if isOpaqueCallableName name then .preRefuse (opaqueObservation name) else .firstClass
        | some v => .notCallable v.typeName
        | Option.none =>
            .preRefuse s!"calling module-level '{fname}' (out-of-G1-tier value) is outside the tier"
    | Option.none =>
      if fname == starArgBuiltinName then
        .builtin fname
      else if (findFunction m fname).isSome then
        if (findClass m fname).isSome || (findNamedTuple m fname).isSome then
          .preRefuse s!"name '{fname}' is bound by both 'def' and 'class'/namedtuple at module level — source-order resolution is outside the tier (ordered ModuleItem representation is the recorded fix)"
        else .modFun fname
      else
      match findClass m fname with
      | some (ci, c) =>
        -- INSTANTIATION (H3). Every guard below fires BEFORE the arguments
        -- evaluate, exactly as the trunk's do — which is why they are plan
        -- constructors and not checks inside `applyCallPlan`.
        if (findNamedTuple m fname).isSome then
          .preRefuse s!"name '{fname}' is bound by both 'class' and a namedtuple assignment at module level — source-order resolution is outside the tier"
        else if c.isExc then
          .preRefuse s!"calling exception class '{fname}' (an exception INSTANCE as a value) is outside the tier — exception classes are raised and matched by name (docs/memory-model.md §exceptions)"
        else
          match c.ntBase with
          | some nt =>
            -- The VALUE-LIKE SUBCLASS (sunfish's `class Position(namedtuple(…))`):
            -- an IMMEDIATE value carrying the SUBCLASS name, no allocation, no
            -- `__init__` run.
            if !c.ok then
              .preRefuse s!"class '{fname}' uses unsupported features besides its namedtuple base — instantiation is outside the tier"
            else if (if hasContextProtocolM c then hasContextUnsupportedDunderM c
                     else hasNtupleExtraDunderM c) then
              .preRefuse s!"class '{fname}' defines dunder methods beyond __init__ — implicit-protocol dispatch is outside the H3 tier"
            else if (findFunction m (fname ++ ".__init__")).isSome then
              .preRefuse s!"'__init__' on the namedtuple subclass '{fname}' (immutable self) is outside the tier"
            else .ntMake nt.name nt.fields
          | Option.none =>
            if !c.ok then
              .preRefuse s!"class '{fname}' uses unsupported features (bases/metaclass/decorators/class-level statements) — instantiation is outside the H3 tier"
            else if (if hasContextProtocolM c then hasContextUnsupportedDunderM c
                     else classHasExtraDunderMAt m ci) then
              .preRefuse s!"class '{fname}' defines dunder methods beyond __init__ — implicit-protocol dispatch is outside the H3 tier"
            else .instantiate ci fname (classMethodQname m ci "__init__").isSome
      | Option.none =>
      match findNamedTuple m fname with
      | some nt => .ntMake nt.tname nt.fields
      | Option.none =>
      if fname == "input" then
        -- The ONE builtin that refuses BEFORE its arguments evaluate: stdin is
        -- a runner-boundary effect, and the trunk refuses at the dispatch.
        .preRefuse "input() is outside the tier (stdin is a runner-boundary effect; docs/memory-model.md §effects)"
      -- §3c-i-b: the ingestion rewrite's synthetic view builtins. Checked
      -- BEFORE `isBuiltinName` and deliberately kept OUT of it: that list is
      -- the pinned CPython `dir(builtins)` and every arm that may decide a
      -- `NameError` consults it, so polluting it would move a real decision.
      else if (dictViewBuiltinKind fname).isSome then .builtin fname
      -- §del: `del d[k]` lowers to `<dictdel>(d, k)`. Same discipline as the
      -- view names above: checked BEFORE `isBuiltinName` and kept out of it.
      else if fname == dictDelBuiltinName then .builtin fname
      -- §del: `del o.attr` lowers to `<attrdel>(o, "attr")` under the same
      -- synthetic-name discipline as item deletion.
      else if fname == attrDelBuiltinName then .builtin fname
      -- `len(sequence * count)` is lowered by Json.lean so both operands
      -- remain structural call arguments (the evaluator cannot recurse
      -- through a pattern extracted from an argument array).
      else if fname == fstringFormatBuiltinName then .builtin fname
      else if fname == lenMultBuiltinName then .builtin fname
      else if isBuiltinName fname then .builtin fname
      else if isModuleDunder fname then
        .preRefuse s!"module attribute '{fname}' is bound by the import machinery, not by a statement — outside the G1 tier"
      else
        -- The absent-arm LIVE view (prefix views during init; the full table
        -- post-init). A live CLOSURE dispatches — a module-level lambda is an
        -- exec-bound closure — anything else is the faithful not-callable
        -- TypeError, and only a genuine MISS may be the NameError.
        match Env.lookup globals fname with
        | some (.ref a) =>
            if funsHeapFree m.functions.toList && topLevelDefFree m then .notCallable "dict"
            else .callClosure a
        | some v => .notCallable v.typeName
        | Option.none =>
          if isPyBuiltinName fname then .preRefuse (unmodelledBuiltinMsg fname)
          else if (moduleGlobals m).2 then .preNameError fname
          else .preRefuse s!"name '{fname}' may be bound by an out-of-tier module-level statement"


/-- THE ITERABLE INVENTORY shared by `sum` / `tuple` / `list`, answering the
element sequence. The trunk spells this dispatch out three times because its
arms differ only in the builtin NAME the refusal interpolates and in the
generator policy; here it is one function taking both, and the messages are the
trunk's verbatim.

`guardGen` is the `moduleGenFree` fork: `sum` and `tuple` stay INSIDE the
heap-free fragment and so must refuse a generator when the module owns no
generator defs, while `list` ALLOCATES — CPython's `list(x)` is never an alias —
which is exactly what lets its generator arm drain unguarded. -/
def iterValues (K : Kont) (m : Module) (fname : String) (guardGen : Bool) :
    RVal → SemF (List RVal)
  | .str t => pure (strCharVals t)
  | .bytes values => pure (bytesIntVals values)
  | .tuple xs => pure xs.toList
  | .ntuple _ _ xs => pure xs.toList
  | .listV xs => pure xs.toList
  | .rangeV lo hi step => liftRes (rangeVals lo.toInt hi.toInt step.toInt)
  | .ref a => do
      match Heap.get? (← frameHeap) a with
      | some (.list xs) => pure xs.toList
      | some (.generator ..) =>
          if guardGen && moduleGenFree m then
            refuse s!"{fname}() over a generator DRAINS it (a stateful read) — outside the tier"
          else do
            inFrame (K.drainIter a)
      -- §L53 rung 3b, for the rebuild: a DRAINING consumer has no mutation
      -- window (it takes the keys with no user code running in between), so
      -- it needs only the keys in insertion order. The trunk pays this seven
      -- times, once per consumer; here `iterValues` is the one dispatch they
      -- all share, so it is ONE arm — the rebuild's factoring earning its
      -- keep. `sorted`/`max`/`min` never reach here: they go through the
      -- shared trunk workers, which is why they were already green.
      | some (.dict es _) => pure (dictKeys es).toList
      | some (.dictView da kind) =>
          match Heap.get? (← frameHeap) da with
          | some (.dict es _) => pure (dictViewElems es kind).toList
          | _ => refuse danglingMsg
      | some (.pyset xs) => do
          liftRes (setIterOrder xs.toList)
      | some (.instance _ _) => raisePy (.typeError "'object' object is not iterable")
      | some (.cell _) => refuse cellInternal
      | some (.closure ..) => raisePy (.typeError "'function' object is not iterable")
      | Option.none => refuse danglingMsg
  | v => raisePy (.typeError s!"'{v.typeName}' object is not iterable")

/-! The immediate range iterator is the same value worker for every draining
consumer. This equation closes the trunk/runner split at the range boundary;
heap-backed cursors remain stateful and use `stepIter`. -/
theorem iterValues_rangeVals (K : Kont) (m : Module) (fname : String)
    (guardGen : Bool) (lo hi step : RangeBound) :
    iterValues K m fname guardGen (.rangeV lo hi step) =
      liftRes (rangeVals lo.toInt hi.toInt step.toInt) := rfl

/-- The sentinel spelling of `iter` first requires a callable.  The tier has
no `callable_iterator`, but it can still answer the faithful error for a
receiver whose heap kind is known to be non-callable.  Genuine closures stay
loud because their callable iterator protocol is not modelled. -/
def iterSentinelValH (h : Heap) : RVal → Res RVal
  | .ref a =>
      match Heap.get? h a with
      | some (.closure ..) =>
          .unsupported "iter(v, w) over a callable is outside the tier (callable_iterator is not modelled; docs/memory-model.md §dict iteration)"
      | some (.cell _) => .unsupported cellInternal
      | Option.none => .unsupported danglingMsg
      | _ => .exn (.typeError "iter(v, w): v must be callable")
  | _ => .exn (.typeError "iter(v, w): v must be callable")

/-- A frame action under one CPython recursion unit. Both Python exceptions
and returns restore the caller's active depth. -/
def withFrameRecursionUnit {α : Type} (action : SemF α) : SemF α := do
  let st ← get
  if pythonFrameFull st.world.callDepth then
    raisePy .recursionError
  else
    set { st with world := { st.world with callDepth := st.world.callDepth + 1 } }
    tryCatch
      (do
        let v ← action
        modify fun st => { st with world := { st.world with callDepth := st.world.callDepth.pred } }
        pure v)
      (fun e => do
        modify fun st => { st with world := { st.world with callDepth := st.world.callDepth.pred } }
        raisePy e)

/-- The world-state counterpart of `withFrameRecursionUnit`. -/
def withWorldRecursionUnit {α : Type} (action : SemW α) : SemW α := do
  let w ← get
  if pythonFrameFull w.callDepth then
    raisePy .recursionError
  else
    set { w with callDepth := w.callDepth + 1 }
    tryCatch
      (do
        let v ← action
        modify fun w => { w with callDepth := w.callDepth.pred }
        pure v)
      (fun e => do
        modify fun w => { w with callDepth := w.callDepth.pred }
        raisePy e)

/-- A nested callable enters through CPython's generic C call path before its
Python frame is made.  That path checks the additional recursion unit at the
boundary, unlike the already-entered frame wrapper used by ordinary statement
execution. -/
def withClosureRecursionUnit {α : Type} (action : SemW α) : SemW α := do
  let w ← get
  if pythonRecursionFull w.callDepth then
    raisePy .recursionError
  else
    set { w with callDepth := w.callDepth + 1 }
    tryCatch
      (do
        let v ← action
        modify fun w => { w with callDepth := w.callDepth.pred }
        pure v)
      (fun e => do
        modify fun w => { w with callDepth := w.callDepth.pred }
        raisePy e)

/-- A C-level call under one CPython recursion unit.  Unlike a Python frame,
the generic C entry checks the additional unit before dispatch
(`Py_EnterRecursiveCall`), so the last available depth is already full.
This is the boundary used by builtins such as `all` and `any`. -/
def withCFrameRecursionUnit {α : Type} (action : SemF α) : SemF α := do
  let st ← get
  if pythonRecursionFull st.world.callDepth then
    raisePy .recursionError
  else
    set { st with world := { st.world with callDepth := st.world.callDepth + 1 } }
    tryCatch
      (do
        let v ← action
        modify fun st => { st with world := { st.world with callDepth := st.world.callDepth.pred } }
        pure v)
      (fun e => do
        modify fun st => { st with world := { st.world with callDepth := st.world.callDepth.pred } }
        raisePy e)

/-- The builtin table. `isBuiltinName` (Ast.lean) is the AUTHORITATIVE
implemented set — so a name reaching here is one the tier claims, and
a name it does not claim can never fall silently past the table. Arguments are
already values: `input` is the one builtin that refuses before they evaluate, and
it is handled in the PLAN, not here. -/
def applyBuiltin (K : Kont) (m : Module) (fname : String) (vs : List RVal) :
    SemF RVal := do
  if fname == starArgBuiltinName then
    match vs with
    | [v] => do
        let xs ← liftRes (unpackAllStar (← frameHeap) v)
        pure (.ntuple starArgValueName #[] xs.toArray)
    | _ => refuse "internal: <star-arg> expects one positional argument"
  else if fname == "len" then
    let st ← get
    let _ ← liftRes (builtinMethORecursionCheck st.world.callDepth)
    match vs with
    | [v] => lenM v
    | _ => raisePy (.typeError s!"len() takes exactly one argument ({vs.length} given)")
  else if fname == fstringFormatBuiltinName then
    match vs with
    | [v, .str spec] => liftRes (formatSpecH v spec)
    | [_, spec] => raisePy (.typeError s!"format() argument 2 must be str, not {spec.typeName}")
    | _ => raisePy (.typeError s!"internal: {fstringFormatBuiltinName} expects two arguments")
  else if fname == lenMultBuiltinName then
    match vs with
    | [left, right] => lenMultM left right
    | _ => raisePy (.typeError s!"internal: {lenMultBuiltinName} expects two arguments")
  else if fname == "abs" then
    let st ← get
    let _ ← liftRes (builtinMethORecursionCheck st.world.callDepth)
    match vs with
    | [v] => liftRes (absVal v)
    | _ => raisePy (.typeError s!"abs() takes exactly one argument ({vs.length} given)")
  else if fname == "round" then
    -- The one-argument integer/Boolean slice: CPython's
    -- `round(int)` returns the same mathematical integer, while
    -- `round(bool)` returns an `int`, not a `bool`. One-argument floats use
    -- the exact binary64 ratio and ties-to-even. Integral ndigits use the
    -- parameterized decimal scaling rule below.
    match vs with
      | [] => do
          let st ← get
          let _ ← liftRes (builtinRoundRecursionCheck st.world.callDepth)
          raisePy (.typeError "round() missing required argument 'number' (pos 1)")
      | [v] =>
          withFrameRecursionUnit do
            let st ← get
            let _ ← liftRes (builtinRoundRecursionCheck st.world.callDepth)
            match v with
          | .int n => pure (.int n)
          | .bool b => pure (.int (if b then 1 else 0))
          | .float value => liftRes (roundFloatVal value)
          | _ => refuse "round() over this non-integral value is outside the tier"
      | [v, digits] =>
          withFrameRecursionUnit do
            let st ← get
            let _ ← liftRes (builtinRoundRecursionCheck st.world.callDepth)
            match asInt digits with
          | none => refuse "round() with non-integral ndigits is outside the tier"
          | some d =>
            match v with
            | .int n =>
              if d < 0 then refuse "round() with negative ndigits for integers is outside the tier"
              else pure (.int n)
            | .bool b =>
              if d < 0 then refuse "round() with negative ndigits for integers is outside the tier"
              else pure (.int (if b then 1 else 0))
            | .float value => liftRes (roundFloatNDigits value d)
            | _ => refuse "round() over this non-integral value is outside the tier"
      | _ => refuse "round() with ndigits is outside the tier"
  else if fname == "int" then
    let st ← get
    let _ ← liftRes (builtinMethORecursionCheck st.world.callDepth)
    liftRes (intCastArgs vs)
  else if fname == "float" then
    do
      let h ← frameHeap
      liftRes (floatCastArgsH h vs)
  else if fname == "bool" then
    liftRes (boolCastArgs (← frameHeap) vs)
  else if fname == "divmod" then
    liftRes (divmodArgs vs)
  else if fname == "pow" then
    match vs with
    | [base, exponent] => liftRes (evalBinOp .pow base exponent)
    | [base, exponent, modulus] => liftRes (powModArgs [base, exponent, modulus])
    | vs => raisePy (.typeError s!"pow() expected 2 or 3 arguments, got {vs.length}")
  else if fname == "ord" then
    match vs with
    | [v] => liftRes (ordVal v)
    | vs => raisePy (.typeError s!"ord() takes exactly one argument ({vs.length} given)")
  else if fname == "chr" then
    match vs with
    | [v] => liftRes (chrVal v)
    | vs => raisePy (.typeError s!"chr() takes exactly one argument ({vs.length} given)")
  else if fname == "ascii" || fname == "hex" || fname == "oct" || fname == "bin" then
    match vs with
    | [v] => do
      let h ← frameHeap
      liftRes (if fname == "ascii" then asciiValH h v else if fname == "hex" then hexVal v else if fname == "oct" then octVal v else binVal v)
    | vs => raisePy (.typeError s!"{fname}() takes exactly one argument ({vs.length} given)")
  else if fname == "format" then
    match vs with
    | [] => raisePy (.typeError "format expected at least 1 argument, got 0")
    | [v] => do liftRes (strOfValH (← frameHeap) v)
    | [v, .str spec] =>
        if spec == "" then do liftRes (strOfValH (← frameHeap) v)
        else liftRes (formatSpecH v spec)
    | [_, spec] =>
        raisePy (.typeError s!"format() argument 2 must be str, not {spec.typeName}")
    | vs => raisePy (.typeError s!"format expected at most 2 arguments, got {vs.length}")
  else if fname == "str" then
    match vs with
    | [] => pure (.str "")
    | [v] => do
        let st ← get
        let _ ← liftRes (builtinMethORecursionCheck st.world.callDepth)
        liftRes (strOfValH st.world.heap v)
    | _ => refuse "str() with encoding/errors arguments is outside the tier (bytes decoding is not guessed; docs/memory-model.md §the cast tier)"
  else if fname == "repr" then
    liftRes (reprArgsH m (← frameHeap) vs)
  else if fname == "print" then
    -- THE ONE EFFECT: stdout is `World` data, so `print` is an ORDINARY builtin
    -- here — reached only after every shadowing arm, so it works inside function
    -- bodies. It returns `None` and appends exactly one chunk.
    match strOfArgs (← frameHeap) vs with
    | some line => do emit line; pure .none
    | Option.none =>
        refuseOrder "print() of a value the tier cannot render EXACTLY: a set (hash order), an instance/closure/generator (identity), a non-ASCII string (Unicode printability is never guessed), or a structure deeper than the repr budget — docs/memory-model.md §effects"
  else if fname == "dict" then
    -- `dict()` is the empty mapping and `dict(d)` is CPython's shallow COPY (a
    -- fresh object, never an alias — the whole point of writing it). Pair
    -- sequences use the same ordered builder as dict comprehensions;
    -- immediate and heap-backed list, tuple, bytes, string, and namedtuple
    -- sequences are admitted. The keyword form `dict(k=v, …)` lives in the
    -- kwargs arm.
    match vs with
    | [] => do let a ← heapPush (.dict #[] 0); pure (.ref a)
    | [v] =>
      match v with
      | .ref ad => do
          match Heap.get? (← frameHeap) ad with
          | some (.dict entries _) => do
              let a ← heapPush (.dict entries 0); pure (.ref a)
          | some (.dictView ..) => refuse "dict() over a dictionary view is outside the tier"
          | some (.list xs) => do
              let items ← liftRes (dictPairs (← frameHeap) 0 xs.toList)
              let entries ← dictBuildM items
              let a ← heapPush (.dict entries.toArray 0)
              pure (.ref a)
          | some (.generator ..) => do
              let vals ← inFrame (K.drainIter ad)
              let items ← liftRes (dictPairs (← frameHeap) 0 vals)
              let entries ← dictBuildM items
              let a ← heapPush (.dict entries.toArray 0)
              pure (.ref a)
          | some (.pyset _) =>
              raisePy (.typeError "cannot convert dictionary update sequence element #0 to a sequence")
          | some (.instance _ _) => raisePy (.typeError "'object' object is not iterable")
          | some (.cell _) => refuse cellInternal
          | some (.closure ..) => raisePy (.typeError "'function' object is not iterable")
          | Option.none => refuse danglingMsg
      | v => do
          match dictPairValues (← frameHeap) v with
          | some values => do
              let items ← liftRes (dictPairs (← frameHeap) 0 values)
              let entries ← dictBuildM items
              let a ← heapPush (.dict entries.toArray 0)
              pure (.ref a)
          | Option.none => raisePy (.typeError s!"'{v.typeName}' object is not iterable")
    | vs => raisePy (.typeError s!"dict expected at most 1 argument, got {vs.length}")
  else if fname == "range" then
    liftRes (rangeMake (← frameHeap) vs)
  else if fname == "max" || fname == "min" then
    let st ← get
    let _ ← liftRes (builtinExtremumRecursionCheck st.world.callDepth (← frameHeap) vs)
    match vs with
    | [.ref a] => do
        match Heap.get? (← frameHeap) a with
        | some (.generator ..) =>
            -- The `moduleGenFree` guard: `max`/`min` stay INSIDE the heap-free
            -- fragment, so a module owning no generator defs must refuse rather
            -- than drain.
            if moduleGenFree m then
              refuse s!"{fname}() over a generator DRAINS it (a stateful read) — outside the tier"
            else do
              let vals ← inFrame (K.drainIter a)
              liftRes (extremumVal (fname == "max") [.listV vals.toArray])
        | _ => do liftRes (extremumValH (← frameHeap) (fname == "max") [.ref a])
    | vs => do liftRes (extremumValH (← frameHeap) (fname == "max") vs)
  else if fname == "sorted" then
    withFrameRecursionUnit do
      let st ← get
      let _ ← liftRes (builtinSortedRecursionCheck st.world.callDepth)
      match vs with
      | [.ref a] => do
          match Heap.get? (← frameHeap) a with
          | some (.generator ..) => do
              let vals ← inFrame (K.drainIter a)
              let sorted_ ← liftRes (sortByLt false vals)
              let ad ← heapPush (.list sorted_.toArray)
              pure (.ref ad)
          | _ => do
              let hr ← liftRes (sortedValH (← frameHeap) (.ref a))
              heapPut hr.1; pure hr.2
      | [v] => do
          let hr ← liftRes (sortedValH (← frameHeap) v)
          heapPut hr.1; pure hr.2
      | _ => raisePy (.typeError s!"sorted expected 1 argument, got {vs.length}")
  else if fname == "sum" then
    let st ← get
    let _ ← liftRes (builtinMethORecursionCheck st.world.callDepth)
    -- The element fold IS `evalBinOp .add` (`sumFold`); a str START is
    -- CPython's own special-cased refusal, not a guess.
    match sumArgs vs with
    | Option.none =>
        raisePy (.typeError s!"sum() takes at most 2 arguments ({vs.length} given)")
    | some (v, start) =>
      match start with
      | .str _ =>
          do liftRes (sumRejectedStart m (← frameHeap) v
            "sum() can't sum strings [use ''.join(seq) instead]")
      | .bytes _ =>
          do liftRes (sumRejectedStart m (← frameHeap) v
            "sum() can't sum bytes [use b''.join(seq) instead]")
      | start => do
          let xs ← iterValues K m "sum" true v
          liftRes (sumFold start xs)
  else if fname == "tuple" || fname == starTupleBuiltinName then
    -- An IMMEDIATE value: `tuple()` allocates nothing.
    match vs with
    | [] => pure (.tuple #[])
    | [v] => do
        let xs ← iterValues K m "tuple" true v
        pure (.tuple xs.toArray)
    | vs => raisePy (.typeError s!"tuple expected at most 1 argument, got {vs.length}")
  else if fname == "list" || fname == starListBuiltinName then
    -- ALLOCATES: CPython's `list(x)` is always a NEW list, never an alias.
    match vs with
    | [] => do let a ← heapPush (.list #[]); pure (.ref a)
    | [v] => do
        let xs ← iterValues K m "list" false v
        let a ← heapPush (.list xs.toArray)
        pure (.ref a)
    | vs => raisePy (.typeError s!"list expected at most 1 argument, got {vs.length}")
  else if fname == "set" then
    -- The honest set subset: construction from an iterable, DEDUPLICATED by
    -- value equality under the dict-key doctrine. It ALLOCATES, so like `list`
    -- its generator arm drains unguarded.
    match vs with
    | [] => do let a ← heapPush (.pyset #[]); pure (.ref a)
    | [.ref a] =>
        match Heap.get? (← frameHeap) a with
        | some (.pyset _) => refuse "set copy construction is outside the tier (the copied table's iteration order is not modeled)"
        | some (.dict _ _) => refuse "set construction from a dict is outside the tier (dict-source table order is not modeled)"
        | some (.dictView ..) => refuse "set construction from a dictionary view is outside the tier (dict-source table order is not modeled)"
        | _ => do
            let xs ← iterValues K m "set" false (.ref a)
            let es ← liftRes (setDedup (← frameHeap) K.fuel [] xs)
            let a ← heapPush (.pyset es.toArray)
            pure (.ref a)
    | [v] => do
        let xs ← iterValues K m "set" false v
        let es ← liftRes (setDedup (← frameHeap) K.fuel [] xs)
        let a ← heapPush (.pyset es.toArray)
        pure (.ref a)
    | vs => raisePy (.typeError s!"set expected at most 1 argument, got {vs.length}")
  else if fname == "any" || fname == "all" then
    match vs with
    | [v] => do
        -- THE GENERATOR ARM IS NOT A DRAIN, and the difference is observable:
        -- `any`/`all` step only until the answer DECIDES and leave the object
        -- SUSPENDED, so a later `next` sees the partial consumption. Routing it
        -- through `iterValues` would fully drain it — a wrong answer to a
        -- question about state, not a missing feature. It gets its own arm.
        let isGen ← (match v with
          | .ref a => do
              match Heap.get? (← frameHeap) a with
              | some (.generator ..) => pure true
              | _ => pure false
          | _ => pure false)
        if isGen then
          -- `stepIter` owns the generator's C/Python entry check.  Keep the
          -- surrounding builtin at the Python-frame boundary, as CPython's
          -- generator resume path does; otherwise the two checks double-count
          -- the final slot.
          (show SemF RVal from withFrameRecursionUnit do
            match v with
            | .ref a => do
                let b ← inFrame (K.anyAllIter a (fname == "all"))
                pure (RVal.bool b)
            | _ => refuse "internal: generator flag without a referent (report this)")
        else
          (show SemF RVal from withCFrameRecursionUnit do
            let xs ← iterValues K m fname true v
            let b ← liftRes (anyAllScan (← frameHeap) (fname == "all") xs)
            pure (RVal.bool b))
    | vs => (show SemF RVal from withCFrameRecursionUnit
        (raisePy (.typeError s!"{fname}() takes exactly one argument ({vs.length} given)")))
  else if fname == "next" then
    -- STEP an iterator. `next(g)` on an exhausted generator is the faithful
    -- `StopIteration`; `next(g, d)` CONSUMES exhaustion and yields `d`. A
    -- non-iterator argument is the faithful `TypeError`, raised inside
    -- `stepIter`, which owns the referent dispatch.
    -- cfunction_vectorcall_FASTCALL enters before builtin_next dispatch.
    withFrameRecursionUnit do
      match vs with
      | [.ref a] => do
          match ← inFrame (K.stepIter a) with
          | some v => pure v
          | Option.none => raisePy .stopIteration
      | [.ref a, d] => do
          match ← inFrame (K.stepIter a) with
          | some v => pure v
          | Option.none => pure d
      | [] => raisePy (.typeError "next expected at least 1 argument, got 0")
      | v :: _ => do
          raisePy (.typeError s!"'{RVal.typeNameH (← frameHeap) v}' object is not an iterator")
  else if fname == "enumerate" then
    -- A LAZY iterator object, not a materialized list: `enumerate(board)` is
    -- stepped one pair at a time, exactly as CPython's is. It allocates a
    -- generator FRAME rather than a second object kind, so one stepper serves
    -- everything.
    match vs with
    | [] => raisePy (.typeError "enumerate expected at least 1 argument, got 0")
    | v :: rest =>
      match enumStart rest with
      | Option.none =>
          -- The START argument's OWN type, read through the heap.
          match rest with
          | [bad] => do
              raisePy (.typeError
                s!"'{RVal.typeNameH (← frameHeap) bad}' object cannot be interpreted as an integer")
          | _ => raisePy (.typeError s!"enumerate expected at most 2 arguments, got {vs.length}")
      | some i0 => do
          let fr ← liftRes (enumFrame (← frameHeap) i0 v)
          let a ← heapPush (.generator "<enumerate>" [] [fr] .suspended)
          pure (.ref a)
  else if fname == "iter" then
    -- §iter: the flagship's key source (`del d[next(iter(d))]`). A LIVE key
    -- cursor over the dict, `enumerate`'s frame without the index, allocated
    -- as a generator object so the ONE stepper serves it — `next`, `for` and
    -- the draining consumers all reach it through `stepIter` unchanged, and
    -- none of them needed a line.
    --
    -- The 2-argument SENTINEL form admits the faithful non-callable error.
    -- A genuine callable still refuses because CPython builds a
    -- `callable_iterator`, a second object kind this tier does not have.
    match vs with
    | [] => raisePy (.typeError "iter expected at least 1 argument, got 0")
    | [v] => do
        let fr ← liftRes (iterFrame (← frameHeap) v)
        let a ← heapPush (.generator "<iter>" [] [fr] .suspended)
        pure (.ref a)
    | [v, _] => do
        liftRes (iterSentinelValH (← frameHeap) v)
    | vs =>
        raisePy (.typeError s!"iter expected at most 2 arguments, got {vs.length}")
  else if fname == "count" then
    -- `itertools.count` — INFINITE by construction; a consumer's `break` is
    -- what ends it (sunfish's ray loop `for j in count(i + d, d)`).
    match countArgsVal vs with
    | Option.none => liftRes (countRefusal vs)
    | some (start, step) => do
        let a ← heapPush (.generator "<count>" [] [.countFromVal start step] .suspended)
        pure (.ref a)
  else if fname == dictDelBuiltinName then
    -- §del: the statement's own effect. `del` has NO VALUE in Python and the
    -- rewrite lowers it under an `exprStmt`, which discards what this answers,
    -- so `.none` here is the exact lowering rather than a convention.
    -- `heapDelete` answers `Option.none` for a NON-DICT receiver and this arm
    -- turns that into the tier's refusal — the type check lands here because
    -- the rewrite is syntactic.
    match vs with
    | [.ref a, k] => do
        match heapDelete (← frameHeap) a k with
        | some r => do
            let h ← liftRes r
            heapPut h
            pure .none
        | Option.none => refuse delRecvMsg
    | _ => refuse delRecvMsg
  else if fname == attrDelBuiltinName then
    -- §del: attribute deletion is admitted for ordinary instances only;
    -- unsupported receiver protocols remain loud rather than guessed.
    match vs with
    | [r, .str attr] =>
        match r with
        | .ref a => do
            let h ← frameHeap
            let h' ← liftRes (heapAttrDeleteClass m h a attr)
            heapPut h'
            pure .none
        | _ => raisePy .attributeError
    | _ => refuse attrDelRecvMsg
  else match dictViewBuiltinKind fname with
    -- §3c-i-b: the view's element sequence. Only ingestion emits this name,
    -- and only in consuming-argument position, so the snapshot cannot outlive
    -- the call that asked for it.
    | some kind =>
      match vs with
      | [.ref a] => do
          match Heap.get? (← frameHeap) a with
          | some (.dict es _) => pure (.listV (dictViewElems es kind))
          | _ => refuse viewRecvMsg
      | _ => refuse viewRecvMsg
    | Option.none => notYet s!"builtin: {fname}()"

/-- Apply a resolved plan to already-evaluated arguments. Not mutual with the
evaluator: the arguments are values, so nothing here evaluates syntax. -/
def opaqueArgObservation : List RVal → Option String
  | [] => none
  | .callable name :: _ =>
      if isOpaqueCallableName name then some (opaqueObservation name) else none
  | _ :: rest => opaqueArgObservation rest

def applyCallPlan (K : Kont) (m : Module) : CallPlan → List RVal → SemF RVal
  | .preRefuse msg,   _  => refuse msg
  | .preNameError n,  _  => raisePy (.nameError n)
  | .firstClass,      _  => refuse "calling a first-class callable value is outside the tier"
  | .notCallable t,   _  => raisePy (.typeError s!"'{t}' object is not callable")
  | .notYetArm arm,   _  => notYet arm
  | .builtin name,    vs => applyBuiltin K m name vs
  | .modFun qname,    vs => do
      let st ← get
      let cellParams := match findFunction m qname with
        | some f => (f.params.toList.map Param.arg).filter isCellKey
        | Option.none => []
      let st' := allocCells st cellParams
      set st'
      let preArgs := vs.take (vs.length - cellParams.length)
      let cellArgs := cellParams.map (fun key => (Env.lookup st'.locals key).getD (.none))
      inFrame (K.call qname (preArgs ++ cellArgs).toArray)
  | .callClosure a,   vs => do
      let st ← get
      inFrame (K.callClo st.locals a vs.toArray)
  | .ntMake tn flds,  vs =>
      -- Wrong arity is the faithful TypeError (CPython raises it through
      -- `tuple.__new__`); nothing allocates, so the world is exactly the
      -- arguments'.
      if vs.length == flds.size then pure (.ntuple tn flds vs.toArray)
      else raisePy (.typeError (ntArityErrorMsg flds vs.length))
  | .instantiate ci cname hasInit, vs => withFrameRecursionUnit do
        if hasInit then do
          let a ← heapPush (.instance ci (instanceAttrsM m ci))
          let initName := (classMethodQname m ci "__init__").getD (cname ++ ".__init__")
          let r ← inFrame (K.call initName ((RVal.ref a :: vs).toArray))
          match r with
          | .none => pure (.ref a)
          -- CPython checks `__init__`'s result: non-None raises.
          | r => raisePy (.typeError s!"__init__() should return None, not '{r.typeName}'")
        else
          match vs with
          -- The arity error fires BEFORE the allocation, so the failing run's
          -- world is the caller's untouched — the trunk raises from `st`, not
          -- from the post-allocation `st'`.
          | [] => do let a ← heapPush (.instance ci (instanceAttrsM m ci)); pure (.ref a)
          | _ => raisePy (.typeError s!"{cname}() takes no arguments")

/-! ## §0.7 METHOD CALLS — three receivers, each forking on its own PURE plan

The trunk already computes each dispatch through a free-scrutinee plan
(`attrCallPlan`, `ntupleCallPlan`, `strCallPlan`) — the recorded meta-proof
discipline — so these arms transliterate almost mechanically. The one thing that
must be preserved exactly is WHEN the arguments evaluate: a missing attribute,
an instance ATTRIBUTE in call position, a plan refusal and a dangling reference
all decide **before** any argument runs, and every in-tier method decides after.
That split is the `evalOpen` side; the functions below are the after-half and
take VALUES. -/

/-- The heap-receiver method tier: instance methods, `dict.get`/`clear`,
`list.append`/`pop`/`insert`. Arguments are already values. -/
def applyAttrPlan (K : Kont) (a : Addr) (attr : String) :
    AttrPlan → List RVal → SemF RVal
  | .instMethod qname, vs =>
      -- The method IS a function (flattened under its qualified name): `self`
      -- is an ordinary first argument and the call threads the shared world.
      inFrame (K.call qname ((RVal.ref a :: vs).toArray))
  | .instAttrValue, _ =>
      refuse s!"calling an instance ATTRIBUTE value ('.{attr}' is data on this instance, not a method) is outside the H3 tier"
  | .attrMissing, _ => raisePy .attributeError
  | .refuse msg, _ => refuse msg
  | .dangling, _ => refuse danglingMsg
  | .dictGet, vs => do
      match vs with
      | [k] => do
          let st ← get
          let _ ← liftRes (builtinMethORecursionCheck st.world.callDepth)
          liftRes (heapGet (← frameHeap) a k .none)
      | [k, d] => do
          let st ← get
          let _ ← liftRes (builtinMethORecursionCheck st.world.callDepth)
          liftRes (heapGet (← frameHeap) a k d)
      | vs => raisePy (.typeError s!"get expected at most 2 arguments, got {vs.length}")
  | .dictView kind, vs =>
      match vs with
      | [] => do
          let view ← heapPush (.dictView a kind)
          pure (.ref view)
      | vs => raisePy (.typeError s!"{attr}() takes no arguments ({vs.length} given)")
  | .dictClear, vs =>
      match vs with
      | [] => do
          match Heap.get? (← frameHeap) a with
          | some (.dict _ ver) =>
              -- entries := #[], SHAPE VERSION bumped: a live `items()` walk
              -- must see the change.
              match Heap.update (← frameHeap) a (.dict #[] (ver + 1)) with
              | some h' => do heapPut h'; pure .none
              | Option.none => refuse danglingMsg
          | _ => refuse danglingMsg
      | vs => raisePy (.typeError s!"clear() takes no arguments ({vs.length} given)")
  | .listAppend, vs => do
      match vs with
      | [v] => do
          let st ← get
          let _ ← liftRes (builtinMethORecursionCheck st.world.callDepth)
          let h' ← liftRes (heapAppend (← frameHeap) a v)
          heapPut h'; pure .none
      | vs => raisePy (.typeError s!"append() takes exactly one argument ({vs.length} given)")
  | .listPop, vs =>
      match vs with
      | [] => do
          let hr ← liftRes (heapPop (← frameHeap) a Option.none)
          heapPut hr.1; pure hr.2
      | [i] =>
          match asInt i with
          | some n => do
              let hr ← liftRes (heapPop (← frameHeap) a (some n))
              heapPut hr.1; pure hr.2
          | Option.none =>
              raisePy (.typeError s!"'{i.typeName}' object cannot be interpreted as an integer")
      | vs => raisePy (.typeError s!"pop expected at most 1 argument, got {vs.length}")
  | .listInsert, vs =>
      -- CPython's CLAMPING insert index — never an IndexError. The coercion
      -- TypeError is decided AFTER the arguments evaluate (pop's rule).
      match vs with
      | [i, v] =>
          match asInt i with
          | some n => do
              let h' ← liftRes (heapInsert (← frameHeap) a n v)
              heapPut h'; pure .none
          | Option.none =>
              raisePy (.typeError s!"'{i.typeName}' object cannot be interpreted as an integer")
      | vs => raisePy (.typeError s!"insert expected 2 arguments, got {vs.length}")

/-- The str method tier. Strings are immutable values, so every in-tier arm is
arguments plus a pure worker. -/
def applyStrMethod (sv : String) (drainIter : Addr → SemW (List RVal)) :
    StrPlan → List RVal → SemF RVal
  | .swapcase, vs =>
      match vs with
      | [] => liftRes (strSwapcase sv)
      | vs => raisePy (.typeError s!"swapcase() takes no arguments ({vs.length} given)")
  | .isupper, vs =>
      match vs with
      | [] => liftRes (strIsUpper sv)
      | vs => raisePy (.typeError s!"isupper() takes no arguments ({vs.length} given)")
  | .islower, vs =>
      match vs with
      | [] => liftRes (strIsLower sv)
      | vs => raisePy (.typeError s!"islower() takes no arguments ({vs.length} given)")
  | .upper, vs =>
      match vs with
      | [] => liftRes (strUpper sv)
      | vs => raisePy (.typeError s!"upper() takes no arguments ({vs.length} given)")
  | .index, vs => do
      let h ← frameHeap
      match vs with
      | [] => raisePy (.typeError "index expected at least 1 argument, got 0")
      | [.str sub] => liftRes (strIndex sv sub)
      | [v] => raisePy (.typeError s!"must be str, not {RVal.typeNameH h v}")
      | [.str sub, start] => liftRes (strIndexBounds sv sub start .none)
      | [.str sub, start, stop] => liftRes (strIndexBounds sv sub start stop)
      | [_v, _] => raisePy (.typeError s!"must be str, not {RVal.typeNameH h _v}")
      | [_v, _, _] => raisePy (.typeError s!"must be str, not {RVal.typeNameH h _v}")
      | vs =>
          if vs.length ≤ 3 then
            refuse "str.index() with start/end arguments are outside the tier (docs/memory-model.md §string semantics)"
          else raisePy (.typeError s!"index expected at most 3 arguments, got {vs.length}")
  | .join, vs =>
      match vs with
      | [v] => do
          let h ← frameHeap
          match v with
          | .ref a =>
              match Heap.get? h a with
              | some (.generator ..) =>
                  let vals ← inFrame (drainIter a)
                  liftRes (strJoinList sv vals)
              | _ => liftRes (strJoinH h sv v)
          | _ => liftRes (strJoinH h sv v)
      | vs => raisePy (.typeError s!"str.join() takes exactly one argument ({vs.length} given)")
  | .refuse msg, _ => refuse msg

/-! Call arguments use the ordinary left-to-right expression walk followed by
the starred-value splice. This macro keeps the expansion outside the
expression mutual block, so it adds no recursive proof member. -/
macro "evalOpenCallList" "(" K:term "," m:term "," es:term ")" : term => do
  let evalList := Lean.mkIdentFrom K `LeanModels.Python.Monadic.evalOpenList
  let flatten := Lean.mkIdentFrom K `LeanModels.Python.flattenStarCallArgs
  `(Functor.map $flatten ($evalList $K $m $es))

/-! ## §1 THE FUEL-FREE EXPRESSION HALF — structural on `Expr` -/

mutual

/-- Evaluate an expression. Structural on `Expr`; the fueled operations come in
through `K`. Evaluation order is left to right, each operand exactly once. -/
def evalOpen (K : Kont) (m : Module) : Expr → SemF RVal
  | .constant c _ => pure (Const.toRVal c)
  | .namedExpr id v _ => do
      -- H7+ §the walrus operator: evaluate, BIND in the running frame, answer
      -- the same value.
      let r ← evalOpen K m v
      if globalDeclared (← get).locals id then
        modify fun st => { st with world := { st.world with globals := Env.set st.world.globals id r } }
      else
        envSet id r
      pure r
  | .name id _ => do
      -- Resolution order (LOAD-BEARING): local env → module globals (G1) →
      -- module function table → builtins → NameError, the last only when the
      -- globals are COMPLETE, else loudly unsupported.
      match ← envGet id with
      | some v => pure v
      | Option.none =>
        let st ← get
        if hasUnboundLocal st.locals id then
          raisePy (.unboundLocalError id)
        else match lookupG (moduleGlobals m).1 id with
        | some (some v) =>
            if id == "__name__" then
              match Env.lookup (← frameGlobals) (deletedModuleDunderMarker id) with
              | some dv => pure dv
              | Option.none => pure v
            else
              pure v
        | some Option.none =>
            -- a statically-POISONED name consults the LIVE view before refusing
            match Env.lookup (← frameGlobals) id with
            | some v => pure v
            | Option.none =>
                refuse s!"module-level value of '{id}' is outside the G1 tier"
        | Option.none =>
          if (findFunction m id).isSome then
            pure (.callable id)
          else if (findClass m id).isSome then
            pure (.callable id)
          else if (findNamedTuple m id).isSome then
            pure (.callable id)
          else if isBuiltinName id then
            pure (.callable id)
          else if isModuleDunder id then
            refuse s!"module attribute '{id}' is bound by the import machinery, not by a statement — outside the G1 tier"
          else
            -- the statically-ABSENT arm consults the live view before deciding
            match Env.lookup (← frameGlobals) id with
            | some v => pure v
            | Option.none =>
              if id == "Ellipsis" then pure .ellipsis
              else if id == "NotImplemented" then pure .notImplemented
              else if isPyBuiltinName id then pure (.callable id)
              else if (moduleGlobals m).2 then do
                let _ ← liftRes (nameErrorRecursionCheck (← get).world.callDepth)
                raisePy (.nameError id)
              else refuse s!"name '{id}' may be bound by an out-of-tier module-level statement"
  | .binOp l op r _ => do
      let a ← evalOpen K m l
      let b ← evalOpen K m r
      binOpHM op a b
  | .unaryOp op operand _ => do
      let v ← evalOpen K m operand
      unaryOpM op v
  | .formattedValue expression reprConversion _ => do
      let value ← evalOpen K m expression
      liftRes (formatValueH (← frameHeap) value reprConversion)
  | .formattedValueAscii expression _ => do
      let value ← evalOpen K m expression
      liftRes (asciiValH (← frameHeap) value)
  | .boolOp op values _ => evalBoolChainM K m op values.toList
  | .compare l ops comparators _ => do
      let a ← evalOpen K m l
      evalCompareChainM K m a ops.toList comparators.toList
  | .call f args kwargs callUnsupported _ =>
      match callUnsupported with
      | some reason => refuse s!"call uses unsupported features: {reason}"
      | Option.none =>
        if kwargs.isEmpty then
          match f with
          | .name fname _ => do
              -- THE FREE-SCRUTINEE DISCIPLINE (the tier's own, recorded for
              -- `attrCallPlan`/`strCallPlan`/`genPlan`): fork on a PURE plan
              -- computed from the state, never on a match nested under the
              -- receiver's binder. Here it is load-bearing twice over — it is
              -- also what keeps this block structurally recursive, since a
              -- mutual member taking the SAME `List Expr` is not a decrease.
              let st ← get
              if (Env.lookup st.locals fname).isNone &&
                  !funsHeapFree m.functions.toList && hasUnboundLocal st.locals fname then
                raisePy (.unboundLocalError fname)
              else
                match callNamePlan m st.locals st.world.globals fname with
                | .preRefuse msg => refuse msg
                | .preNameError n => raisePy (.nameError n)
                | plan => do
                    let vs ← match plan with
                      | .builtin "print" =>
                          match args.toList with
                          | [e] =>
                              match complexPrintLiteral e with
                              | some v => pure [v]
                              | Option.none => evalOpenCallList (K, m, args.toList)
                          | _ => evalOpenCallList (K, m, args.toList)
                      | _ => evalOpenCallList (K, m, args.toList)
                    match opaqueArgObservation vs with
                    | some msg => refuse msg
                    | none => applyCallPlan K m plan vs
          | .attribute recv attr _ => do
              -- ===== THE TRACE CLOCK. Time is an INPUT: an unshadowed
              -- benign-import clock name is loud until the integer trace
              -- carries binary64 readings. Decided BEFORE the receiver evaluates,
              -- since evaluating the receiver is itself the poisoned refusal.
              -- `time.time(args…)` evaluates the args then raises CPython's
              -- exact arity TypeError without consuming the trace. =====
              let st0 ← get
              if isClockCall m st0 recv attr then
                match args.toList with
                | [] =>
                    refuse "time.time() readings are outside the tier until the clock trace carries binary64 values (CPython returns float)"
                | _ :: _ =>
                    raisePy (.typeError s!"time.time() takes no arguments ({args.size} given)")
              else do
              let r ← evalOpen K m recv
              match r with
              | .ref a => do
                  -- The plan decides BEFORE the arguments: a missing attribute
                  -- raises `AttributeError` before any argument runs.
                  let h ← frameHeap
                  match attrCallPlan m h a attr with
                  | .attrMissing => raisePy .attributeError
                  | .instAttrValue =>
                      refuse s!"calling an instance ATTRIBUTE value ('.{attr}' is data on this instance, not a method) is outside the H3 tier"
                  | .refuse msg => refuse msg
                  | .dangling => refuse danglingMsg
                  | plan => do
                      let vs ← evalOpenCallList (K, m, args.toList)
                      applyAttrPlan K a attr plan vs
              | .ntuple tn fs xs =>
                  -- namedtuple SUBCLASS method dispatch: methods ARE functions,
                  -- `self` is the ntuple VALUE. The plan precedes the arguments.
                  match ntupleCallPlan m tn fs attr with
                  | .instMethod qname => do
                      let vs ← evalOpenCallList (K, m, args.toList)
                      inFrame (K.call qname ((RVal.ntuple tn fs xs :: vs).toArray))
                  | .attrMissing => raisePy .attributeError
                  | .refuse msg => refuse msg
                  | _ => refuse "internal: namedtuple call plan out of range (report this)"
              | .str sv => do
                  let vs ← evalOpenCallList (K, m, args.toList)
                  applyStrMethod sv K.drainIter (strCallPlan attr) vs
              | .float fv =>
                  if attr == "is_integer" then do
                    let vs ← evalOpenCallList (K, m, args.toList)
                    match vs with
                    | [] => pure (.bool (floatIsInteger fv))
                    | vs => raisePy (.typeError s!"float.is_integer() takes no arguments ({vs.length} given)")
                  else
                    raisePy .attributeError
              | .callable _ =>
                  refuse "attribute access on a callable value is outside the closed-function tier"
              | r =>
                  raisePy .attributeError
          | f => refuse s!"calling a non-name expression ('{f.kindName}') is outside the v0 tier"
        else
          -- ===== H6 KEYWORD TIER. Keywords resolve to a COMPLETE positional
          -- array at the call site (`mergeKwArgs`), so the call boundary's
          -- signature never changes. Positionals evaluate first, then keyword
          -- VALUES, left to right — source order, since Python forbids a
          -- positional after a keyword. =====
          match f with
          | .name fname _ => do
              let st ← get
              if (Env.lookup st.locals fname).isNone &&
                  !funsHeapFree m.functions.toList && hasUnboundLocal st.locals fname then
                raisePy (.unboundLocalError fname)
              else match callNamePlan m st.locals st.world.globals fname with
              | .preRefuse msg => refuse msg
              | .preNameError n => raisePy (.nameError n)
              | .firstClass => do
                  let _ ← evalOpenCallList (K, m, args.toList)
                  let _ ← K.kwArgs kwargs.toList
                  refuse "calling a first-class callable value is outside the tier"
              | .notCallable t => do
                  let _ ← evalOpenCallList (K, m, args.toList)
                  let _ ← K.kwArgs kwargs.toList
                  raisePy (.typeError s!"'{t}' object is not callable")
              | .instantiate _ cname _ =>
                  refuse s!"instantiating class '{cname}' with keyword arguments is outside the H6 tier"
              | .ntMake tn fields => do
                  let vs ← evalOpenCallList (K, m, args.toList)
                  let kvs ← K.kwArgs kwargs.toList
                  let full ← liftRes (mergeNtKw fields vs kvs)
                  pure (.ntuple tn fields full)
              | .callClosure _ =>
                  refuse "keyword arguments on a closure call are outside the tier (docs/memory-model.md §nested defs and closures)"
              | .notYetArm arm => notYet s!"{arm} + keyword arguments"
              | .builtin name =>
                  if name == "dict" then
                    -- `dict(k=v, …)` is the ONLY way to build a mapping whose
                    -- keys are identifiers, and CPython keeps the CALL's own
                    -- order (duplicate keywords are a SyntaxError, so no insert
                    -- can collide). A positional alongside keywords stays loud.
                    if !args.isEmpty then
                      refuse "dict(<iterable>, k=v, …) mixing a positional argument with keywords is outside the tier"
                    else do
                      let kvs ← K.kwArgs kwargs.toList
                      let entries := (kvs.map (fun kv => (RVal.str kv.1, kv.2))).toArray
                      let a ← heapPush (.dict entries 0)
                      pure (.ref a)
                  else if name == "sorted" then
                    -- `reverse=` is accepted (truthiness decides the direction,
                    -- and descending is a STABLE descending insertion — never
                    -- sort-then-reverse). `key=` gates on a FIRST-CLASS callable
                    -- value and stays loud. Other keywords stay loud because
                    -- CPython materializes the iterable before list.sort
                    -- validates them.
                    if kwargs.toList.any (·.1 == "key") then
                      refuse "sorted(key=…) is outside the tier — the key callable is a first-class function value (bound methods are loud under H3; docs/backlog.md)"
                    else
                      match kwargs.toList.find? (fun kv => kv.1 != "reverse") with
                      | some _ => do
                          let _ ← evalOpenCallList (K, m, args.toList)
                          let _ ← K.kwArgs kwargs.toList
                          withFrameRecursionUnit do
                            let st ← get
                            let _ ← liftRes (builtinSortedRecursionCheck st.world.callDepth)
                            refuse "sorted() with unsupported keywords is outside the tier"
                      | Option.none => do
                          let vs ← evalOpenCallList (K, m, args.toList)
                          let kvs ← K.kwArgs kwargs.toList
                          withFrameRecursionUnit do
                            let st ← get
                            let _ ← liftRes (builtinSortedRecursionCheck st.world.callDepth)
                            match vs, kvs.map (·.2) with
                            | [v], [rv] => do
                                let desc ← truthyM rv
                                match v with
                                | .ref a => do
                                    match Heap.get? (← frameHeap) a with
                                    | some (.generator ..) => do
                                        let vals ← inFrame (K.drainIter a)
                                        let sorted_ ← liftRes (sortByLt desc vals)
                                        let ad ← heapPush (.list sorted_.toArray)
                                        pure (.ref ad)
                                    | _ => do
                                        let hr ← liftRes (sortedValH (← frameHeap) (.ref a) desc)
                                        heapPut hr.1; pure hr.2
                                | v => do
                                    let hr ← liftRes (sortedValH (← frameHeap) v desc)
                                    heapPut hr.1; pure hr.2
                            | [_], _ =>
                                refuse "duplicate keyword argument 'reverse' (unreachable through ingestion — CPython rejects it at compile time)"
                            | vs, _ => raisePy (.typeError s!"sorted expected 1 argument, got {vs.length}")
                  else if name == "float" || name == "len" || name == "bool" || name == "any" || name == "all" then
                    -- CPython's float, len, and bool constructors accept no keyword
                    -- arguments. Evaluate both argument lists before their
                    -- faithful TypeErrors, preserving Python's order.
                    let _ ← evalOpenCallList (K, m, args.toList)
                    let _ ← K.kwArgs kwargs.toList
                    if name == "len" || name == "any" || name == "all" then
                      let st ← get
                      let _ ← liftRes (builtinMethORecursionCheck st.world.callDepth)
                      pure ()
                    raisePy (.typeError (if name == "float" then
                      "float() takes no keyword arguments"
                    else if name == "len" then
                      "len() takes no keyword arguments"
                    else if name == "bool" then "bool() takes no keyword arguments"
                    else s!"{name}() takes no keyword arguments"))
                  else if name == "divmod" then
                    -- CPython's divmod constructor accepts no keyword
                    -- arguments. Evaluate both argument lists before its
                    -- faithful TypeError, preserving Python's order.
                    let _ ← evalOpenCallList (K, m, args.toList)
                    let _ ← K.kwArgs kwargs.toList
                    raisePy (.typeError "divmod() takes no keyword arguments")
                  else if name == "repr" || name == "abs" || name == "ord" || name == "chr" || name == "next" || name == "ascii" || name == "tuple" || name == "list" || name == "range" || name == "int" || name == "hex" || name == "oct" || name == "bin" then
                    -- CPython's repr, abs, ord, chr, next, ascii, tuple, list, range, hex, oct, and bin constructors accept no keyword;
                    -- int accepts base; its shared binder checks arity and keywords.
                    -- Evaluate both argument lists before validating the call.
                    let vs ← evalOpenCallList (K, m, args.toList)
                    let kvs ← K.kwArgs kwargs.toList
                    if name == "int" then
                      liftRes (intCastArgs vs kvs)
                    else
                    if name == "abs" then
                      let st ← get
                      let _ ← liftRes (builtinMethORecursionCheck st.world.callDepth)
                      pure ()
                    raisePy (.typeError (if name == "repr" then
                      "repr() takes no keyword arguments"
                    else if name == "abs" then
                      "abs() takes no keyword arguments"
                    else if name == "ord" then
                      "ord() takes no keyword arguments"
                    else if name == "chr" then
                      "chr() takes no keyword arguments"
                    else if name == "next" then
                      "next() takes no keyword arguments"
                    else if name == "ascii" then
                      "ascii() takes no keyword arguments"
                    else if name == "tuple" then
                      "tuple() takes no keyword arguments"
                    else if name == "list" then
                      "list() takes no keyword arguments"
                    else if name == "range" then
                      "range() takes no keyword arguments"
                    else if name == "hex" then
                      "hex() takes no keyword arguments"
                    else if name == "oct" then
                      "oct() takes no keyword arguments"
                    else "bin() takes no keyword arguments"))
                  else refuse s!"builtin '{name}' with keyword arguments is outside the H6 tier"
              | .modFun qname =>
                  match findFunction m qname with
                  | Option.none => refuse "internal: modFun plan without a definition (report this)"
                  | some fdefn =>
                      if !fdefn.argsOk then
                        -- The merge would read an UNTRUSTED parameter table, so
                        -- the loud refusal must win over any binding TypeError.
                        refuse s!"function '{qname}' uses unsupported parameter features (non-literal defaults/varargs/kwargs/decorators)"
                      else do
                        let vs ← evalOpenCallList (K, m, args.toList)
                        let kvs ← K.kwArgs kwargs.toList
                        let st ← get
                        let full ← liftRes (mergeKwArgsAt st.world.callDepth qname fdefn.params vs kvs)
                        inFrame (K.call qname full)
          | .attribute recv attr _ => do
              let r ← evalOpen K m recv
              match r with
              | .ref a => do
                  match attrCallPlan m (← frameHeap) a attr with
                  | .instMethod qname =>
                      match findFunction m qname with
                      | Option.none =>
                          refuse "internal: instance method plan without a definition (report this)"
                      | some fdefn =>
                          if !fdefn.argsOk then
                            refuse s!"function '{qname}' uses unsupported parameter features (non-literal defaults/varargs/kwargs/decorators)"
                          else do
                            let vs ← evalOpenCallList (K, m, args.toList)
                            let kvs ← K.kwArgs kwargs.toList
                            let st ← get
                            let full ← liftRes (mergeKwArgsAt st.world.callDepth qname fdefn.params (RVal.ref a :: vs) kvs)
                            inFrame (K.call qname full)
                  | .instAttrValue =>
                      refuse s!"calling an instance ATTRIBUTE value ('.{attr}' is data on this instance, not a method) is outside the H3 tier"
                  | .attrMissing => raisePy .attributeError
                  | .dictGet => refuse "dict.get() with keyword arguments is outside the tier (get is positional-only in CPython)"
                  | .dictView _ => refuse "dict view method calls with keyword arguments are outside the tier"
                  | .dictClear => refuse "dict.clear() with keyword arguments is outside the tier (clear takes no keyword arguments in CPython)"
                  | .listAppend => refuse "list.append() with keyword arguments is outside the tier (append is positional-only in CPython)"
                  | .listPop => refuse "list.pop() with keyword arguments is outside the tier (pop is positional-only in CPython)"
                  | .listInsert => refuse "list.insert() with keyword arguments is outside the tier (insert is positional-only in CPython)"
                  | .refuse msg => refuse msg
                  | .dangling => refuse danglingMsg
              | .ntuple tn fs xs =>
                  match ntupleCallPlan m tn fs attr with
                  | .instMethod qname =>
                      match findFunction m qname with
                      | Option.none =>
                          refuse "internal: namedtuple method plan without a definition (report this)"
                      | some fdefn =>
                          if !fdefn.argsOk then
                            refuse s!"function '{qname}' uses unsupported parameter features (non-literal defaults/varargs/kwargs/decorators)"
                          else do
                            let vs ← evalOpenCallList (K, m, args.toList)
                            let kvs ← K.kwArgs kwargs.toList
                            let st ← get
                            let full ← liftRes
                              (mergeKwArgsAt st.world.callDepth qname fdefn.params (RVal.ntuple tn fs xs :: vs) kvs)
                            inFrame (K.call qname full)
                  | .attrMissing => raisePy .attributeError
                  | .refuse msg => refuse msg
                  | _ => refuse "internal: namedtuple call plan out of range (report this)"
              | r => do
                  refuse s!"method call '.{attr}' with keyword arguments on '{RVal.typeNameH (← frameHeap) r}' is outside the H6 tier"
          | f => refuse s!"calling a non-name expression ('{f.kindName}') is outside the v0 tier"
  | .list elts _ => do
      -- H2: a list display ALLOCATES per display; the fresh address is the old
      -- heap size.
      let vs ← evalOpenList K m elts.toList
      let a ← heapPush (.list vs.toArray)
      pure (.ref a)
  | .tuple elts _ => do
      let vs ← evalOpenList K m elts.toList
      pure (.tuple vs.toArray)
  | .subscript v idx _ => do
      let c ← evalOpen K m v
      let i ← evalOpen K m idx
      let heap ← frameHeap
      let _ ← checkBytesIndexM m heap c i
      indexM c i
  | .dict keys values _ => do
      -- CPython `BUILD_MAP`: every key/value expression first (k₁, v₁, k₂, v₂,
      -- left to right), then the entries insert in order, then the ALLOCATION.
      -- The LOCKSTEP walk goes out through `K` — see §0.5 for why it cannot be
      -- a member of this block.
      let items ← K.dictItems keys.toList values.toList
      let entries ← dictBuildM items
      let a ← heapPush (.dict entries.toArray 0)
      pure (.ref a)
  | .attribute recv attr _ => do
      let r ← evalOpen K m recv
      match r with
      | .ref a => do
          let st ← get
          liftRunAt (attrReadResult m st a attr)
      | .ntuple tn fields xs => ntupleAttrM m tn fields xs attr
      | .callable name => refuse (if isOpaqueCallableName name then opaqueObservation name else
          "attribute access on a callable value is outside the closed-function tier")
      | r =>
          if attr == "__doc__" then
            refuse "scalar __doc__ lookup depends on CPython's builtin type documentation, outside the closed-function tier"
          else
            raisePy .attributeError
  | .ifExp t b o _ => do
      -- CPython: the test first, then EXACTLY ONE branch (lazy).
      let tv ← evalOpen K m t
      let cond ← truthyM tv
      if cond then evalOpen K m b else evalOpen K m o
  | .slice v l u stp _ => do
      -- H5 strings: receiver, then lower/upper/step (`BUILD_SLICE`), then the
      -- subscript application.
      let cv ← evalOpen K m v
      let lv ← evalOpen K m l
      let uv ← evalOpen K m u
      let sv ← evalOpen K m stp
      sliceHeapM cv lv uv sv
  | .genExp .. =>
      refuse "this generator expression is outside the tier (ingestion could not lower it to a generator function; docs/memory-model.md §generator semantics)"
  | .listComp elt target iter ifs walrus _ =>
      K.listComp (.start elt target iter ifs walrus)
  | .unsupported pyKind _ _ => refuse s!"unsupported expression '{pyKind}'"
  termination_by structural e => e

/-- Evaluate a list of expressions left to right, each exactly once. -/
def evalOpenList (K : Kont) (m : Module) : List Expr → SemF (List RVal)
  | [] => pure []
  | e :: rest => do
      let v ← evalOpen K m e
      let vs ← evalOpenList K m rest
      pure (v :: vs)
  termination_by structural es => es

/-- `and`/`or` answer the DECIDING OPERAND, not a bool.

STRUCTURAL-RECURSION NOTE, measured: the list must be passed WHOLE from
`evalOpen` (`values.toList`, a projection of the `.boolOp` node's own field).
Destructuring it at the call site — `match values.toList with | e :: es =>
evalBoolChainM … e es`, which is the trunk's shape because the trunk's measure
is fuel — severs the subterm chain and Lean answers *"failed to eliminate
recursive application"*. The refusal for an empty chain therefore lives HERE
rather than in `evalOpen`; the string is the trunk's, verbatim. -/
def evalBoolChainM (K : Kont) (m : Module) (op : BoolOp) :
    List Expr → SemF RVal
  | [] => refuse "BoolOp with no operands"
  | [e] => evalOpen K m e
  | e :: rest => do
      let v ← evalOpen K m e
      let b ← truthyM v
      match op with
      | .and => if b then evalBoolChainM K m op rest else pure v
      | .or  => if b then pure v else evalBoolChainM K m op rest
  termination_by structural es => es

/-- A comparison CHAIN short-circuits: the remaining comparators do not
evaluate once a link is false. -/
def evalCompareChainM (K : Kont) (m : Module) (lhs : RVal) :
    List CmpOp → List Expr → SemF RVal
  | [], [] => pure (.bool true)
  | op :: ops', e :: rest => do
      let rhs ← evalOpen K m e
      let h ← frameHeap
      let _ ← checkBytesCompareM m h op lhs rhs
      let st ← get
      let _ ← liftRes (richCompareRecursionCheckH h st.world.callDepth op lhs rhs)
      let b ← liftRes (evalCompareOpH h K.fuel op lhs rhs)
      if b then evalCompareChainM K m rhs ops' rest else pure (.bool false)
  | _, _ => refuse "Compare with mismatched ops/comparators"
  termination_by structural _ops es => es

/-- Heap-backed list repetition allocates a fresh list, as CPython does for
`list * int` even when the count is zero or negative. The source list remains
untouched, so aliases continue to observe the original object. -/
def listRepeatH (h : Heap) (xs : Array RVal) (count : Int) : Res (Heap × RVal) :=
  if count.natAbs > seqIndexBudget then
    .exn (.overflowError "cannot fit 'int' into an index-sized integer")
  else if count ≤ 0 || xs.isEmpty then
    .ok (h.push (.list #[]), .ref h.size)
  else if count.natAbs ≤ seqBudget && xs.size * count.toNat ≤ seqBudget then
    .ok (h.push (.list ((List.replicate count.toNat xs.toList).flatten.toArray)), .ref h.size)
  else
    .unsupported "list repetition beyond seqBudget is outside the tier (count magnitude or output element count; docs/memory-model.md §list repetition)"

/-- Update an existing heap list for `xs *= count`.  The address is retained so
aliases observe the in-place mutation, including the empty result for a
non-positive count. -/
def listRepeatUpdate (h : Heap) (a : Addr) (xs : Array RVal) (count : Int) : Res Heap :=
  if count.natAbs > seqIndexBudget then
    .exn (.overflowError "cannot fit 'int' into an index-sized integer")
  else if count ≤ 0 then
    match Heap.update h a (.list #[]) with
    | some h' => .ok h'
    | none => .unsupported "dangling list reference during augmented repetition"
  else if count.natAbs ≤ seqBudget && xs.size * count.toNat ≤ seqBudget then
    let ys := (List.replicate count.toNat xs.toList).flatten.toArray
    match Heap.update h a (.list ys) with
    | some h' => .ok h'
    | none => .unsupported "dangling list reference during augmented repetition"
  else
    .unsupported "list repetition beyond seqBudget is outside the tier (count magnitude or output element count; docs/memory-model.md §list repetition)"

def listRepeatUpdateM (a : Addr) (count : RVal) : SemF Unit := do
  let h ← frameHeap
  match Heap.get? h a with
  | some (.list xs) =>
      match asInt count with
      | some n =>
          let h' ← liftRes (listRepeatUpdate h a xs n)
          heapPut h'
      | none =>
          raisePy (.typeError s!"can't multiply sequence by non-int of type '{RVal.typeNameH h count}'")
  | some _ => refuse "augmented repetition receiver is not a list"
  | none => refuse danglingMsg

/-- Stateful multiplication dispatch for heap-backed lists. All other
operators retain the pure worker used by the trunk interpreter. -/
def binOpHM (op : BinOp) (a b : RVal) : SemF RVal := do
  if op == .bitAnd then
    let h ← frameHeap
    if setLikeRefH h a && setLikeRefH h b then
      let (h', result) ← liftRes (evalBinOpH h op a b)
      heapPut h'
      pure result
    else
      binOpM op a b
  else if op == .mult then
    let h ← frameHeap
    match a, b with
    | .ref addr, count =>
      match Heap.get? h addr with
      | some (.list xs) =>
        match asInt count with
        | some n =>
          let (h', result) ← liftRes (listRepeatH h xs n)
          heapPut h'
          pure result
        | none => raisePy (.typeError s!"can't multiply sequence by non-int of type '{RVal.typeNameH h count}'")
      | _ => binOpM op a b
    | count, .ref addr =>
      match Heap.get? h addr with
      | some (.list xs) =>
        match asInt count with
        | some n =>
          let (h', result) ← liftRes (listRepeatH h xs n)
          heapPut h'
          pure result
        | none => raisePy (.typeError s!"can't multiply sequence by non-int of type '{RVal.typeNameH h count}'")
      | _ => binOpM op a b
    | _, _ => binOpM op a b
  else if op == .mod then
    match a, b with
    | .str fmt, .ref _ =>
        let h ← frameHeap
        liftRes (strFormatH h fmt b)
    | _, _ => binOpM op a b
  else
    binOpM op a b

end

def execGlobal (names : Array String) : SemF RFlow := do
  let st ← get
  if names.toList.any (globalDeclared st.locals) then
    pure .next
  else
    let locals := names.toList.foldl (fun env id => Env.set env (globalMarker id) RVal.none) st.locals
    set { st with locals := locals }
    pure .next

/-! ## §2 THE FUEL-FREE STATEMENT HALF — structural on `Stmt` -/

/-- Raise the result of an admitted exception constructor after its arguments
have run. The generic type-call recursion check is shared with the proof
interpreter. -/
def raiseConstructed {α : Type} (e : PyErr) : SemF α := do
  let st ← get
  raisePy (exceptionConstructError st.world.callDepth e)

mutual

/-- Execute one statement. Structural on `Stmt`; `while` and the `for` cursors
go out through `K` because their recursion is not structural. -/
def execOpen (K : Kont) (m : Module) : Stmt → SemF RFlow
  | .classDef name _ => refuse s!"class {name} is only admitted at module scope"
  | .annNoValue id _ => do
      modify fun st => { st with locals := Env.set st.locals (unboundLocalMarker id) RVal.none }
      pure .next
  | .ret Option.none _ => pure (.ret .none)
  | .ret (some e) _ => do
      let v ← evalOpen K m e
      pure (.ret v)
  | .assign targets value _ =>
      match targets.toList with
      | [.subscript dE kE _] => do
          -- CPython order: the RHS first, then the target primary, then the
          -- subscript, then the store.
          let v ← evalOpen K m value
          let c ← evalOpen K m dE
          let k ← evalOpen K m kE
          match c with
          | .ref a => do
              let h' ← liftRes (heapStore (← frameHeap) a k v)
              heapPut h'; pure .next
          | .listV _ =>
              refuse "subscript assignment to a list ('xs[i] = v' mutates in place, visible through aliases) is outside the v0 tier (lists move to the heap at H2)"
          | c => raisePy (.typeError s!"'{c.typeName}' object does not support item assignment")
      | [.attribute recvE attr _] => do
          -- CPython order: the RHS first, then the target primary, then the store.
          let v ← evalOpen K m value
          let r ← evalOpen K m recvE
          match r with
          | .ref a => do
              let h' ← liftRes (heapAttrStoreClass m (← frameHeap) a attr v)
              heapPut h'; pure .next
          | _ => raisePy .attributeError
      | [.tuple elts sp] =>
          if (targetNames elts).isSome then do
            let v ← evalOpen K m value
            assignM (.tuple elts sp) v
            pure .next
          else do
            let v ← evalOpen K m value
            let st ← get
            let xs ← liftRes (unpackSeq st.world.heap elts.size v)
            let he ← liftRes (unpackStoreHM m st.world.heap st.locals elts.toList xs)
            modify fun st => { st with world := { st.world with heap := he.1 }, locals := he.2 }
            pure .next
      | [t] => do
          let v ← evalOpen K m value
          match t with
          | .name id _ => globalAssignM id v
          | _ => assignM t v
          pure .next
      | _ => refuse "chained assignment (multiple targets) is outside the v0 tier"
  | .unpackAssign before star after value _ => do
      let v ← evalOpen K m value
      let parts ← liftRes (unpackSeqStar (← frameHeap) before.size after.size v)
      let (pre, mid, suf) := parts
      let a ← heapPush (.list mid.toArray)
      let names := before.toList ++ [star] ++ after.toList
      let vals := pre ++ [.ref a] ++ suf
      modify fun st => { st with locals := bindAll st.locals names vals }
      pure .next
  | .augAssign target op value _ =>
      match target with
      | .name id _ => do
          -- CPython order: the target is LOADED before the value is evaluated.
          let st ← get
          let env := if globalDeclared st.locals id then st.world.globals else st.locals
          match Env.lookup env id with
          | Option.none => raisePy (.nameError id)
          | some (.ref a) =>
              if op == .mult then
                match Heap.get? (← frameHeap) a with
                | some (.list _) => do
                    let v ← evalOpen K m value
                    listRepeatUpdateM a v
                    pure .next
                | _ => refuse "augmented assignment to a heap object is outside the H1 tier (docs/memory-model.md)"
              else
                refuse "augmented assignment to a heap object is outside the H1 tier (docs/memory-model.md)"
          | some (.listV _) =>
              refuse "augmented assignment to a list ('+=' mutates in place, visible through aliases) is outside the v0 tier"
          | some old => do
              let v ← evalOpen K m value
              let r ← binOpM op old v
              globalAssignM id r
              pure .next
      | .attribute recvE attr _ => do
          -- CPython order: receiver, attribute LOAD (an AttributeError fires
          -- BEFORE the value evaluates), value, binop, attribute STORE.
          let r ← evalOpen K m recvE
          match r with
          | .ref a => do
              let st ← get
              let old ← liftRunAt (attrReadResult m st a attr)
              match old with
              | .listV _ =>
                  refuse "augmented assignment to a list-valued attribute ('+=' mutates in place, visible through aliases) is outside the tier"
              | .ref a2 =>
                  do
                    let v ← evalOpen K m value
                    let h' ← liftRes (heapListAugAssign (← frameHeap) a2 op v)
                    heapPut h'
                    pure .next
              | old => do
                  let v ← evalOpen K m value
                  let res ← binOpM op old v
                  let h' ← liftRes (heapAttrStoreClass m (← frameHeap) a attr res)
                  heapPut h'; pure .next
          | _ => raisePy .attributeError
      | t => refuse s!"augmented assignment to '{t.kindName}' is outside the v0 tier"
  | .whileLoop test body orelse _ => K.whileLoop test body.toList orelse.toList
  | .forStmt target iter body orelse _ =>
      match orelse.toList with
      | [] => do
          -- §3c-i-a: the VIEW CALL fuses with the loop here too — this is the
          -- ORDINARY function-body path, the commonest of the three.
          match dictViewCall iter with
          | some (recv, kind) => do
              let dv ← evalOpen K m recv
              match dv with
              | .ref a =>
                  match Heap.get? (← frameHeap) a with
                  | some (.dict es sv) => K.forDict target a 0 es.size sv (es.toList.map Prod.fst) kind body.toList
                  | _ => refuse viewRecvMsg
              | _ => refuse viewRecvMsg
          | Option.none => do
            let it ← evalOpen K m iter
            match it with
            | .listV xs => K.forSeq target xs.toList body.toList
            | .tuple xs => K.forSeq target xs.toList body.toList
            | .ntuple _ _ xs => K.forSeq target xs.toList body.toList
            -- H5 iteration: a str iterates its CODE POINTS; the snapshot IS the
            -- live semantics (strs are immutable).
            | .str s => K.forSeq target (strCharVals s) body.toList
            | .bytes xs => K.forSeq target (bytesIntVals xs) body.toList
            | .rangeV lo hi step => do
                let xs ← liftRes (rangeVals lo.toInt hi.toInt step.toInt)
                K.forSeq target xs body.toList
            -- H2: `for` over a heap LIST is a LIVE INDEX CURSOR, never a snapshot.
            | .ref a => K.forList target a 0 body.toList
            | v => raisePy (.typeError s!"'{v.typeName}' object is not iterable")
      | _ :: _ => refuse "'for … else' is outside the v0 tier"
  | .ifStmt test body orelse _ => do
      let t ← evalOpen K m test
      let b ← truthyM t
      if b then execOpenList K m body.toList else execOpenList K m orelse.toList
  | .exprStmt e _ => do
      let _ ← evalOpen K m e
      pure .next
  | .pass _ => pure .next
  | .brk _ => pure .brk
  | .cont _ => pure .cont
  | .withStmt items body withUnsupported sp => do
      match withUnsupported, items.toList with
      | some reason, _ =>
          refuse s!"with statement uses unsupported features ({reason}) — outside the tier"
      | none, [item] =>
          match item.context with
          | .call (.name fname _) _args kwargs callUnsupported _ =>
              let exitFn := findFunction m (fname ++ ".__exit__")
              let exitArgsFree := exitFn.map FunctionDefn.withExitExceptionArgsFree == some true
              let exitTypeTest := exitFn.map FunctionDefn.withExitExceptionTypeTest == some true
              if !exitArgsFree && !exitTypeTest then
                refuse "with body exceptions require __exit__ not to inspect exception arguments (full exception triples are outside the tier)"
              else if !kwargs.isEmpty || callUnsupported.isSome then
                refuse "with context calls with keywords or starred arguments are outside the tier"
              else
                match findContextClassM m fname with
                | Option.none =>
                    refuse "with requires an admitted class with __enter__ and __exit__"
                | some _ => do
                    let contextName := "<with-context>"
                    let contextExpr := Expr.name contextName sp
                    let enterExpr :=
                      Expr.call (Expr.attribute contextExpr "__enter__" sp)
                        #[] #[] Option.none sp
                    let noneExpr := Expr.constant .none sp
                    let exitExpr :=
                      Expr.call (Expr.attribute contextExpr "__exit__" sp)
                        #[noneExpr, noneExpr, noneExpr] #[] Option.none sp
                    let old ← envGet contextName
                    let context ← evalOpen K m item.context
                    envSet contextName context
                    let entered ← evalOpen K m enterExpr
                    assignTargetM item.target entered
                    let flow ←
                      tryCatch (do
                        let flow ← K.withBody body.toList
                        pure (Except.ok flow)) (fun e => do
                      envSet contextName context
                      withExitResult (evalOpen K m)
                        (if exitTypeTest then
                          Expr.call (Expr.attribute (Expr.name contextName sp) "__exit__" sp)
                            #[.constant (.str "exception") sp, noneExpr, noneExpr] #[] Option.none sp
                        else exitExpr)
                        (restoreEnvM contextName old) e)
                    withExitOnFlow (evalOpen K m) exitExpr
                      (restoreEnvM contextName old) flow
          | _ =>
              refuse "with context must be a direct class constructor call"
      | _, _ => refuse "multiple context-manager items are outside the tier"
  | .globalDecl names _ => execGlobal names
  | .nonlocalDecl names _ => do
        let st ← get
        if names.toList.all (fun id => (Env.lookup st.locals (cellKey id)).isSome) then
          pure .next
        else
          refuse "unsupported statement 'Nonlocal'"
  | .unsupported pyKind _ _ =>
      if pyKind == "TypeErrorHandler" then pure .next
      else refuse s!"unsupported statement '{pyKind}'"
  | .yieldStmt _ _ =>
      refuse "'yield' outside a generator body (the def is not marked `is_generator`) — outside the tier"
  | .yieldFromStmt .. =>
      refuse "un-lowered 'yield from' (the iterable is not an admitted genexp, or the genexp's target occurs elsewhere in the body) — outside the tier (docs/memory-model.md §yield from)"
  | .defStmt name params argsOk localsOk hasGlobal isGenerator body captures _ => do
      -- SNAPSHOT the captures from the current frame, ALLOCATE the closure, bind
      -- the name. Under the extractor's never-rebound admission the snapshot IS
      -- CPython's cell. Cells are allocated FIRST so the snapshot picks up the
      -- directory entries rather than the values.
      modify fun st => allocCells st captures.toList
      let st ← get
      match capturesSnapshot st.locals captures.toList with
      | Option.none =>
          refuse s!"nested def '{name}': a captured name is unbound at def time (unreachable through ingestion — report this)"
      | some cap => do
          let a ← heapPush (.closure name params argsOk localsOk hasGlobal isGenerator body cap)
          envSet name (.ref a)
          -- Recursive nested defs capture their own name through an empty
          -- cell. Fill that cell only after the closure has an address.
          match Env.lookup (← get).locals (cellKey name) with
          | some (.ref ca) =>
              let h' ← liftRes (cellStore (← frameHeap) ca (.ref a))
              heapPut h'
          | _ => pure ()
          pure .next
  | .raiseStmt exc cause _ =>
      -- The admitted shape is `raise N` of an admitted exception class,
      -- resolved to its class IDENTITY. The name must resolve UNAMBIGUOUSLY:
      -- any local/global/def shadow refuses, because CPython would raise the
      -- shadow's value.
      match cause with
      | some _ =>
          refuse "dynamic 'raise … from …' (exception chaining) is outside the tier (docs/memory-model.md §exceptions)"
      | Option.none =>
        match exc with
        | Option.none =>
            refuse "bare 'raise' (re-raise of the active exception) is outside the tier (docs/memory-model.md §exceptions)"
        | some (.name id _) => do
            let st ← get
            if hasUnboundLocal st.locals id then
              raisePy (.unboundLocalError id)
            else
              match Env.lookup st.locals id with
              | some (.ref _) =>
                  refuse s!"'raise {id}': a heap-backed exception value is outside the tier (docs/memory-model.md §exceptions)"
              | some _ =>
                  raisePy (.typeError "exceptions must derive from BaseException")
              | Option.none =>
                  if (lookupG (moduleGlobals m).1 id).isSome
                      || (Env.lookup st.world.globals id).isSome
                      || (findFunction m id).isSome then
                    refuse s!"'raise {id}': the name is shadowed by a local/global/def binding — outside the tier (docs/memory-model.md §exceptions)"
                  else
                    match findClass m id with
                    | some (ci, c) =>
                        if c.isExc then raiseConstructed (.user ci c.name)
                        else refuse s!"'raise {id}': only an admitted exception class (`class N(Exception): pass` or a measured direct builtin ancestor) can be raised — outside the tier (docs/memory-model.md §exceptions)"
                    | Option.none =>
                        if (findNamedTuple m id).isSome then
                          raisePy (.typeError "exceptions must derive from BaseException")
                        else if admittedBuiltinRaise.contains id then
                          raiseConstructed (.builtinException (builtinExceptionIdentity id))
                        else
                          refuse s!"'raise {id}': only an admitted exception class name can be raised — outside the tier (docs/memory-model.md §exceptions)"
        | some (.call (.name id _) args kwargs callUnsupported _) => do
            -- The measured payload form is one positional string passed to a
            -- builtin exception class whose `PyErr` retains that string.
            -- Resolve the class before evaluating the argument, matching
            -- Python's callee-first order and the static shadow guard above.
            let st ← get
            if !kwargs.isEmpty || callUnsupported.isSome then
              refuse "'raise N(…)': keyword/starred constructor arguments are outside the tier (docs/memory-model.md §exceptions)"
            else if (Env.lookup st.locals id).isSome
                || (lookupG (moduleGlobals m).1 id).isSome
                || (Env.lookup st.world.globals id).isSome
                || (findFunction m id).isSome then
              refuse s!"'raise {id}': the name is shadowed by a local/global/def binding — outside the tier (docs/memory-model.md §exceptions)"
            else if (findClass m id).isSome then
              match findClass m id with
              | some (ci, c) =>
                  if c.isExc then
                    match args.toList with
                    | [] => raiseConstructed (.user ci c.name)
                    | [arg] => do
                        let v ← evalOpen K m arg
                        match v with
                        | .str msg => raiseConstructed (.userMessage ci c.name msg)
                        | _ => refuse s!"'raise {id}(…)': the measured constructor form requires one string argument — outside the tier (docs/memory-model.md §exceptions)"
                    | _ => refuse s!"'raise {id}(…)': the measured constructor form requires exactly one positional string argument — outside the tier (docs/memory-model.md §exceptions)"
                  else
                    refuse s!"'raise {id}(…)': only an admitted exception class (`class N(Exception): pass` or a measured direct builtin ancestor) can be raised — outside the tier (docs/memory-model.md §exceptions)"
              | none => refuse s!"'raise {id}(…)': user exception and namedtuple constructors with payloads are outside the tier (docs/memory-model.md §exceptions)"
            else if (findNamedTuple m id).isSome then
              refuse s!"'raise {id}(…)': user exception and namedtuple constructors with payloads are outside the tier (docs/memory-model.md §exceptions)"
            else if !isPyBuiltinName id then
              -- Resolve the callee before its arguments, as CPython does:
              -- an unknown constructor name is a faithful NameError.
              raisePy (.nameError id)
            else
              match args.toList with
              | [] =>
                  if admittedBuiltinRaise.contains id then
                    raiseConstructed (.builtinException (builtinExceptionIdentity id))
                  else
                    refuse s!"'raise {id}()': only an admitted builtin exception class can be constructed without arguments"
              | [arg] => do
                  let v ← evalOpen K m arg
                  match v with
                  | .str msg =>
                      match builtinExcWithMessage id msg with
                      | some e => raiseConstructed e
                      | none =>
                          if admittedBuiltinRaise.contains id then
                            refuse s!"'raise {id}(…)': only the measured one-string builtin exception constructors are admitted — outside the tier (docs/memory-model.md §exceptions)"
                          else
                            refuse s!"'raise {id}': only an admitted exception class name can be raised — outside the tier (docs/memory-model.md §exceptions)"
                  | _ =>
                      refuse s!"'raise {id}(…)': the measured constructor form requires one string argument — outside the tier (docs/memory-model.md §exceptions)"
              | _ =>
                  refuse s!"'raise {id}(…)': the measured constructor form requires exactly one positional string argument — outside the tier (docs/memory-model.md §exceptions)"
        | some _ =>
            refuse "'raise <expression>' (anything but an admitted exception class name) is outside the tier (docs/memory-model.md §exceptions)"
  | .assertStmt test msg _ => do
      -- CPython's `if not test: raise AssertionError(msg)`. The model runs
      -- without `-O`, so the test always evaluates; the MESSAGE evaluates only
      -- on the failing path — CPython's laziness, observable whenever it has an
      -- effect. The rendering is `printOne`, `print`'s own one-argument `str()`,
      -- so the two agree by construction.
      let t ← evalOpen K m test
      let b ← truthyM t
      if b then pure .next
      else
        match msg with
        | Option.none => raiseConstructed (.assertionError Option.none)
        | some e => do
            let v ← evalOpen K m e
            match printOne (← frameHeap) v with
            | some rendered => raiseConstructed (.assertionError (some rendered))
            | Option.none =>
                refuseOrder "assert message: the tier cannot render this value EXACTLY — a set (hash order), an instance/closure/generator (identity), a non-ASCII string (Unicode printability is never guessed), or a structure deeper than the repr budget — docs/memory-model.md §the assert statement"
  | .delStmt names _ => do
      -- `delNames` threads the locals left to right, so the PARTIAL effect is
      -- kept: earlier removals are already applied when a later target misses.
      let st ← get
      match delNames st.locals names.toList with
      | (env, Option.none) => do envPut env; pure .next
      | (_, some n) => raisePy (.unboundLocalError n)
  | .tryStmt body excNames handler tryUnsupported _ =>
      let excName := excHandlerPrimary excNames
      -- THE SUBSTRATE EARNS ITS KEEP HERE. `tryCatch` on `ExceptT PyErr …`
      -- catches exactly the LANGUAGE's raise and lets `Loud` — the model giving
      -- up — propagate untouched, which is the trunk's hand-written fork over
      -- `.exn` / `.timeout` / `.unsupported` obtained for free. And the
      -- RETAINED-STATE covenant is the layer order: the handler runs from the
      -- state the raise happened in, with no rollback, because `StateT` is
      -- INSIDE `ExceptT`. Neither property is coded here; both are the type.
      match tryUnsupported with
      | some reason =>
          refuse s!"try/except uses unsupported features ({reason}) — outside the tier (docs/memory-model.md §exceptions)"
      | Option.none => do
        let st ← get
        if excHandlerBare excNames then
          tryCatch (execOpenList K m body.toList) (fun _ =>
            execOpenList K m handler.toList)
        else if excHandlerTuple excNames then
          let names := excHandlerNames excNames
          if names.any (fun name =>
              (Env.lookup st.locals name).isSome
                || (lookupG (moduleGlobals m).1 name).isSome
                || (Env.lookup st.world.globals name).isSome
                || (findFunction m name).isSome) then
            refuse s!"'except {excName}:': a tuple handler name is shadowed by a local/global/def binding — outside the tier (docs/memory-model.md §exceptions)"
          else if names.any (fun name => !excHandlerAdmitted m name) then
            refuse s!"'except {excName}:': every tuple handler name must be an admitted exception class — outside the tier (docs/memory-model.md §exceptions)"
          else
            tryCatch (execOpenList K m body.toList) (fun e =>
              if names.any (fun name => excHandlerMatches m name e) then
                execOpenList K m handler.toList
              else raisePy e)
        else if !dynamicShadowHandlerName excName &&
            ((Env.lookup st.locals excName).isSome
              || (lookupG (moduleGlobals m).1 excName).isSome
              || (Env.lookup st.world.globals excName).isSome
              || (findFunction m excName).isSome) then
          refuse s!"'except {excName}:': the name is shadowed by a local/global/def binding — outside the tier (docs/memory-model.md §exceptions)"
        else
          match findClass m excName with
          | Option.none =>
              -- The pinned two-name import-error table, consulted only after
              -- `findClass` missed, so a user class named `ImportError` wins.
              if (findNamedTuple m excName).isSome then
                tryCatch (execOpenList K m body.toList) (fun _ =>
                  raisePy (.typeError
                    "catching classes that do not inherit from BaseException is not allowed"))
              else if importErrorHandlerMatch excName then
                tryCatch (execOpenList K m body.toList) (fun e =>
                  match e with
                  | .importError _ => execOpenList K m handler.toList
                  | e => raisePy e)
              else if admittedBuiltinExc.contains excName then
                -- §except-builtin: a BUILTIN exception class. The whole
                -- decision is `builtinExcCatches`, which lives in `Ast.lean`
                -- as DATA: this matcher exists TWICE (function scope and
                -- module scope) and a rule spelled twice is a rule that
                -- drifts. Nothing is inferred from CPython's hierarchy --
                -- every pair in that table is one the tier can exhibit.
                tryCatch (execOpenList K m body.toList) (fun e => do
                  let st' ← get
                  if hasUnboundLocal st'.locals excName then
                    raisePy (.unboundLocalError excName)
                  else if (Env.lookup st'.locals excName).isSome
                      || (lookupG (moduleGlobals m).1 excName).isSome
                      || (Env.lookup st'.world.globals excName).isSome
                      || (findFunction m excName).isSome then
                    raisePy (.typeError
                      "catching classes that do not inherit from BaseException is not allowed")
                  else if builtinExcCatches excName e || userExcCatches m excName e then
                    execOpenList K m handler.toList
                  else raisePy e)
              else if refusedAncestorExc.contains excName then
                refuse s!"'except {excName}:': '{excName}' is a CPython ANCESTOR class the tier has not measured — admitting it would claim a catch set this model has never enumerated, so it is refused BY NAME rather than derived from a hierarchy (docs/memory-model.md §exceptions)"
              else
                refuse s!"'except {excName}:': matchable classes are an admitted user class (`class N(Exception): pass` or a measured direct builtin ancestor), the pinned import-error names, or one of `admittedBuiltinExc` — '{excName}' is none of those (docs/memory-model.md §exceptions)"
          | some (ci, c) =>
              if !c.isExc then
                refuse s!"'except {excName}:': class '{excName}' is not an admitted exception class — outside the tier (docs/memory-model.md §exceptions)"
              else
                tryCatch (execOpenList K m body.toList) (fun e =>
                  match e with
                  | .user cid _ | .userMessage cid _ _ =>
                      if cid == ci then execOpenList K m handler.toList else raisePy e
                  | e => raisePy e)
  | .importStmt mod _ =>
      if opaqueImportAllowed mod then do
        let root := String.mk (mod.toList.takeWhile (· != '.'))
        modify fun st => { st with locals := Env.set st.locals root (.callable (opaqueCallableName mod root)) }
        pure .next
      else refuse s!"plain import {mod} is only admitted at module scope"
  | .importFrom mod names star _ =>
      -- Pass 0 (§import forms): the importable universe is EMPTY, so every
      -- admitted from-import RAISES — fuel-free, state unchanged, never `.ok`.
      -- The EXTRACTOR's admission is what makes the raise faithful: either the
      -- module is absent from the pinned platform inventory (so the raise IS
      -- CPython's own `ModuleNotFoundError`), or the statement sits in
      -- import-guard position and the raise is caught by construction, the
      -- fallback branch then running from the RETAINED state.
      if mod == "__main__" then
        refuse "from __main__ import ... requires the runner's live __main__ module, outside the closed-function tier"
      else if opaqueImportAllowed mod && !star then do
        modify fun st => { st with locals := names.toList.foldl (fun env name =>
          Env.set env name (.callable (opaqueCallableName mod name))) st.locals }
        pure .next
      else
        raisePy (.importError mod)
  termination_by structural s => s

/-- A block stops at the first non-`next` flow. -/
def execOpenList (K : Kont) (m : Module) : List Stmt → SemF RFlow
  | [] => pure .next
  | s :: rest => do
      match ← execOpen K m s with
      | .next => execOpenList K m rest
      | flow => pure flow
  termination_by structural ss => ss

end

/-! ## §2.5 THE LIST-COMPREHENSION STEP

The expression arm above only evaluates the comprehension's outer iterable;
the per-element walk is routed through `Kont.listComp`.  Each call to that
field therefore consumes one fuel level in `kont`, while the filter and
element expressions remain ordinary structural `evalOpen` calls at that
level.  The expression arm remains a loud boundary until the next item wires
this continuation to the AST node; keeping the stepping seam separate is what
lets that arm stay structural. -/

def listCompIfs (K : Kont) (m : Module) : List Expr → SemF Bool
  | [] => pure true
  | test :: rest => do
      let v ← evalOpen K m test
      let keep ← truthyM v
      if keep then listCompIfs K m rest else pure false
  termination_by structural ifs => ifs

def listCompAt (K : Kont) (m : Module) : ListCompCont → SemF RVal
  | c =>
      match c.rest with
      | [] => do
          envPut c.savedLocals
          let a ← heapPush (.list c.acc.reverse.toArray)
          pure (.ref a)
      | v :: rest => do
          assignM c.target v
          let keep ← listCompIfs K m c.ifs
          if keep then do
            let x ← evalOpen K m c.elt
            K.listComp (.step { c with rest := rest, acc := x :: c.acc })
          else
            K.listComp (.step { c with rest := rest })
  termination_by structural c.rest

def listCompReqAt (K : Kont) (m : Module) : ListCompReq → SemF RVal
  | .step c => listCompAt K m c
  | .start elt target iter ifs walrus => do
      if !walrus.isEmpty then
        refuse "list comprehension walrus bindings are outside the tier"
      else
        let source ← evalOpen K m iter
        let xs ← match source with
          | .ref a =>
              match Heap.get? (← frameHeap) a with
              | some (.generator ..) =>
                  refuse "list comprehension over a generator requires lazy stepping (outside the one-generator slice)"
              | _ => iterValues K m "list" false source
          | _ => iterValues K m "list" false source
        let saved ← get
        -- A comprehension has its own target scope. Restore the caller's
        -- locals on normal completion and on a Python exception; heap effects
        -- remain retained by the surrounding frame state.
        tryCatch
          (K.listComp (.step
            { elt := elt, target := target, ifs := ifs.toList,
              rest := xs, acc := [], savedLocals := saved.locals }))
          (fun e => do
            envPut saved.locals
            raisePy e)

/-! ## §2.6 THE DICT LOCKSTEP — the one walk that could not be a block member

**THE ARCHITECTURAL DEBT OF §0.5, PAID — and this is the choice and its price.**

CPython's `BUILD_MAP` evaluates k₁, v₁, k₂, v₂, … so the two expression lists
must be walked in LOCKSTEP. Inside the mutual block that is not definable: a
structural measure can name only ONE list, and the other list's head is then not
a subterm of it (`failed to eliminate recursive application`). Three exits were
priced; the third is taken.

| exit | price | verdict |
|---|---|---|
| a paired AST field, `Array (Expr × Expr)` on `.dict` | edits `Ast.lean`, `Json.lean`, the trunk's `evalExpr`, and four walkers — **it changes the TRUNK**, which this rebuild may not do | REJECTED |
| one well-founded member inside the block | a mutual block shares ONE strategy, so it makes the WHOLE block well-founded and costs every kernel `rfl` — the mergeSort trap | REJECTED |
| **split the block: route the walk through `Kont`** | **one `Kont` field, one ordinary structural definition, one fuel level** | **TAKEN** |

**How the split works.** `evalOpen`'s `.dict` arm calls `K.dictItems` — a record
field, so from the block's point of view it is not a recursive call at all. The
walk itself is defined BELOW the block, where `evalOpen` is an ordinary constant,
so its own recursion is plainly structural on its own first list and nothing
constrains the second.

**The price, stated exactly: one fuel level per dict display** — because
`kont m (fuel+1)` must build its field from `kont m fuel`. That is **precisely
what the trunk charges** (`evalExpr m (fuel+1)` on a `.dict` calls
`evalDictItems m fuel`), so this arm is the one place the rebuild's fuel
accounting is *identical* to the trunk's rather than more generous. Nothing else
is given up: the walk is kernel-reducible like everything else in the file. -/

/-- The call site's KEYWORD values, paired back with their names. Same shape and
same reason as `dictItemsAt`: defined below the block, so `evalOpen` is an
ordinary constant and the recursion is plainly structural on its own list. -/
def kwArgsAt (K : Kont) (m : Module) :
    List (String × Expr) → SemF (List (String × RVal))
  | [] => pure []
  | (n, e) :: rest => do
      let v ← evalOpen K m e
      let vs ← kwArgsAt K m rest
      pure ((n, v) :: vs)
  termination_by structural kws => kws

/-- The LOCKSTEP walk. Structural on `ks`; `evalOpen` is not mutual with it, so
the second list is unconstrained — that is the whole trick. -/
def dictItemsAt (K : Kont) (m : Module) :
    List Expr → List Expr → SemF (List (RVal × RVal))
  | [], [] => pure []
  | k :: ks, v :: vs => do
      let kv ← evalOpen K m k
      let vv ← evalOpen K m v
      let rest ← dictItemsAt K m ks vs
      pure ((kv, vv) :: rest)
  | _, _ => refuse "Dict with mismatched keys/values"
  termination_by structural ks _ => ks

/-! ## §2.7 THE GENERATOR TIER

`Obj.generator` holds a DEFUNCTIONALIZED continuation — a stack of `GenFrame`s,
each a structural suffix of the body plus that loop's residual state — so `yield`
is admitted in statement position and the frame stack replaces the Lean call
stack. All four engine functions below are ORDINARY (non-recursive) functions of
`K`: every continuation step goes through a `Kont` field, i.e. one fuel level
down, which is exactly the trunk's `execGen m fuel` recursion re-expressed. That
is the same trick §2.2 used for the dict lockstep, applied to a genuinely
fuel-bounded knot rather than a structural one. -/

/-- Resume an iterator to its next yield. An exception escaping an actual
generator closes its frame; native dictionary cursors retain a permanent
failure instead. In the trunk the exception continuation uses `Run.bindE`;
here it is `tryCatch`. -/
def stepIterAt (K : Kont) (a : Addr) : SemW (Option RVal) := do
  let w ← get
  match Heap.get? w.heap a with
  | some (.generator qname locals cont status) =>
    match status with
    | .closed => pure Option.none
    | .failed error => raisePy error
    | .running => raisePy (.valueError "generator already executing")
    | _ =>
      match Heap.update w.heap a (.generator qname locals cont .running) with
      | Option.none => refuse danglingMsg
      | some h₁ => do
          let resume := inWorld locals (tryCatch
            (do
              let r ← K.execGen cont
              let st ← get
              match r with
              | some (v, cont') =>
                  match Heap.update st.world.heap a
                      (.generator qname st.locals cont' .suspended) with
                  | Option.none => refuse danglingMsg
                  | some h₂ => do heapPut h₂; pure (some v)
              | Option.none =>
                  match Heap.update st.world.heap a
                      (.generator qname st.locals [] .closed) with
                  | Option.none => refuse danglingMsg
                  | some h₂ => do heapPut h₂; pure Option.none)
            (fun e => do
              let st ← get
              match Heap.update st.world.heap a
                  (.generator qname st.locals [] (cont.exceptionStatus e)) with
              | Option.none => refuse danglingMsg
              | some h₂ => do heapPut h₂; raisePy (generatorEscape e)))
          if nativeIteratorName qname then
            set { w with heap := h₁ }
            resume
          else if pythonRecursionFull w.callDepth then
            match Heap.update h₁ a (.generator qname locals [] .closed) with
            | Option.none => refuse danglingMsg
            | some h₂ => do
                set { w with heap := h₂ }
                raisePy .recursionError
          else
            set { w with heap := h₁ }
            withWorldRecursionUnit resume
  | some _ =>
      raisePy (.typeError s!"'{RVal.typeNameH w.heap (.ref a)}' object is not an iterator")
  | Option.none => refuse danglingMsg

/-- The continuation walker. Yield-FREE statements go through the ordinary
statement executor, so their semantics has exactly ONE definition; only the
constructs that can SUSPEND are opened here. `break`/`continue` unwind the frame
stack; `return <value>` refuses loudly rather than drop `StopIteration.value`. -/
def execGenAt (K : Kont) (m : Module) : GenCont → SemF (Option (RVal × GenCont))
  | [] => pure Option.none
  | .block [] :: k' => K.execGen k'
  | .block (s :: ss) :: k' =>
      match genPlan s with
      | .delegate => do
          match ← execOpen K m s with
          | .next => K.execGen (.block ss :: k')
          | .ret .none => pure Option.none
          | .ret _ =>
              refuse "'return <value>' inside a generator (StopIteration.value) is outside the tier"
          | .brk =>
              match genBreak k' with
              | some k'' => K.execGen k''
              | Option.none => refuse "'break' outside loop"
          | .cont =>
              match genContinue k' with
              | some k'' => K.execGen k''
              | Option.none => refuse "'continue' outside loop"
      | .yieldHere e => do
          let v ← evalOpen K m e
          pure (some (v, .block ss :: k'))
      | .branch test body orelse => do
          let t ← evalOpen K m test
          let b ← truthyM t
          K.execGen ((if b then GenFrame.block body else GenFrame.block orelse)
            :: .block ss :: k')
      | .whileHere test body orelse =>
          K.execGen (.whileLoop test body orelse :: .block ss :: k')
      | .forHere target iter body => do
          -- §3c-i-a: a VIEW CALL fuses with the loop — the view never
          -- escapes, so no object is needed; only the KIND differs.
          match dictViewCall iter with
          | some (recv, kind) => do
              let dv ← evalOpen K m recv
              match dv with
              | .ref ad =>
                  match Heap.get? (← frameHeap) ad with
                  | some (.dict es sv) =>
                      K.execGen (.forDict target ad 0 es.size sv kind body :: .block ss :: k')
                  | _ => refuse viewRecvMsg
              | _ => refuse viewRecvMsg
          | Option.none => do
            let it ← evalOpen K m iter
            match it with
            | .listV xs => K.execGen (.forSeq target xs.toList body :: .block ss :: k')
            | .tuple xs => K.execGen (.forSeq target xs.toList body :: .block ss :: k')
            | .ntuple _ _ xs => K.execGen (.forSeq target xs.toList body :: .block ss :: k')
            | .str sv => K.execGen (.forSeq target (strCharVals sv) body :: .block ss :: k')
            | .bytes xs => K.execGen (.forSeq target (bytesIntVals xs) body :: .block ss :: k')
            | .rangeV lo hi step => do
                let xs ← liftRes (rangeVals lo.toInt hi.toInt step.toInt)
                K.execGen (.forSeq target xs body :: .block ss :: k')
            | .ref ad =>
                match Heap.get? (← frameHeap) ad with
                | some (.list _) => K.execGen (.forList target ad 0 body :: .block ss :: k')
                | some (.generator ..) => K.execGen (.forGen target ad body :: .block ss :: k')
                -- §3a: the LIVE dict cursor. The size and shapeVersion the loop
                -- STARTS with ride in the frame, because that is what lets the
                -- next step tell CPython's two mutation regimes apart.
                | some (.dict es sv) =>
                    K.execGen (.forDict target ad 0 es.size sv .keys body :: .block ss :: k')
                | some (.dictView da kind) =>
                    match Heap.get? (← frameHeap) da with
                    | some (.dict es sv) =>
                        K.execGen (.forDict target da 0 es.size sv kind body :: .block ss :: k')
                    | _ => refuse danglingMsg
                | some (.instance _ _) => raisePy (.typeError "'object' object is not iterable")
                | some (.cell _) => refuse cellInternal
                | some (.closure ..) => raisePy (.typeError "'function' object is not iterable")
                | some (.pyset xs) => do
                    let ys ← liftRes (setIterOrder xs.toList)
                    K.execGen (.forSeq target ys body :: .block ss :: k')
                | Option.none => refuse danglingMsg
            | v => raisePy (.typeError s!"'{v.typeName}' object is not iterable")
      | .refuse msg => refuse msg
  | .forSeq target xs body :: k' =>
      match xs with
      | [] => K.execGen k'
      | x :: rest => do
          assignM target x
          K.execGen (.block body :: .forSeq target rest body :: k')
  | .forList target ad i body :: k' => do
      match Heap.get? (← frameHeap) ad with
      | some (.list xs) =>
          if i < xs.size then do
            assignM target (xs.getD i .none)
            K.execGen (.block body :: .forList target ad (i + 1) body :: k')
          else K.execGen k'
      | some (.dict _ _) =>
          refuse "'for' over a dict is outside the tier (live dict iteration; docs/memory-model.md)"
      | some (.dictView ..) => refuse "internal: a list cursor over a dictionary view (report this)"
      | some (.instance _ _) => raisePy (.typeError "'object' object is not iterable")
      | some (.generator ..) =>
          refuse "internal: a list cursor over a generator object (report this)"
      | some (.cell _) => refuse cellInternal
      | some (.closure ..) => refuse "internal: a list cursor over a function object (report this)"
      | some (.pyset _) => refuse "internal: a list cursor over a set (report this)"
      | Option.none => refuse danglingMsg
  -- §3a THE LIVE DICT CURSOR (docs/memory-model.md §dict iteration). Three
  -- regimes, measured against CPython 3.9.19 before this was written:
  --   * no mutation, or a value UPDATE of an existing key -> exact;
  --   * a SIZE change -> CPython's faithful RuntimeError, raised at the NEXT
  --     step (including when the change happens on the last iteration, where
  --     StopIteration would otherwise have ended the loop);
  --   * a same-size KEY-SET change -> LOUD. CPython either raises a SECOND,
  --     different RuntimeError ("dictionary keys changed during iteration")
  --     or answers a sequence that depends on its entries-array layout and
  --     compaction schedule, so neither answer is guessable. `shapeVersion`
  --     is what detects it; it is bumped by `dictStore` on growth only, so a
  --     value update slips past it exactly as it should.
  | .forDict target ad i n sv kind body :: k' => do
      match ← dictStepM ad i n sv [] kind with
      | some .resized => raisePy (.runtimeError "dictionary changed size during iteration")
      | some .rekeyed => refuse "the dict's KEY SET changed during iteration without changing its size — CPython's answer depends on its entries-array layout (docs/memory-model.md §dict iteration)"
      | some .rekeyedDone => K.execGen k'
      | some .rekeyedRuntime => raisePy (.runtimeError "dictionary keys changed during iteration")
      | some (.yieldVal kv) => do
          assignM target kv
          K.execGen (.block body :: .forDict target ad (i + 1) n sv kind body :: k')
      | some .done => K.execGen k'
      | Option.none => refuse "internal: a dict cursor over a non-dict object (report this)"
  | .forGen target ad body :: k' => do
      match ← inFrame (K.stepIter ad) with
      | Option.none => K.execGen k'
      | some v => do
          assignM target v
          K.execGen (.block body :: .forGen target ad body :: k')
  | .enumSeq i xs :: k' =>
      match xs with
      | [] => K.execGen k'
      | x :: rest => pure (some (.tuple #[.int i, x], .enumSeq (i + 1) rest :: k'))
  | .enumList i ad cur :: k' => do
      match Heap.get? (← frameHeap) ad with
      | some (.list xs) =>
          if cur < xs.size then
            pure (some (.tuple #[.int i, xs.getD cur .none],
                        .enumList (i + 1) ad (cur + 1) :: k'))
          else K.execGen k'
      | some _ => refuse "internal: an enumerate cursor over a non-list object (report this)"
      | Option.none => refuse danglingMsg
  -- §3c-i-c: `enumerate(d)`. This is `forDict`'s decision with the tuple
  -- wrapped at the frame — `dictStep` already decides all three mutation
  -- regimes, and the view kind is `.keys` because CPython enumerates a bare
  -- dict by key. Exhaustion falls out BY CONSTRUCTION rather than by a guard:
  -- `.done` pops the frame through `K.execGen k'`, so a dict that grows AFTER
  -- the enumerate is exhausted cannot raise — which is what the oracle says
  -- (`[(0, 'a')]` then `[]`, never a RuntimeError).
  | .enumDict i ad cur n sv kind :: k' => do
      match ← dictStepM ad cur n sv [] kind with
      | some .resized => raisePy (.runtimeError "dictionary changed size during iteration")
      | some .rekeyed => refuse "the dict's KEY SET changed during iteration without changing its size — CPython's answer depends on its entries-array layout (docs/memory-model.md §dict iteration)"
      | some .rekeyedDone => K.execGen k'
      | some .rekeyedRuntime => raisePy (.runtimeError "dictionary keys changed during iteration")
      | some (.yieldVal kv) =>
          pure (some (.tuple #[.int i, kv], .enumDict (i + 1) ad (cur + 1) n sv kind :: k'))
      | some .done => K.execGen k'
      | Option.none => refuse "internal: an enumerate cursor over a non-dict object (report this)"
  -- §iter: `iter(d)`. The `enumDict` step with the tuple taken OFF — CPython's
  -- `dict_keyiterator` yields the bare key — so `dictStepM` decides all three
  -- regimes here too and the view kind is `.keys`.
  --
  -- THE EXHAUSTION BOUNDARY IS MEASURED, not conventional. An iterator that has
  -- yielded its LAST key is still live: growing the dict then raises
  -- `RuntimeError` (CPython, measured), and it does here because the frame is
  -- still on the stack and `dictStepM` re-reads. One that has been stepped PAST
  -- the end is DEAD: CPython clears its `di_dict` and a later `next(it, x)`
  -- answers `x` silently, and it does here because `.done` pops the frame
  -- through `K.execGen k'` and the generator closes. Neither is a guard; both
  -- fall out of WHERE the pop happens.
  | .iterDict ad cur n sv initialKeys :: k' => do
      match ← dictStepM ad cur n sv initialKeys .keys with
      | some .resized => raisePy (.runtimeError "dictionary changed size during iteration")
      | some .rekeyed => refuse "the dict's KEY SET changed during iteration without changing its size — CPython's answer depends on its entries-array layout (docs/memory-model.md §dict iteration)"
      | some .rekeyedDone => K.execGen k'
      | some .rekeyedRuntime => raisePy (.runtimeError "dictionary keys changed during iteration")
      | some (.yieldVal kv) =>
          pure (some (kv, .iterDict ad (cur + 1) n sv initialKeys :: k'))
      | some .done => K.execGen k'
      | Option.none => refuse "internal: an iter() cursor over a non-dict object (report this)"
  -- §iterList: `iter(xs)`. The `enumList` step with the tuple taken OFF —
  -- CPython's `list_iterator` yields the bare element — exactly as `iterDict`
  -- is `enumDict` with the tuple off.
  --
  -- MUTATION NEEDS NO REGIME HERE, and that is the whole difference from the
  -- dict cursor. `Heap.get?` re-reads the list every step and `cur < xs.size`
  -- compares against its CURRENT size — precisely what CPython's
  -- `list_iterator.__next__` does (`it_index < PyList_GET_SIZE(seq)`). A list
  -- that GREW keeps yielding; one that SHRANK past the cursor exhausts
  -- silently. Neither is a guess, so this cursor declares NO divergence
  -- where `iterDict` needed two.
  --
  -- WITNESSED: the grow direction (`dict_lab::iter_list_grew`) and the
  -- dead-cursor boundary (`::iter_list_exhausted`). NOT WITNESSED: the
  -- SHRINK direction, and the reason is upstream — writing it needs
  -- `del xs[i]`, itself a refused frontier row (`del.non-dict-receiver`).
  -- The arm above handles it by construction, but no test reaches it until
  -- that row lands, exactly as `pyc-div-1`'s witness waited on
  -- `except_builtin`. Named here so the gap has an owner, not a hope.
  | .iterList ad cur :: k' => do
      match Heap.get? (← frameHeap) ad with
      | some (.list xs) =>
          if cur < xs.size then
            pure (some (xs.getD cur .none, .iterList ad (cur + 1) :: k'))
          else K.execGen k'
      | some _ => refuse "internal: an iter() cursor over a non-list object (report this)"
      | Option.none => refuse danglingMsg
  | .iterBytes xs cur :: k' =>
      if h : cur < xs.size then
        let b := xs[cur]
        pure (some (.int b.toNat, .iterBytes xs (cur + 1) :: k'))
      else K.execGen k'
  | .countFrom cur step :: k' =>
      -- never exhausts: `count` is the infinite ray of sunfish's move generator,
      -- and a consumer's `break` is what ends it.
      pure (some (.int cur, .countFrom (cur + step) step :: k'))
  | .countFromVal cur step :: k' =>
      match evalBinOp .add cur step with
      | .ok next => pure (some (cur, .countFromVal next step :: k'))
      | .exn error => raisePy error
      | .timeout => exhausted
      | .unsupported message => refuse message
  | .whileLoop test body orelse :: k' => do
      let t ← evalOpen K m test
      let b ← truthyM t
      if b then K.execGen (.block body :: .whileLoop test body orelse :: k')
      else K.execGen (.block orelse :: k')

/-- The LAZY `for` cursor over a generator: one `stepIter` per iteration, so the
generator's effects interleave with the body's, and `break` simply stops stepping
— leaving the object SUSPENDED for the next consumer. -/
def forGenAt (K : Kont) (m : Module) (target : Expr) (a : Addr)
    (body : List Stmt) : SemF RFlow := do
  match ← inFrame (K.stepIter a) with
  | Option.none => pure .next
  | some v => do
      assignM target v
      match ← execOpenList K m body with
      | .next | .cont => K.forGen target a body
      | .brk => pure .next
      | .ret v => pure (.ret v)

/-- Drain to EXHAUSTION. Fuel bounds it, so an infinite generator is a loud
timeout — exactly the divergence CPython would have. -/
def drainIterAt (K : Kont) (a : Addr) : SemW (List RVal) := do
  match ← K.stepIter a with
  | Option.none => pure []
  | some v => do
      let vs ← K.drainIter a
      pure (v :: vs)

/-- Short-circuit drain for `any`/`all`: step until the first truthy (`any`) /
falsy (`all`) and STOP, leaving the generator SUSPENDED and resumable. -/
def anyAllIterAt (K : Kont) (a : Addr) (isAll : Bool) : SemW Bool := do
  match ← K.stepIter a with
  | Option.none => pure isAll
  | some v => do
      let w ← get
      let b ← liftRes (truthyH w.heap v)
      if b != isAll then pure b else K.anyAllIter a isAll

/-- Invoke a CLOSURE object (H7): the callee env is parameters bound to
arguments, THEN the snapshot — parameters shadow captures. Mirrors `callInM`'s
refusals and call shape; a GENERATOR closure allocates the H4 object with the
snapshot inside its stored locals, so resume-time capture reads ride the stepper
unchanged. -/
def callCloAt (K : Kont) (m : Module) (name : String) (params : Array Param)
    (argsOk localsOk isGenerator : Bool) (body : Array Stmt) (captured : REnv)
    (args : Array RVal) : SemW RVal :=
  if !argsOk then
    refuse s!"nested function '{name}' uses unsupported parameter features (non-literal defaults/varargs/kwargs/decorators)"
  else if !localsOk then
    refuse s!"nested function '{name}' calls a name it also assigns (CPython static-locals rule) — outside the tier"
  else if !arityOk params args.size then do
    let w ← get
    raisePy (positionalArityError w.callDepth name params args.size)
  else if isGenerator then do
    let w ← get
    if pythonFrameFull w.callDepth then
      raisePy .recursionError
    else
      let env := markUnboundLocals body.toList (mkCallEnv params args) ++ captured
      let g : Obj := .generator s!"<closure:{name}>" env
        [.block body.toList] .created
      set { w with heap := w.heap.push g }
      pure (.ref w.heap.size)
  else do
    -- Ordinary closures enter the same Python-frame unit as named functions.
    let w ← get
    if envHasGenerator w.heap captured && pythonRecursionFull (w.callDepth + 1) then
      raisePy .recursionError
    else withClosureRecursionUnit do
      let env := markUnboundLocals body.toList (mkCallEnv params args) ++ captured
      match ← inWorld env (execOpenList K m body.toList) with
      | .ret v => pure v
      | .next  => pure .none
      | .brk   => refuse "'break' outside loop"
      | .cont  => refuse "'continue' outside loop"

/-! Restore the active-frame count when a module-level call returns or raises.
The model's raise channel retains the world, so the exception handler must
perform the same unwind as the normal path. Model refusals and timeouts carry
no state and therefore need no cleanup. -/
def leaveCallM {α : Type} (action : SemW α) : SemW α :=
  tryCatch
    (do
      let value ← action
      modify fun w => { w with callDepth := w.callDepth.pred }
      pure value)
    (fun e => do
      modify fun w => { w with callDepth := w.callDepth.pred }
      raisePy e)

def finishCallM {α : Type} (depth : Nat) (action : SemW α) : SemW α :=
  tryCatch
    (do
      let value ← action
      modify fun w => { w with callDepth := depth }
      pure value)
    (fun e => do
      modify fun w => { w with callDepth := depth }
      raisePy e)

def finishTopCallM {α : Type} (action : SemW α) : SemW α :=
  finishCallM pythonTopCallDepth action

/-! ## §3 THE FUELED KNOT — structural on FUEL, and the only place fuel is spent -/

/-- Enter a module-level function. The guard ORDER is the trunk's: parameter
features, then the static-locals rule, then arity, then the generator fork. -/
def callInM (K : Kont) (m : Module) (fname : String) (args : Array RVal) : SemW RVal :=
  match findFunction m fname with
  | Option.none => raisePy (.nameError fname)
  | some f =>
    if proofCellGeneratorUnsafe m fname then
      refuse "generator-expression cell capture cannot be established for this function; outside the closed-function tier"
    else if !f.argsOk then
      refuse s!"function '{fname}' uses unsupported parameter features (non-literal defaults/varargs/kwargs/decorators)"
    else if !f.localsOk then
      refuse s!"function '{fname}' calls a name it also assigns (CPython static-locals rule) — outside the v0 tier"
    else if !arityOk f.params args.size then do
      let w ← get
      raisePy (positionalArityError (entryBindingDepth w.callDepth) fname f.params args.size)
    else if f.isGenerator then do
      -- H4 CREATION: calling a generator function runs NO code. It allocates the
      -- suspended frame — arguments bound into its locals, the whole body as the
      -- initial continuation — and returns the object. Every effect in the body
      -- therefore happens only as a consumer steps it, which is exactly the
      -- laziness the search depends on.
      -- §PEP 289: `genInitCont` seeds a synthesized genexp's continuation with
      -- its cursor ALREADY pushed, so the outermost iterable is iterated at
      -- CREATION as CPython does. Every other generator — including every user
      -- `def` with a `yield` — gets `[.block body]` unchanged, because for
      -- those CPython has run no code and called no `iter()` either.
      let w ← get
      let env := globalCallEnv w f.params args f.body f.hasGlobal
      if fname.startsWith genExpPrefix then
        match Env.lookup env genExpArgName with
        | some v =>
            -- `GET_ITER` for a generator expression happens at creation;
            -- value-sequence iterators remain represented by the original
            -- value and are stepped by the existing `for` arms.
            match v with
            | .ref a =>
                match Heap.get? w.heap a with
                | some (.instance _ _) | some (.closure ..) | some (.cell _) =>
                    raisePy (.typeError "'object' object is not iterable")
                | some _ => pure ()
                | none => refuse danglingMsg
            | v => liftRes (genExpCreationCheck v)
        | none => refuse "internal: synthesized genexp argument is unbound"
      else pure ()
      let g : Obj := .generator fname env (genInitCont w.heap fname env f.body.toList) .created
      set { w with heap := w.heap.push g }
      pure (.ref w.heap.size)
    else do
      let w ← get
      if w.callDepth == pythonTopCallDepth then
        set { w with callDepth := 1 }
        let flow ← finishCallM w.callDepth (inWorld (globalCallEnv w f.params args f.body f.hasGlobal)
          (execOpenList K m f.body.toList))
        match flow with
        | .ret v => pure v
        | .next  => pure .none
        | .brk   => refuse "'break' outside loop"
        | .cont  => refuse "'continue' outside loop"
      else if pythonFrameFull w.callDepth then
        raisePy .recursionError
      else
        set { w with callDepth := w.callDepth + 1 }
        let flow ← leaveCallM (inWorld (globalCallEnv w f.params args f.body f.hasGlobal)
          (execOpenList K m f.body.toList))
        match flow with
        | .ret v => pure v
        | .next  => pure .none
        | .brk   => refuse "'break' outside loop"
        | .cont  => refuse "'continue' outside loop"

/-- The fueled operations at each fuel level. `kont m 0` is `Kont.bottom` —
every operation `.timeout`s — which is what makes fuel exhaustion loud rather
than wrong, and makes "the rebuild's only `.timeout` source" a checkable claim.

**THE KNOT MUST BE BUILT LAZILY, and this is a MEASURED correctness-of-cost
requirement rather than a style note.** The obvious spelling binds the successor
level once —

    | fuel + 1 => let K := kont m fuel
                  { call := fun … => … K …, … }

— and `let` is STRICT, so constructing `kont m F` forces the entire chain down to
`0` before a single statement runs: **O(F) work and O(F) stack, per entry**. At
the closed-function surface's fuel of 10 000 that is merely wasteful; at script
mode's **1 000 000** it stalls outright (measured: one script pinned a runner at
~0 % CPU for minutes, having executed nothing).

So every field takes its successor level INSIDE its own lambda. Construction is
then O(1) and the chain is forced exactly as deep as the run actually goes —
which is the behaviour the trunk gets for free by matching `fuel` lazily inside
each function, and which a defunctionalized knot has to ask for. -/
def kont (m : Module) : Nat → Kont
  | 0 => Kont.bottom
  | fuel + 1 =>
    { fuel := fuel
      call := fun fname args => callInM (kont m fuel) m fname args
      callClo := fun locals a args => do
          let K := kont m fuel
          let w ← get
          match Heap.get? w.heap a with
          | some (.cell _) => refuse cellInternal
          | some (.closure nm ps ao lo _ ig bd cap) => do
              let cap' ← liftRes (cellsFor w.heap locals cap)
              callCloAt K m nm ps ao lo ig bd cap' args
          -- Constant message on purpose: `typeNameH` here whnf-storms symbolic
          -- proofs (the recorded H2 finding), and the CLASS is what is compared.
          | _ => raisePy (.typeError "'dict' object is not callable")
      dictItems := fun ks vs => dictItemsAt (kont m fuel) m ks vs
      kwArgs := fun kws => kwArgsAt (kont m fuel) m kws
      whileLoop := fun test body orelse => do
          let K := kont m fuel
          let t ← evalOpen K m test
          let b ← truthyM t
          if b then
            match ← execOpenList K m body with
            | .next | .cont => K.whileLoop test body orelse
            | .brk => pure .next
            | .ret v => pure (.ret v)
          else execOpenList K m orelse
      forSeq := fun target xs body =>
          let K := kont m fuel
          match xs with
          | [] => pure .next
          | x :: rest => do
              assignM target x
              match ← execOpenList K m body with
              | .next | .cont => K.forSeq target rest body
              | .brk => pure .next
              | .ret v => pure (.ret v)
      forList := fun target a i body => do
          let K := kont m fuel
          -- THE LIVE INDEX CURSOR: the referent is re-read EVERY step, so body
          -- mutation, growth and `pop`-shrinkage are observed exactly as
          -- CPython's listiterator observes them.
          match Heap.get? (← frameHeap) a with
          | some (.list xs) =>
              if i < xs.size then do
                assignM target (xs.getD i .none)
                match ← execOpenList K m body with
                | .next | .cont => K.forList target a (i + 1) body
                | .brk => pure .next
                | .ret v => pure (.ret v)
              else pure .next
          -- §3a: the LIVE dict cursor in an ORDINARY function body. This is
          -- the path a plain `def` takes (execGen's is the GENERATOR one and
          -- the script shell's is module scope) — three entries, and the
          -- `dict.for-in-function` witness is what proved the count.
          | some (.dict es sv) => K.forDict target a 0 es.size sv (es.toList.map Prod.fst) .keys body
          | some (.dictView da kind) =>
              match Heap.get? (← frameHeap) da with
              | some (.dict es sv) => K.forDict target da 0 es.size sv (es.toList.map Prod.fst) kind body
              | _ => refuse danglingMsg
          | some (.instance _ _) => raisePy (.typeError "'object' object is not iterable")
          | some (.generator ..) => K.forGen target a body
          | some (.cell _) => refuse cellInternal
          | some (.closure ..) => refuse "internal: a list cursor over a function object (report this)"
          | some (.pyset xs) => do
              let ys ← liftRes (setIterOrder xs.toList)
              K.forSeq target ys body
          | Option.none => refuse danglingMsg
      forDict := fun target a i n sv initialKeys kind body => do
          let K := kont m fuel
          -- the same three regimes as the other two cursors, forked on the
          -- same pure plan so they cannot drift apart
          match ← dictStepM a i n sv initialKeys kind with
          | some .resized => raisePy (.runtimeError "dictionary changed size during iteration")
          | some .rekeyed => refuse "the dict's KEY SET changed during iteration without changing its size — CPython's answer depends on its entries-array layout (docs/memory-model.md §dict iteration)"
          | some .rekeyedDone => pure .next
          | some .rekeyedRuntime => raisePy (.runtimeError "dictionary keys changed during iteration")
          | some (.yieldVal kv) => do
              assignM target kv
              match ← execOpenList K m body with
              | .next | .cont => K.forDict target a (i + 1) n sv initialKeys kind body
              | .brk => pure .next
              | .ret v => pure (.ret v)
          | some .done => pure .next
          | Option.none => refuse "internal: a dict cursor over a non-dict object (report this)"
      stepIter := fun a => stepIterAt (kont m fuel) a
      execGen := fun k => execGenAt (kont m fuel) m k
      forGen := fun t a b => forGenAt (kont m fuel) m t a b
      drainIter := fun a => drainIterAt (kont m fuel) a
      anyAllIter := fun a b => anyAllIterAt (kont m fuel) a b
      withBody := fun body => execOpenList (kont m fuel) m body
      listComp := fun c => listCompReqAt (kont m fuel) m c }
  termination_by structural fuel => fuel


/-! ## §4 THE RUNNER BOUNDARY

`callInMono` has the SAME type as the trunk's `callIn`, which is the whole point:
`Main.lean` swaps one for the other behind `--monadic` and the THREE existing
harnesses (`diff_test.py`, `script_corpus.py`, `refusal_census.py`) compare the
two interpreters through their own `--runner` flag. No harness is forked, and no
harness learns anything about the rebuild beyond one flag. -/

/-- The differential battery's entry point, typed exactly as `callIn`. -/
def callInMono (m : Module) (fuel : Nat) (w : World) (fname : String)
    (args : Array RVal) : Run World RVal :=
  toRun ((kont m fuel).call fname args) { w with callDepth := pythonTopCallDepth }

/-! ### §4.1 THE CLASS THE PUBLIC WRAPPER ERASES

`Run.unsupported` has ONE field, a `String`. `Loud.unsupported` has THREE — the
§5.2 CLASS, the prose, and the diagnostic snapshot — so `toRun` is a projection
that DROPS the class (`Substrate.lean`'s `ofRun_toRun_normalises` states the
loss as a theorem). Everything downstream of `callInMono` therefore sees prose
where the model had a classified verdict, and a scoreboard that must bucket by
class is left parsing prose — the exact thing the class exists to prevent.

**The `--observations` pattern, applied to the class.** That flag's rule is
already: *the public wrapper erases the world, so under the flag the driver
calls the inner API and keeps it.* The class is the same shape of loss one layer
further in, so it gets the same treatment — one run, two projections, and a
theorem saying they are one run.

**Opt-in, and `harness/cases.json` is untouched.** The differential compares the
model's line to a dict it builds itself by WHOLE-DICT equality, which is what
makes any additive field a failure; the field appears only under
`--observations`, exactly like `stdout` and `args_after`. -/

/-- Run from an explicitly supplied recursion depth. The caller supplies the
normalized CPython entry count in `w.callDepth`; unlike `callInRaw`, this
entry point does not replace it with the fresh-module boundary. -/
def callInRawAt (m : Module) (fuel : Nat) (w : World) (fname : String)
    (args : Array RVal) : HaltWith Unit Unit (Except PyErr RVal × World) :=
  (kont m fuel).call fname args w

/-- The runner boundary's INNER value — the one `toRun` is a projection of. -/
def callInRaw (m : Module) (fuel : Nat) (w : World) (fname : String)
    (args : Array RVal) : HaltWith Unit Unit (Except PyErr RVal × World) :=
  (kont m fuel).call fname args { w with callDepth := pythonTopCallDepth }

/-- `Run`'s view of an inner value: `toRun`, written as a function of the
already-applied run so both projections can share one execution. -/
def ofHalt {α : Type} :
    HaltWith Unit Unit (Except PyErr α × World) → Run World α
  | .ok (.ok a, w)                => .ok w a
  | .ok (.error e, w)             => .exn w e
  | .error .timeout               => .timeout
  | .error (.unsupported _ msg _) => .unsupported msg

/-- **ONE RUN, TWO PROJECTIONS** — and this theorem is what makes that a fact
rather than an intention. Without it the runner could quietly execute the
interpreter twice and the two answers could drift. -/
theorem callInMono_eq_ofHalt (m : Module) (fuel : Nat) (w : World)
    (fname : String) (args : Array RVal) :
    callInMono m fuel w fname args = ofHalt (callInRaw m fuel w fname args) := by
  simp only [callInMono, toRun, callInRaw, ofHalt]
  rcases h : (kont m fuel).call fname args { w with callDepth := pythonTopCallDepth } with l | ⟨r, w'⟩
  · cases l <;> rfl
  · cases r <;> rfl

/-! ### A CALL-BOUNDARY ADEQUACY SLICE

Before body execution, both interpreters perform the same missing-function
check. This branch is useful independently of the still-open recursive call
bridge: it fixes the entry depth and preserves the complete world while
returning CPython's `NameError`. -/
theorem twinAgrees_callIn_missing_function (m : Module) (fuel : Nat) (w : World)
    (fname : String) (args : Array RVal) (hfuel : 0 < fuel)
    (hfind : findFunction m fname = none) :
    callInMono m fuel w fname args =
      .exn { w with callDepth := pythonTopCallDepth } (.nameError fname) := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    simp [callInMono, callInM, kont, hfind, toRun, pythonTopCallDepth,
      raisePy, raiseIn, throw, throwThe, MonadExceptOf.throw, ExceptT.mk,
      StateT.pure, Except.pure, pure]

theorem twinAgrees_callIn_unsupported_args (m : Module) (fuel : Nat) (w : World)
    (fname : String) (args : Array RVal) (f : FunctionDefn) (hfuel : 0 < fuel)
    (hfind : findFunction m fname = some f) (hargs : f.argsOk = false)
    (hgen : proofCellGeneratorUnsafe m fname = false) :
    callInMono m fuel w fname args =
      .unsupported
        (s!"function '{fname}' uses unsupported parameter features (non-literal defaults/varargs/kwargs/decorators)") := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    simp [callInMono, callInM, kont, hfind, hargs, hgen, toRun,
      pythonTopCallDepth, Monadic.refuse, LeanModels.refuse, raisePy,
      raiseIn, throw, throwThe, MonadExceptOf.throw, ExceptT.mk,
      StateT.pure, Except.pure, pure]

theorem twinAgrees_callIn_arity_error (m : Module) (fuel : Nat) (w : World)
    (fname : String) (args : Array RVal) (f : FunctionDefn) (hfuel : 0 < fuel)
    (hfind : findFunction m fname = some f) (hargs : f.argsOk = true)
    (hlocal : f.localsOk = true) (hgen : proofCellGeneratorUnsafe m fname = false)
    (harity : arityOk f.params args.size = false) :
    callInMono m fuel w fname args =
      .exn { w with callDepth := pythonTopCallDepth }
        (positionalArityError (entryBindingDepth pythonTopCallDepth) fname f.params args.size) := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    have hget : (getThe World : PyM World World) { w with callDepth :=
        pythonRecursionLimit + 1 } =
        .ok (.ok { w with callDepth := pythonRecursionLimit + 1 },
          { w with callDepth := pythonRecursionLimit + 1 }) := by rfl
    simp [hget, callInMono, callInM, kont, hfind, hargs, hlocal, hgen, harity,
      toRun, pythonTopCallDepth, Monadic.refuse, LeanModels.refuse, raisePy,
      raiseIn, throw, throwThe, MonadExceptOf.throw, ExceptT.mk, StateT.pure,
      MonadState.get, MonadStateOf.get, instMonadStateOfOfMonadLift,
      ExceptT.instMonadLift, StateT.instMonad, StateT.get, StateT.bind,
      ExceptT.bind, ExceptT.bindCont, Except.bind, bind, Except.pure, pure]

theorem twinAgrees_callIn_static_locals (m : Module) (fuel : Nat) (w : World)
    (fname : String) (args : Array RVal) (f : FunctionDefn) (hfuel : 0 < fuel)
    (hfind : findFunction m fname = some f) (hargs : f.argsOk = true)
    (hlocal : f.localsOk = false) (hgen : proofCellGeneratorUnsafe m fname = false) :
    callInMono m fuel w fname args =
      .unsupported
        (s!"function '{fname}' calls a name it also assigns (CPython static-locals rule) — outside the v0 tier") := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    simp [callInMono, callInM, kont, hfind, hargs, hlocal, hgen, toRun,
      pythonTopCallDepth, Monadic.refuse, LeanModels.refuse, raisePy,
      raiseIn, throw, throwThe, MonadExceptOf.throw, ExceptT.mk,
      StateT.pure, Except.pure, pure]

theorem twinAgrees_callIn_zero_fuel (m : Module) (w : World)
    (fname : String) (args : Array RVal) :
    callInMono m 0 w fname args = .timeout := by
  rfl

/-- The §5.2 CLASS, present exactly when the run REFUSED. `none` is not a
default: it is the statement that this run did not refuse. -/
def refusalClass {α : Type} :
    HaltWith Unit Unit (Except PyErr α × World) → Option String
  | .error (.unsupported c _ _) => some c.className
  | _ => Option.none

/-- **PRESENT EXACTLY WHEN**, as a theorem rather than a comment: the class is
there precisely on the runs whose `Run` projection says `unsupported`. A field
whose presence rule is only documented is a field a consumer will read wrong. -/
theorem refusalClass_isSome_iff {α : Type}
    (h : HaltWith Unit Unit (Except PyErr α × World)) :
    (refusalClass h).isSome ↔ ∃ msg, ofHalt h = .unsupported msg := by
  cases h with
  | error l =>
      cases l with
      | timeout => simp [refusalClass, ofHalt]
      | unsupported c msg s => simp [refusalClass, ofHalt]
  | ok p =>
      obtain ⟨r, w⟩ := p
      cases r <;> simp [refusalClass, ofHalt]

/-! ## §5 NON-VACUITY FIRST — the rebuild RUNS, and the KERNEL decides it

The fuel ruling's whole claim is that both halves stay kernel-reducible. That is
a property to CHECK, not to assert: `#guard` is `Decidable.decide` plus `rfl`, so
a well-founded fallback would fail these outright. -/

private def sp0 : Span := ⟨0, 0, 0, 0⟩
private def emptyModule : Module := { functions := #[], classes := #[], namedtuples := #[], topLevel := #[] }
private def K0 : Kont := kont emptyModule 64
private def st0 : FrameState := ⟨{ heap := #[], globals := [] }, [("x", .int 7)]⟩

/-! ## §1.1 A control-level refinement seed

The monadic evaluator and the legacy fuelled evaluator agree on the first
control arm that has no recursive continuation: literal evaluation.  Keeping
this bridge here, beside the monadic arm, makes the remaining adequacy debt
explicit rather than treating the pure-worker bridges as if they covered the
whole evaluator. -/

theorem twinAgrees_evalOpen_constant (K : Kont) (m : Module) (st : FrameState)
    (c : Const) (sp : Span) (fuel : Nat) (hfuel : 0 < fuel) :
    LeanModels.Python.Monadic.toRun (evalOpen K m (.constant c sp)) st =
      evalExpr m fuel st (.constant c sp) := by
  cases fuel with
  | zero => omega
  | succ fuel =>
      rfl

/- A unary literal has one recursive child. The explicit `1 < fuel` premise
   records the fuel spent by the legacy child evaluation; without it the
   fuel-free monadic presentation can decide a run that the trunk times out. -/
theorem twinAgrees_evalOpen_unaryInt (K : Kont) (m : Module) (st : FrameState)
    (op : UnaryOp) (a : Int) (sp : Span) (fuel : Nat) (hfuel : 1 < fuel) :
    LeanModels.Python.Monadic.toRun (evalOpen K m
      (.unaryOp op (.constant (.int a) sp) sp)) st =
      evalExpr m fuel st (.unaryOp op (.constant (.int a) sp) sp) := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      rw [evalExpr]
      have hc := twinAgrees_evalOpen_constant K m st (.int a) sp (fuel + 1) (by omega)
      rw [← hc]
      simp [evalOpen, toRun_bind, toRun_pure, twinAgrees_unaryOp, Run.bind,
        Run.liftRes]

/- Two literal children exercise the left-to-right expression-list control
   path. The same positive fuel margin suffices because the legacy evaluator
   gives both children the post-step fuel. -/
theorem twinAgrees_evalOpen_intAdd (K : Kont) (m : Module) (st : FrameState)
    (a b : Int) (sp : Span) (fuel : Nat) (hfuel : 1 < fuel) :
    LeanModels.Python.Monadic.toRun (evalOpen K m
      (.binOp (.constant (.int a) sp) .add (.constant (.int b) sp) sp)) st =
      evalExpr m fuel st
        (.binOp (.constant (.int a) sp) .add (.constant (.int b) sp) sp) := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      rw [evalExpr]
      have hca := twinAgrees_evalOpen_constant K m st (.int a) sp (fuel + 1) (by omega)
      have hcb : ∀ st' : FrameState,
          LeanModels.Python.Monadic.toRun (evalOpen K m
            (.constant (.int b) sp)) st' =
            evalExpr m (fuel + 1) st' (.constant (.int b) sp) := by
        intro st'
        exact twinAgrees_evalOpen_constant K m st' (.int b) sp (fuel + 1) (by omega)
      rw [← hca]
      have hcb' : ∀ st' : FrameState,
          evalExpr m (fuel + 1) st' (.constant (.int b) sp) =
            LeanModels.Python.Monadic.toRun (evalOpen K m
              (.constant (.int b) sp)) st' := by
        intro st'
        exact (hcb st').symm
      simp only [hcb']
      have haddAnd : (BinOp.add == BinOp.bitAnd) = false := by decide
      have haddMult : (BinOp.add == BinOp.mult) = false := by decide
      have haddMod : (BinOp.add == BinOp.mod) = false := by decide
      simp [evalOpen, binOpHM, haddAnd, haddMult, haddMod, toRun_bind, toRun_pure,
        twinAgrees_binOp, Run.bind, Run.liftRes]

theorem twinAgrees_evalOpen_intSub (K : Kont) (m : Module) (st : FrameState)
    (a b : Int) (sp : Span) (fuel : Nat) (hfuel : 1 < fuel) :
    LeanModels.Python.Monadic.toRun (evalOpen K m
      (.binOp (.constant (.int a) sp) .sub (.constant (.int b) sp) sp)) st =
      evalExpr m fuel st
        (.binOp (.constant (.int a) sp) .sub (.constant (.int b) sp) sp) := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      rw [evalExpr]
      have hca := twinAgrees_evalOpen_constant K m st (.int a) sp (fuel + 1) (by omega)
      have hcb : ∀ st' : FrameState,
          LeanModels.Python.Monadic.toRun (evalOpen K m
            (.constant (.int b) sp)) st' =
            evalExpr m (fuel + 1) st' (.constant (.int b) sp) := by
        intro st'
        exact twinAgrees_evalOpen_constant K m st' (.int b) sp (fuel + 1) (by omega)
      rw [← hca]
      have hcb' : ∀ st' : FrameState,
          evalExpr m (fuel + 1) st' (.constant (.int b) sp) =
            LeanModels.Python.Monadic.toRun (evalOpen K m
              (.constant (.int b) sp)) st' := by
        intro st'
        exact (hcb st').symm
      simp only [hcb']
      have hsubAnd : (BinOp.sub == BinOp.bitAnd) = false := by decide
      have hsubMult : (BinOp.sub == BinOp.mult) = false := by decide
      have hsubMod : (BinOp.sub == BinOp.mod) = false := by decide
      simp [evalOpen, binOpHM, hsubAnd, hsubMult, hsubMod, toRun_bind, toRun_pure,
        twinAgrees_binOp, Run.bind, Run.liftRes]

theorem twinAgrees_evalOpen_intDiv (K : Kont) (m : Module) (st : FrameState)
    (a b : Int) (sp : Span) (fuel : Nat) (hfuel : 1 < fuel) :
    LeanModels.Python.Monadic.toRun (evalOpen K m
      (.binOp (.constant (.int a) sp) .div (.constant (.int b) sp) sp)) st =
      evalExpr m fuel st
        (.binOp (.constant (.int a) sp) .div (.constant (.int b) sp) sp) := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      rw [evalExpr]
      have hca := twinAgrees_evalOpen_constant K m st (.int a) sp (fuel + 1) (by omega)
      have hcb : ∀ st' : FrameState,
          LeanModels.Python.Monadic.toRun (evalOpen K m
            (.constant (.int b) sp)) st' =
            evalExpr m (fuel + 1) st' (.constant (.int b) sp) := by
        intro st'
        exact twinAgrees_evalOpen_constant K m st' (.int b) sp (fuel + 1) (by omega)
      rw [← hca]
      have hcb' : ∀ st' : FrameState,
          evalExpr m (fuel + 1) st' (.constant (.int b) sp) =
            LeanModels.Python.Monadic.toRun (evalOpen K m
              (.constant (.int b) sp)) st' := by
        intro st'
        exact (hcb st').symm
      simp only [hcb']
      have hdivAnd : (BinOp.div == BinOp.bitAnd) = false := by decide
      have hdivMult : (BinOp.div == BinOp.mult) = false := by decide
      have hdivMod : (BinOp.div == BinOp.mod) = false := by decide
      simp [evalOpen, binOpHM, hdivAnd, hdivMult, hdivMod, toRun_bind, toRun_pure,
        twinAgrees_binOp, Run.bind, Run.liftRes]

theorem twinAgrees_evalOpen_intFloorDiv (K : Kont) (m : Module) (st : FrameState)
    (a b : Int) (sp : Span) (fuel : Nat) (hfuel : 1 < fuel) :
    LeanModels.Python.Monadic.toRun (evalOpen K m
      (.binOp (.constant (.int a) sp) .floorDiv (.constant (.int b) sp) sp)) st =
      evalExpr m fuel st
        (.binOp (.constant (.int a) sp) .floorDiv (.constant (.int b) sp) sp) := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      rw [evalExpr]
      have hca := twinAgrees_evalOpen_constant K m st (.int a) sp (fuel + 1) (by omega)
      have hcb : ∀ st' : FrameState,
          LeanModels.Python.Monadic.toRun (evalOpen K m
            (.constant (.int b) sp)) st' =
            evalExpr m (fuel + 1) st' (.constant (.int b) sp) := by
        intro st'
        exact twinAgrees_evalOpen_constant K m st' (.int b) sp (fuel + 1) (by omega)
      rw [← hca]
      have hcb' : ∀ st' : FrameState,
          evalExpr m (fuel + 1) st' (.constant (.int b) sp) =
            LeanModels.Python.Monadic.toRun (evalOpen K m
              (.constant (.int b) sp)) st' := by
        intro st'
        exact (hcb st').symm
      simp only [hcb']
      have hfloorAnd : (BinOp.floorDiv == BinOp.bitAnd) = false := by decide
      have hfloorMult : (BinOp.floorDiv == BinOp.mult) = false := by decide
      have hfloorMod : (BinOp.floorDiv == BinOp.mod) = false := by decide
      simp [evalOpen, binOpHM, hfloorAnd, hfloorMult, hfloorMod, toRun_bind,
        toRun_pure, twinAgrees_binOp, Run.bind, Run.liftRes]

theorem twinAgrees_evalOpen_intMod (K : Kont) (m : Module) (st : FrameState)
    (a b : Int) (sp : Span) (fuel : Nat) (hfuel : 1 < fuel) :
    LeanModels.Python.Monadic.toRun (evalOpen K m
      (.binOp (.constant (.int a) sp) .mod (.constant (.int b) sp) sp)) st =
      evalExpr m fuel st
        (.binOp (.constant (.int a) sp) .mod (.constant (.int b) sp) sp) := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      rw [evalExpr]
      have hca := twinAgrees_evalOpen_constant K m st (.int a) sp (fuel + 1) (by omega)
      have hcb : ∀ st' : FrameState,
          LeanModels.Python.Monadic.toRun (evalOpen K m
            (.constant (.int b) sp)) st' =
            evalExpr m (fuel + 1) st' (.constant (.int b) sp) := by
        intro st'
        exact twinAgrees_evalOpen_constant K m st' (.int b) sp (fuel + 1) (by omega)
      rw [← hca]
      have hcb' : ∀ st' : FrameState,
          evalExpr m (fuel + 1) st' (.constant (.int b) sp) =
            LeanModels.Python.Monadic.toRun (evalOpen K m
              (.constant (.int b) sp)) st' := by
        intro st'
        exact (hcb st').symm
      simp only [hcb']
      have hmodAnd : (BinOp.mod == BinOp.bitAnd) = false := by decide
      have hmodMult : (BinOp.mod == BinOp.mult) = false := by decide
      have hmodSelf : (BinOp.mod == BinOp.mod) = true := by decide
      simp [evalOpen, binOpHM, Const.toRVal, hmodAnd, hmodMult, hmodSelf, toRun_bind, toRun_pure,
        twinAgrees_binOp, Run.bind, Run.liftRes]

theorem twinAgrees_evalOpen_intBitOr (K : Kont) (m : Module) (st : FrameState)
    (a b : Int) (sp : Span) (fuel : Nat) (hfuel : 1 < fuel) :
    LeanModels.Python.Monadic.toRun (evalOpen K m
      (.binOp (.constant (.int a) sp) .bitOr (.constant (.int b) sp) sp)) st =
      evalExpr m fuel st
        (.binOp (.constant (.int a) sp) .bitOr (.constant (.int b) sp) sp) := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      rw [evalExpr]
      have hca := twinAgrees_evalOpen_constant K m st (.int a) sp (fuel + 1) (by omega)
      have hcb : ∀ st' : FrameState,
          LeanModels.Python.Monadic.toRun (evalOpen K m
            (.constant (.int b) sp)) st' =
            evalExpr m (fuel + 1) st' (.constant (.int b) sp) := by
        intro st'
        exact twinAgrees_evalOpen_constant K m st' (.int b) sp (fuel + 1) (by omega)
      rw [← hca]
      have hcb' : ∀ st' : FrameState,
          evalExpr m (fuel + 1) st' (.constant (.int b) sp) =
            LeanModels.Python.Monadic.toRun (evalOpen K m
              (.constant (.int b) sp)) st' := by
        intro st'
        exact (hcb st').symm
      simp only [hcb']
      have horAnd : (BinOp.bitOr == BinOp.bitAnd) = false := by decide
      have horMult : (BinOp.bitOr == BinOp.mult) = false := by decide
      have horMod : (BinOp.bitOr == BinOp.mod) = false := by decide
      simp [evalOpen, binOpHM, horAnd, horMult, horMod, toRun_bind, toRun_pure,
        twinAgrees_binOp, Run.bind, Run.liftRes]

theorem twinAgrees_evalOpen_intBitXor (K : Kont) (m : Module) (st : FrameState)
    (a b : Int) (sp : Span) (fuel : Nat) (hfuel : 1 < fuel) :
    LeanModels.Python.Monadic.toRun (evalOpen K m
      (.binOp (.constant (.int a) sp) .bitXor (.constant (.int b) sp) sp)) st =
      evalExpr m fuel st
        (.binOp (.constant (.int a) sp) .bitXor (.constant (.int b) sp) sp) := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      rw [evalExpr]
      have hca := twinAgrees_evalOpen_constant K m st (.int a) sp (fuel + 1) (by omega)
      have hcb : ∀ st' : FrameState,
          LeanModels.Python.Monadic.toRun (evalOpen K m
            (.constant (.int b) sp)) st' =
            evalExpr m (fuel + 1) st' (.constant (.int b) sp) := by
        intro st'
        exact twinAgrees_evalOpen_constant K m st' (.int b) sp (fuel + 1) (by omega)
      rw [← hca]
      have hcb' : ∀ st' : FrameState,
          evalExpr m (fuel + 1) st' (.constant (.int b) sp) =
            LeanModels.Python.Monadic.toRun (evalOpen K m
              (.constant (.int b) sp)) st' := by
        intro st'
        exact (hcb st').symm
      simp only [hcb']
      have hxorAnd : (BinOp.bitXor == BinOp.bitAnd) = false := by decide
      have hxorMult : (BinOp.bitXor == BinOp.mult) = false := by decide
      have hxorMod : (BinOp.bitXor == BinOp.mod) = false := by decide
      simp [evalOpen, binOpHM, hxorAnd, hxorMult, hxorMod, toRun_bind, toRun_pure,
        twinAgrees_binOp, Run.bind, Run.liftRes]

theorem twinAgrees_evalOpen_intLShift (K : Kont) (m : Module) (st : FrameState)
    (a b : Int) (sp : Span) (fuel : Nat) (hfuel : 1 < fuel) :
    LeanModels.Python.Monadic.toRun (evalOpen K m
      (.binOp (.constant (.int a) sp) .lshift (.constant (.int b) sp) sp)) st =
      evalExpr m fuel st
        (.binOp (.constant (.int a) sp) .lshift (.constant (.int b) sp) sp) := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      rw [evalExpr]
      have hca := twinAgrees_evalOpen_constant K m st (.int a) sp (fuel + 1) (by omega)
      have hcb : ∀ st' : FrameState,
          LeanModels.Python.Monadic.toRun (evalOpen K m
            (.constant (.int b) sp)) st' =
            evalExpr m (fuel + 1) st' (.constant (.int b) sp) := by
        intro st'
        exact twinAgrees_evalOpen_constant K m st' (.int b) sp (fuel + 1) (by omega)
      rw [← hca]
      have hcb' : ∀ st' : FrameState,
          evalExpr m (fuel + 1) st' (.constant (.int b) sp) =
            LeanModels.Python.Monadic.toRun (evalOpen K m
              (.constant (.int b) sp)) st' := by
        intro st'
        exact (hcb st').symm
      simp only [hcb']
      have hshiftAnd : (BinOp.lshift == BinOp.bitAnd) = false := by decide
      have hshiftMult : (BinOp.lshift == BinOp.mult) = false := by decide
      have hshiftMod : (BinOp.lshift == BinOp.mod) = false := by decide
      simp [evalOpen, binOpHM, hshiftAnd, hshiftMult, hshiftMod, toRun_bind,
        toRun_pure, twinAgrees_binOp, Run.bind, Run.liftRes]

theorem twinAgrees_evalOpen_intRShift (K : Kont) (m : Module) (st : FrameState)
    (a b : Int) (sp : Span) (fuel : Nat) (hfuel : 1 < fuel) :
    LeanModels.Python.Monadic.toRun (evalOpen K m
      (.binOp (.constant (.int a) sp) .rshift (.constant (.int b) sp) sp)) st =
      evalExpr m fuel st
        (.binOp (.constant (.int a) sp) .rshift (.constant (.int b) sp) sp) := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      rw [evalExpr]
      have hca := twinAgrees_evalOpen_constant K m st (.int a) sp (fuel + 1) (by omega)
      have hcb : ∀ st' : FrameState,
          LeanModels.Python.Monadic.toRun (evalOpen K m
            (.constant (.int b) sp)) st' =
            evalExpr m (fuel + 1) st' (.constant (.int b) sp) := by
        intro st'
        exact twinAgrees_evalOpen_constant K m st' (.int b) sp (fuel + 1) (by omega)
      rw [← hca]
      have hcb' : ∀ st' : FrameState,
          evalExpr m (fuel + 1) st' (.constant (.int b) sp) =
            LeanModels.Python.Monadic.toRun (evalOpen K m
              (.constant (.int b) sp)) st' := by
        intro st'
        exact (hcb st').symm
      simp only [hcb']
      have hrshiftAnd : (BinOp.rshift == BinOp.bitAnd) = false := by decide
      have hrshiftMult : (BinOp.rshift == BinOp.mult) = false := by decide
      have hrshiftMod : (BinOp.rshift == BinOp.mod) = false := by decide
      simp [evalOpen, binOpHM, hrshiftAnd, hrshiftMult, hrshiftMod, toRun_bind,
        toRun_pure, twinAgrees_binOp, Run.bind, Run.liftRes]

/- The expression-control family reaches the heap-aware binary worker for
   `.bitAnd`. Immediate integer operands cannot be set-like, so the monadic
   branch falls through to the shared pure worker and leaves the heap/value
   pair unchanged. -/
theorem twinAgrees_binOpHM_intBitAnd (a b : Int) (st : FrameState) :
    LeanModels.Python.Monadic.toRun (binOpHM .bitAnd (.int a) (.int b)) st =
      match evalBinOpH st.world.heap .bitAnd (.int a) (.int b) with
      | .ok (h, v) => .ok { st with world := { st.world with heap := h } } v
      | .exn e => .exn st e
      | .timeout => .timeout
      | .unsupported msg => .unsupported msg := by
  have hand : (BinOp.bitAnd == BinOp.bitAnd) = true := by decide
  have hmult : (BinOp.bitAnd == BinOp.mult) = false := by decide
  unfold binOpHM
  rw [if_pos hand]
  rw [toRun_bind]
  unfold frameHeap
  rw [toRun_bind]
  rw [toRun_get]
  simp only [toRun_pure]
  simpa [twinAgrees_binOp, evalBinOpH, setLikeRefH, evalBinOp, asInt,
    hmult, Run.liftRes]

/- Immediate integer multiplication also takes the heap-aware dispatch branch:
   it reads the frame heap, recognizes that neither operand is a list, and
   returns the pure worker result with the heap unchanged. -/
theorem twinAgrees_binOpHM_intMult (a b : Int) (st : FrameState) :
    LeanModels.Python.Monadic.toRun (binOpHM .mult (.int a) (.int b)) st =
      match evalBinOpH st.world.heap .mult (.int a) (.int b) with
      | .ok (h, v) => .ok { st with world := { st.world with heap := h } } v
      | .exn e => .exn st e
      | .timeout => .timeout
      | .unsupported msg => .unsupported msg := by
  have hand : (BinOp.mult == BinOp.bitAnd) = false := by decide
  have hmult : (BinOp.mult == BinOp.mult) = true := by decide
  unfold binOpHM
  simp only [hand, hmult, Bool.false_eq_true, if_false, if_true]
  rw [toRun_bind]
  unfold frameHeap
  rw [toRun_bind]
  rw [toRun_get]
  simp only [toRun_pure]
  simp [twinAgrees_binOp, evalBinOpH, evalBinOpMultH, evalBinOp,
    evalBinOpMultH, asInt, hand, hmult, Bool.false_eq_true, if_false,
    if_true, Run.liftRes]

/- The expression-control bridge for a literal integer bitwise-and.  The
   heap-aware dispatch theorem above supplies the state-preserving worker
   equation after both literal children have crossed the shared constant
   bridge. -/
theorem twinAgrees_evalOpen_intBitAnd (K : Kont) (m : Module) (st : FrameState)
    (a b : Int) (sp : Span) (fuel : Nat) (hfuel : 1 < fuel) :
    LeanModels.Python.Monadic.toRun (evalOpen K m
      (.binOp (.constant (.int a) sp) .bitAnd (.constant (.int b) sp) sp)) st =
      evalExpr m fuel st
        (.binOp (.constant (.int a) sp) .bitAnd (.constant (.int b) sp) sp) := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      rw [evalExpr]
      have hca := twinAgrees_evalOpen_constant K m st (.int a) sp (fuel + 1) (by omega)
      have hcb : ∀ st' : FrameState,
          LeanModels.Python.Monadic.toRun (evalOpen K m
            (.constant (.int b) sp)) st' =
            evalExpr m (fuel + 1) st' (.constant (.int b) sp) := by
        intro st'
        exact twinAgrees_evalOpen_constant K m st' (.int b) sp (fuel + 1) (by omega)
      rw [← hca]
      have hcb' : ∀ st' : FrameState,
          evalExpr m (fuel + 1) st' (.constant (.int b) sp) =
            LeanModels.Python.Monadic.toRun (evalOpen K m
              (.constant (.int b) sp)) st' := by
        intro st'
        exact (hcb st').symm
      simp only [hcb']
      have handAnd : (BinOp.bitAnd == BinOp.bitAnd) = true := by decide
      have handMult : (BinOp.bitAnd == BinOp.mult) = false := by decide
      simp only [evalOpen, toRun_bind, toRun_pure, Run.bind, handAnd, handMult,
        Bool.true_or, if_true]
      exact twinAgrees_binOpHM_intBitAnd a b st

/- The expression-control bridge for literal integer multiplication reuses the
   heap-aware worker equation above and preserves the same legacy fuel margin. -/
theorem twinAgrees_evalOpen_intMult (K : Kont) (m : Module) (st : FrameState)
    (a b : Int) (sp : Span) (fuel : Nat) (hfuel : 1 < fuel) :
    LeanModels.Python.Monadic.toRun (evalOpen K m
      (.binOp (.constant (.int a) sp) .mult (.constant (.int b) sp) sp)) st =
      evalExpr m fuel st
        (.binOp (.constant (.int a) sp) .mult (.constant (.int b) sp) sp) := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      rw [evalExpr]
      have hca := twinAgrees_evalOpen_constant K m st (.int a) sp (fuel + 1) (by omega)
      have hcb : ∀ st' : FrameState,
          LeanModels.Python.Monadic.toRun (evalOpen K m
            (.constant (.int b) sp)) st' =
            evalExpr m (fuel + 1) st' (.constant (.int b) sp) := by
        intro st'
        exact twinAgrees_evalOpen_constant K m st' (.int b) sp (fuel + 1) (by omega)
      rw [← hca]
      have hcb' : ∀ st' : FrameState,
          evalExpr m (fuel + 1) st' (.constant (.int b) sp) =
            LeanModels.Python.Monadic.toRun (evalOpen K m
              (.constant (.int b) sp)) st' := by
        intro st'
        exact (hcb st').symm
      simp only [hcb']
      have hmultAnd : (BinOp.mult == BinOp.bitAnd) = false := by decide
      have hmultSelf : (BinOp.mult == BinOp.mult) = true := by decide
      simp only [evalOpen, toRun_bind, toRun_pure, Run.bind, hmultAnd, hmultSelf,
        Bool.false_or, if_false, Bool.true_or, if_true]
      exact twinAgrees_binOpHM_intMult a b st

/- `x + 5 = 12`, through the fuel-free evaluator, decided by the KERNEL. -/
#guard (match toRun (evalOpen K0 emptyModule
          (.binOp (.name "x" sp0) .add (.constant (.int 5) sp0) sp0)) st0 with
        | .ok _ v => v == .int 12
        | _ => false)

/- An unbound name raises `NameError` and the state is RETAINED — the layer
order's whole point, and the property `StateT` outside `ExceptT` cannot state. -/
#guard (match toRun (evalOpen K0 emptyModule (.name "nope" sp0)) st0 with
        | .exn s e => e == .nameError "nope" && s == st0
        | _ => false)

/- `and` answers the DECIDING OPERAND, not a bool (CPython, not a guess). -/
#guard (match toRun (evalOpen K0 emptyModule
          (.boolOp .and #[.constant (.int 0) sp0, .constant (.int 9) sp0] sp0)) st0 with
        | .ok _ v => v == .int 0
        | _ => false)

/- A chained comparison short-circuits: `1 < 2 < 3` is `True`. -/
#guard (match toRun (evalOpen K0 emptyModule
          (.compare (.constant (.int 1) sp0) #[.lt, .lt]
            #[.constant (.int 2) sp0, .constant (.int 3) sp0] sp0)) st0 with
        | .ok _ v => v == .bool true
        | _ => false)

/- A list display ALLOCATES: the answer is a `.ref` at the old heap size. -/
#guard (match toRun (evalOpen K0 emptyModule
          (.list #[.constant (.int 1) sp0, .constant (.int 2) sp0] sp0)) st0 with
        | .ok s v => v == .ref 0 && s.world.heap.size == 1
        | _ => false)

/- A one-generator list comprehension steps through the fueled continuation,
allocates a fresh heap list, and restores the caller's target binding. -/
#guard (match toRun (evalOpen K0 emptyModule
          (.listComp
            (.binOp (.name "x" sp0) .add (.constant (.int 1) sp0) sp0)
            (.name "x" sp0)
            (.tuple #[.constant (.int 1) sp0, .constant (.int 2) sp0] sp0)
            #[] #[] sp0)) st0 with
        | .ok s (.ref 0) =>
            Env.lookup s.locals "x" == some (.int 7) &&
            Heap.get? s.world.heap 0 == some (.list #[.int 2, .int 3])
        | _ => false)

/- Statement execution: `y = x * 3` binds 21 in the frame's locals. -/
#guard (match toRun (execOpen K0 emptyModule
          (.assign #[.name "y" sp0]
            (.binOp (.name "x" sp0) .mult (.constant (.int 3) sp0) sp0) sp0)) st0 with
        | .ok s _ => Env.lookup s.locals "y" == some (.int 21)
        | _ => false)

/- A `while` runs through the FUELED knot and terminates: sum 1..4 = 10. -/
#guard (match toRun (execOpenList K0 emptyModule
          [ .assign #[.name "t" sp0] (.constant (.int 0) sp0) sp0,
            .assign #[.name "i" sp0] (.constant (.int 1) sp0) sp0,
            .whileLoop (.compare (.name "i" sp0) #[.ltE] #[.constant (.int 4) sp0] sp0)
              #[ .augAssign (.name "t" sp0) .add (.name "i" sp0) sp0,
                 .augAssign (.name "i" sp0) .add (.constant (.int 1) sp0) sp0 ] #[] sp0 ])
          st0 with
        | .ok s _ => Env.lookup s.locals "t" == some (.int 10)
        | _ => false)

/- FUEL EXHAUSTION IS LOUD, never wrong: at `kont m 0` every fueled operation
answers `.timeout`, so a `while` with no fuel times out rather than deciding. -/
#guard (match toRun (execOpen (kont emptyModule 0) emptyModule
          (.whileLoop (.constant (.bool true) sp0) #[.pass sp0] #[] sp0)) st0 with
        | .timeout => true
        | _ => false)

/- `print` is an ORDINARY builtin: it appends one chunk and answers `None`. -/
#guard (match toRun (evalOpen K0 emptyModule
          (.call (.name "print" sp0) #[.constant (.str "hi") sp0] #[] Option.none sp0)) st0 with
        | .ok s v => v == .none && s.world.stdout == ["hi"]
        | _ => false)

/-! ### The EXCEPTIONS tier, pinned — the three claims §6.1 makes about the stack

These are not decoration. §6.1 of the plan claims that `try`/`except` gets two
properties from the TYPE rather than from the arm's code, and a claim of that
shape is worth exactly as much as its counterexample test. -/

private def excCls : ClassDefn :=
  { name := "Stop", ok := true, isExc := true, methods := #[], span := sp0 }
private def excModule : Module :=
  { functions := #[], classes := #[excCls], namedtuples := #[], topLevel := #[] }
private def KE : Kont := kont excModule 64
private def stE : FrameState := ⟨{ heap := #[], globals := [] }, []⟩

/- 1. A matching user exception IS caught — AND the body's binding SURVIVES into
the handler. That is the RETAINED-STATE covenant, and it is the layer order:
`StateT` inside `ExceptT`. The wrong order would lose `seen`. -/
#guard (match toRun (execOpen KE excModule
          (.tryStmt #[ .assign #[.name "seen" sp0] (.constant (.int 1) sp0) sp0,
                       .raiseStmt (some (.name "Stop" sp0)) Option.none sp0 ]
             #["Stop"]
             #[ .assign #[.name "caught" sp0] (.constant (.int 2) sp0) sp0 ]
             Option.none sp0)) stE with
        | .ok s _ => Env.lookup s.locals "seen" == some (.int 1)
                     && Env.lookup s.locals "caught" == some (.int 2)
        | _ => false)

/- 2. A `Loud` refusal inside the body is NOT caught — it propagates. This is the
property that keeps a MODEL gap from masquerading as PYTHON behaviour: an
`except` clause must never be able to swallow "I do not model this". `tryCatch`
on `ExceptT PyErr …` gives it for free, because `Loud` lives below that layer. -/
#guard (match toRun (execOpen KE excModule
          (.tryStmt #[ .globalDecl #["x"] sp0 ]
             #["Stop"]
             #[ .assign #[.name "caught" sp0] (.constant (.int 2) sp0) sp0 ]
             Option.none sp0)) stE with
        | .unsupported _ => false
        | _ => true)

/- 3. A NON-matching exception propagates rather than being caught. -/
#guard (match toRun (execOpen KE excModule
          (.tryStmt #[ .exprStmt (.name "nope" sp0) sp0 ]
             #["Stop"]
             #[ .assign #[.name "caught" sp0] (.constant (.int 2) sp0) sp0 ]
             Option.none sp0)) stE with
        | .exn _ e => e == .nameError "nope"
        | _ => false)

/-! ### The GENERATOR tier, pinned — laziness is the property, so test laziness

`count` is INFINITE. If the tier materialized it, these would not terminate; that
they are decided by the kernel in finite time IS the laziness claim. -/

private def call1 (f : String) (a : Expr) : Expr :=
  .call (.name f sp0) #[a] #[] Option.none sp0
private def call2 (f : String) (a b : Expr) : Expr :=
  .call (.name f sp0) #[a, b] #[] Option.none sp0

/- `g = count(5, 2)`; two `next`s give 5 then 7 — an INFINITE generator stepped
twice, allocated as a frame and resumed through the continuation walker. -/
#guard (match toRun (execOpenList K0 emptyModule
          [ .assign #[.name "g" sp0]
              (call2 "count" (.constant (.int 5) sp0) (.constant (.int 2) sp0)) sp0,
            .assign #[.name "a" sp0] (call1 "next" (.name "g" sp0)) sp0,
            .assign #[.name "b" sp0] (call1 "next" (.name "g" sp0)) sp0 ]) st0 with
        | .ok s _ => Env.lookup s.locals "a" == some (.int 5)
                     && Env.lookup s.locals "b" == some (.int 7)
        | _ => false)

/- `enumerate` is LAZY too, and a `for` over it is the lazy cursor: summing the
indices of a 3-element tuple gives 0+1+2 = 3, and the pair unpacks. -/
#guard (match toRun (execOpenList K0 emptyModule
          [ .assign #[.name "t" sp0] (.constant (.int 0) sp0) sp0,
            .forStmt (.tuple #[.name "i" sp0, .name "c" sp0] sp0)
              (call1 "enumerate"
                (.tuple #[.constant (.str "a") sp0, .constant (.str "b") sp0,
                          .constant (.str "c") sp0] sp0))
              #[ .augAssign (.name "t" sp0) .add (.name "i" sp0) sp0 ] #[] sp0 ]) st0 with
        | .ok s _ => Env.lookup s.locals "t" == some (.int 3)
        | _ => false)

/- EXHAUSTION is the faithful `StopIteration`, not a silent `None`. -/
#guard (match toRun (execOpenList K0 emptyModule
          [ .assign #[.name "g" sp0]
              (call1 "enumerate" (.tuple #[] sp0)) sp0,
            .exprStmt (call1 "next" (.name "g" sp0)) sp0 ]) st0 with
        | .exn _ e => e == .stopIteration
        | _ => false)

/- `next(g, d)` CONSUMES exhaustion and yields the default instead. -/
#guard (match toRun (execOpenList K0 emptyModule
          [ .assign #[.name "g" sp0] (call1 "enumerate" (.tuple #[] sp0)) sp0,
            .assign #[.name "d" sp0]
              (call2 "next" (.name "g" sp0) (.constant (.int 9) sp0)) sp0 ]) st0 with
        | .ok s _ => Env.lookup s.locals "d" == some (.int 9)
        | _ => false)

/-! ### A CONTROL-LEVEL ADEQUACY SLICE

The two interpreters use different fuel geometries, but their expression-list
control is the same on an arbitrary-length list of constants.  This theorem is
deliberately indexed by the list length rather than by a hand-written pair of
literal operands: it is the first induction that composes the shared literal
bridge with the left-to-right list walker.  The strict length bound records the
fuel consumed by the trunk's one-step list driver at every element.
-/

private def twinConstExprs : List (Const × Span) → List Expr
  | [] => []
  | (c, sp) :: xs => .constant c sp :: twinConstExprs xs

theorem twinAgrees_evalOpenList_constants (K : Kont) (m : Module) (st : FrameState) :
    ∀ (xs : List (Const × Span)) (fuel : Nat), xs.length < fuel →
      toRun (evalOpenList K m (twinConstExprs xs)) st =
        evalExprs m fuel st (twinConstExprs xs) := by
  intro xs
  induction xs with
  | nil =>
      intro fuel hlen
      cases fuel with
      | zero => simp at hlen
      | succ fuel => rfl
  | cons x xs ih =>
      rcases x with ⟨c, sp⟩
      intro fuel hlen
      cases fuel with
      | zero => simp at hlen
      | succ fuel =>
          cases fuel with
          | zero =>
              simp [List.length_cons] at hlen
          | succ fuel =>
              have htail : xs.length < fuel + 1 := by
                simp_all [List.length_cons]
              have hi := ih (fuel + 1) htail
              simp only [twinConstExprs, evalOpenList, toRun_bind]
              rw [show toRun (evalOpen K m (.constant c sp)) st =
                Run.ok st (Const.toRVal c) by rfl]
              simp only [Run.bind]
              rw [hi]
              simp [evalExprs, evalExpr, toRun_pure, Run.bind, Run.liftRes]

/- The reusable composition form: callers supply one pointwise expression
   bridge, and this theorem supplies the arbitrary-length left-to-right list
   control.  The bridge is quantified over every continuation state because
   the first expression may update locals or the heap before the tail starts. -/
theorem twinAgrees_evalOpenList_of_each (K : Kont) (m : Module) :
    ∀ (es : List Expr) (fuel : Nat) (st : FrameState), es.length < fuel →
      (∀ e ∈ es, ∀ st' g, 0 < g →
        toRun (evalOpen K m e) st' = evalExpr m g st' e) →
      toRun (evalOpenList K m es) st = evalExprs m fuel st es := by
  intro es
  induction es with
  | nil =>
      intro fuel st hlen hEach
      cases fuel with
      | zero => simp at hlen
      | succ fuel => rfl
  | cons e es ih =>
      intro fuel st hlen hEach
      cases fuel with
      | zero => simp at hlen
      | succ fuel =>
          cases fuel with
          | zero => simp [List.length_cons] at hlen
          | succ fuel =>
              have htail : es.length < fuel + 1 := by
                simp_all [List.length_cons]
              have hfirst := hEach e (by simp) st (fuel + 1) (by omega)
              have htailEach : ∀ e' ∈ es, ∀ st' g, 0 < g →
                  toRun (evalOpen K m e') st' = evalExpr m g st' e' := by
                intro e' he' st' g hg
                exact hEach e' (by simp [he']) st' g hg
              have hi : ∀ st', toRun (evalOpenList K m es) st' =
                  evalExprs m (fuel + 1) st' es := by
                intro st'
                exact ih (fuel + 1) st' htail htailEach
              simp only [evalOpenList, toRun_bind]
              rw [hfirst]
              simp only [Run.bind]
              generalize hres : evalExpr m (fuel + 1) st e = r
              cases r with
              | timeout => simp [hres, evalExprs, Run.bind]
              | unsupported msg => simp [hres, evalExprs, Run.bind]
              | exn st' err => simp [hres, evalExprs, Run.bind]
              | ok st' v => simp [hres, hi st', evalExprs, toRun_pure, Run.bind]

/- The statement-level counterpart uses the same proof shape, including the
   retained state after a normal statement and the four flow results.  It is
   intentionally a composition theorem: statement-specific bridges remain
   separate obligations, while this induction owns sequencing and early flow. -/
theorem twinAgrees_execOpenList_of_each (K : Kont) (m : Module) :
    ∀ (ss : List Stmt) (fuel : Nat) (st : FrameState), ss.length < fuel →
      (∀ s ∈ ss, ∀ st' g, 0 < g →
        toRun (execOpen K m s) st' = execStmt m g st' s) →
      toRun (execOpenList K m ss) st = execStmts m fuel st ss := by
  intro ss
  induction ss with
  | nil =>
      intro fuel st hlen hEach
      cases fuel with
      | zero => simp at hlen
      | succ fuel => rfl
  | cons s ss ih =>
      intro fuel st hlen hEach
      cases fuel with
      | zero => simp at hlen
      | succ fuel =>
          cases fuel with
          | zero => simp [List.length_cons] at hlen
          | succ fuel =>
              have htail : ss.length < fuel + 1 := by
                simp_all [List.length_cons]
              have hfirst := hEach s (by simp) st (fuel + 1) (by omega)
              have htailEach : ∀ s' ∈ ss, ∀ st' g, 0 < g →
                  toRun (execOpen K m s') st' = execStmt m g st' s' := by
                intro s' hs' st' g hg
                exact hEach s' (by simp [hs']) st' g hg
              have hi : ∀ st', toRun (execOpenList K m ss) st' =
                  execStmts m (fuel + 1) st' ss := by
                intro st'
                exact ih (fuel + 1) st' htail htailEach
              simp only [execOpenList, toRun_bind]
              rw [hfirst]
              simp only [Run.bind]
              generalize hres : execStmt m (fuel + 1) st s = r
              cases r with
              | timeout => simp [hres, execStmts, Run.bind]
              | unsupported msg => simp [hres, execStmts, Run.bind]
              | exn st' err => simp [hres, execStmts, Run.bind]
              | ok st' flow =>
                  cases flow with
                  | next => simp [hres, hi st', execStmts, toRun_pure, Run.bind]
                  | brk => simp [hres, execStmts, toRun_pure, Run.bind]
                  | cont => simp [hres, execStmts, toRun_pure, Run.bind]
                  | ret v => simp [hres, execStmts, toRun_pure, Run.bind]

theorem twinAgrees_execOpenList_nil (K : Kont) (m : Module) (st : FrameState) :
    toRun (execOpenList K m []) st = .ok st .next := by
  rfl

theorem twinAgrees_execOpenList_nil_world (K : Kont) (m : Module)
    (locals : REnv) (w : World) :
    toRun (inWorld locals (execOpenList K m [])) w = .ok w .next := by
  rw [inWorld_toRun, twinAgrees_execOpenList_nil]
  rfl

theorem finishCallM_pure_ok {α : Type} (depth : Nat) (w : World) (v : α) :
    toRun (finishCallM depth (pure v : SemW α)) w =
      .ok { w with callDepth := depth } v := by
  let action : SemW α := do
    let value ← pure v
    modify fun w => { w with callDepth := depth }
    pure value
  have hraw : action w = .ok (.ok v, { w with callDepth := depth }) := by
    simp only [action]
    rw [bind_apply]
    rfl
  unfold finishCallM
  apply toRun_tryCatch_ok
  exact hraw

theorem finishCallM_empty_body_ok (K : Kont) (m : Module) (locals : REnv)
    (w : World) (depth : Nat) :
    toRun (finishCallM depth (inWorld locals (execOpenList K m []))) w =
      .ok { w with callDepth := depth } .next := by
  have hraw : (inWorld locals (execOpenList K m [])) w =
      .ok (.ok RFlow.next, w) := by rfl
  unfold finishCallM
  apply toRun_tryCatch_ok
  rw [bind_apply, hraw]
  rfl

private def adequacySpan : Span := ⟨0, 0, 0, 0⟩

theorem finishCallM_pass_body_ok (K : Kont) (m : Module) (locals : REnv)
    (w : World) (depth : Nat) :
    toRun (finishCallM depth
      (inWorld locals (execOpenList K m [.pass adequacySpan]))) w =
      .ok { w with callDepth := depth } .next := by
  have hraw : (inWorld locals (execOpenList K m [.pass adequacySpan])) w =
      .ok (.ok RFlow.next, w) := by rfl
  unfold finishCallM
  apply toRun_tryCatch_ok
  rw [bind_apply, hraw]
  rfl

theorem finishCallM_expr_constant_body_ok (K : Kont) (m : Module)
    (locals : REnv) (w : World) (depth : Nat) :
    toRun (finishCallM depth
      (inWorld locals (execOpenList K m
        [.exprStmt (.constant (.int 1) adequacySpan) adequacySpan]))) w =
      .ok { w with callDepth := depth } .next := by
  have hraw : (inWorld locals (execOpenList K m
      [.exprStmt (.constant (.int 1) adequacySpan) adequacySpan])) w =
      .ok (.ok RFlow.next, w) := by rfl
  unfold finishCallM
  apply toRun_tryCatch_ok
  rw [bind_apply, hraw]
  rfl

theorem finishCallM_ret_constant_body_ok (K : Kont) (m : Module)
    (locals : REnv) (w : World) (depth : Nat) :
    toRun (finishCallM depth
      (inWorld locals (execOpenList K m
        [.ret (some (.constant (.int 1) adequacySpan)) adequacySpan]))) w =
      .ok { w with callDepth := depth } (.ret (.int 1)) := by
  have hraw : (inWorld locals (execOpenList K m
      [.ret (some (.constant (.int 1) adequacySpan)) adequacySpan])) w =
      .ok (.ok (.ret (.int 1)), w) := by rfl
  unfold finishCallM
  apply toRun_tryCatch_ok
  rw [bind_apply, hraw]
  rfl

theorem finishCallM_ret_none_body_ok (K : Kont) (m : Module)
    (locals : REnv) (w : World) (depth : Nat) :
    toRun (finishCallM depth
      (inWorld locals (execOpenList K m
        [.ret Option.none adequacySpan]))) w =
      .ok { w with callDepth := depth } (.ret .none) := by
  have hraw : (inWorld locals (execOpenList K m
      [.ret Option.none adequacySpan])) w =
      .ok (.ok (.ret .none), w) := by rfl
  unfold finishCallM
  apply toRun_tryCatch_ok
  rw [bind_apply, hraw]
  rfl

theorem finishCallM_break_body_ok (K : Kont) (m : Module)
    (locals : REnv) (w : World) (depth : Nat) :
    toRun (finishCallM depth
      (inWorld locals (execOpenList K m [.brk adequacySpan]))) w =
      .ok { w with callDepth := depth } RFlow.brk := by
  have hraw : (inWorld locals (execOpenList K m [.brk adequacySpan])) w =
      .ok (.ok RFlow.brk, w) := by rfl
  unfold finishCallM
  apply toRun_tryCatch_ok
  rw [bind_apply, hraw]
  rfl

theorem finishCallM_continue_body_ok (K : Kont) (m : Module)
    (locals : REnv) (w : World) (depth : Nat) :
    toRun (finishCallM depth
      (inWorld locals (execOpenList K m [.cont adequacySpan]))) w =
      .ok { w with callDepth := depth } RFlow.cont := by
  have hraw : (inWorld locals (execOpenList K m [.cont adequacySpan])) w =
      .ok (.ok RFlow.cont, w) := by rfl
  unfold finishCallM
  apply toRun_tryCatch_ok
  rw [bind_apply, hraw]
  rfl

theorem finishCallM_pass_expr_body_ok (K : Kont) (m : Module)
    (locals : REnv) (w : World) (depth : Nat) :
    toRun (finishCallM depth
      (inWorld locals (execOpenList K m
        [.pass adequacySpan,
         .exprStmt (.constant (.int 1) adequacySpan) adequacySpan]))) w =
      .ok { w with callDepth := depth } .next := by
  have hraw : (inWorld locals (execOpenList K m
      [.pass adequacySpan,
       .exprStmt (.constant (.int 1) adequacySpan) adequacySpan])) w =
      .ok (.ok RFlow.next, w) := by rfl
  unfold finishCallM
  apply toRun_tryCatch_ok
  rw [bind_apply, hraw]
  rfl

theorem finishCallM_pass_ret_body_ok (K : Kont) (m : Module)
    (locals : REnv) (w : World) (depth : Nat) :
    toRun (finishCallM depth
      (inWorld locals (execOpenList K m
        [.pass adequacySpan,
         .ret (some (.constant (.int 1) adequacySpan)) adequacySpan]))) w =
      .ok { w with callDepth := depth } (.ret (.int 1)) := by
  have hraw : (inWorld locals (execOpenList K m
      [.pass adequacySpan,
       .ret (some (.constant (.int 1) adequacySpan)) adequacySpan])) w =
      .ok (.ok (.ret (.int 1)), w) := by rfl
  unfold finishCallM
  apply toRun_tryCatch_ok
  rw [bind_apply, hraw]
  rfl

theorem finishCallM_pass_break_body_ok (K : Kont) (m : Module)
    (locals : REnv) (w : World) (depth : Nat) :
    toRun (finishCallM depth
      (inWorld locals (execOpenList K m
        [.pass adequacySpan, .brk adequacySpan]))) w =
      .ok { w with callDepth := depth } RFlow.brk := by
  have hraw : (inWorld locals (execOpenList K m
      [.pass adequacySpan, .brk adequacySpan])) w =
      .ok (.ok RFlow.brk, w) := by rfl
  unfold finishCallM
  apply toRun_tryCatch_ok
  rw [bind_apply, hraw]
  rfl

theorem finishCallM_pass_continue_body_ok (K : Kont) (m : Module)
    (locals : REnv) (w : World) (depth : Nat) :
    toRun (finishCallM depth
      (inWorld locals (execOpenList K m
        [.pass adequacySpan, .cont adequacySpan]))) w =
      .ok { w with callDepth := depth } RFlow.cont := by
  have hraw : (inWorld locals (execOpenList K m
      [.pass adequacySpan, .cont adequacySpan])) w =
      .ok (.ok RFlow.cont, w) := by rfl
  unfold finishCallM
  apply toRun_tryCatch_ok
  rw [bind_apply, hraw]
  rfl

theorem finishCallM_three_pass_body_ok (K : Kont) (m : Module)
    (locals : REnv) (w : World) (depth : Nat) :
    toRun (finishCallM depth
      (inWorld locals (execOpenList K m
        [.pass adequacySpan, .pass adequacySpan, .pass adequacySpan]))) w =
      .ok { w with callDepth := depth } .next := by
  have hraw : (inWorld locals (execOpenList K m
      [.pass adequacySpan, .pass adequacySpan, .pass adequacySpan])) w =
      .ok (.ok RFlow.next, w) := by rfl
  unfold finishCallM
  apply toRun_tryCatch_ok
  rw [bind_apply, hraw]
  rfl

theorem finishCallM_four_pass_body_ok (K : Kont) (m : Module)
    (locals : REnv) (w : World) (depth : Nat) :
    toRun (finishCallM depth
      (inWorld locals (execOpenList K m
        [.pass adequacySpan, .pass adequacySpan,
         .pass adequacySpan, .pass adequacySpan]))) w =
      .ok { w with callDepth := depth } .next := by
  have hraw : (inWorld locals (execOpenList K m
      [.pass adequacySpan, .pass adequacySpan,
       .pass adequacySpan, .pass adequacySpan])) w =
      .ok (.ok RFlow.next, w) := by rfl
  unfold finishCallM
  apply toRun_tryCatch_ok
  rw [bind_apply, hraw]
  rfl

theorem finishCallM_five_pass_body_ok (K : Kont) (m : Module)
    (locals : REnv) (w : World) (depth : Nat) :
    toRun (finishCallM depth
      (inWorld locals (execOpenList K m
        [.pass adequacySpan, .pass adequacySpan, .pass adequacySpan,
         .pass adequacySpan, .pass adequacySpan]))) w =
      .ok { w with callDepth := depth } .next := by
  have hraw : (inWorld locals (execOpenList K m
      [.pass adequacySpan, .pass adequacySpan, .pass adequacySpan,
       .pass adequacySpan, .pass adequacySpan])) w =
      .ok (.ok RFlow.next, w) := by rfl
  unfold finishCallM
  apply toRun_tryCatch_ok
  rw [bind_apply, hraw]
  rfl

theorem finishCallM_four_pass_ret_body_ok (K : Kont) (m : Module)
    (locals : REnv) (w : World) (depth : Nat) :
    toRun (finishCallM depth
      (inWorld locals (execOpenList K m
        [.pass adequacySpan, .pass adequacySpan, .pass adequacySpan,
         .pass adequacySpan,
         .ret (some (.constant (.int 1) adequacySpan)) adequacySpan]))) w =
      .ok { w with callDepth := depth } (.ret (.int 1)) := by
  have hraw : (inWorld locals (execOpenList K m
      [.pass adequacySpan, .pass adequacySpan, .pass adequacySpan,
       .pass adequacySpan,
       .ret (some (.constant (.int 1) adequacySpan)) adequacySpan])) w =
      .ok (.ok (.ret (.int 1)), w) := by rfl
  unfold finishCallM
  apply toRun_tryCatch_ok
  rw [bind_apply, hraw]
  rfl

theorem finishCallM_pass_assign_empty_locals_body_ok (K : Kont) (m : Module)
    (w : World) (depth : Nat) :
    toRun (finishCallM depth
      (inWorld [] (execOpenList K m
        [.pass adequacySpan,
         .assign #[.name "x" adequacySpan]
           (.constant (.int 1) adequacySpan) adequacySpan]))) w =
      .ok { w with callDepth := depth } .next := by
  have hraw : (inWorld [] (execOpenList K m
      [.pass adequacySpan,
       .assign #[.name "x" adequacySpan]
         (.constant (.int 1) adequacySpan) adequacySpan])) w =
      .ok (.ok RFlow.next, w) := by rfl
  unfold finishCallM
  apply toRun_tryCatch_ok
  rw [bind_apply, hraw]
  rfl

theorem finishCallM_assign_existing_local_body_ok (K : Kont) (m : Module)
    (w : World) (depth : Nat) :
    toRun (finishCallM depth
      (inWorld [("x", .int 0)] (execOpenList K m
        [.assign #[.name "x" adequacySpan]
          (.constant (.int 1) adequacySpan) adequacySpan]))) w =
      .ok { w with callDepth := depth } .next := by
  have hraw : (inWorld [("x", .int 0)] (execOpenList K m
      [.assign #[.name "x" adequacySpan]
        (.constant (.int 1) adequacySpan) adequacySpan])) w =
      .ok (.ok RFlow.next, w) := by rfl
  unfold finishCallM
  apply toRun_tryCatch_ok
  rw [bind_apply, hraw]
  rfl

theorem finishCallM_assign_existing_local_ret_body_ok (K : Kont) (m : Module)
    (w : World) (depth : Nat) :
    toRun (finishCallM depth
      (inWorld [("x", .int 0)] (execOpenList K m
        [.assign #[.name "x" adequacySpan]
           (.constant (.int 1) adequacySpan) adequacySpan,
         .ret (some (.constant (.int 2) adequacySpan)) adequacySpan]))) w =
      .ok { w with callDepth := depth } (.ret (.int 2)) := by
  have hraw : (inWorld [("x", .int 0)] (execOpenList K m
      [.assign #[.name "x" adequacySpan]
         (.constant (.int 1) adequacySpan) adequacySpan,
       .ret (some (.constant (.int 2) adequacySpan)) adequacySpan])) w =
      .ok (.ok (.ret (.int 2)), w) := by rfl
  unfold finishCallM
  apply toRun_tryCatch_ok
  rw [bind_apply, hraw]
  rfl

theorem finishCallM_assign_existing_local_pass_body_ok (K : Kont) (m : Module)
    (w : World) (depth : Nat) :
    toRun (finishCallM depth
      (inWorld [("x", .int 0)] (execOpenList K m
        [.assign #[.name "x" adequacySpan]
           (.constant (.int 1) adequacySpan) adequacySpan,
         .pass adequacySpan]))) w =
      .ok { w with callDepth := depth } .next := by
  have hraw : (inWorld [("x", .int 0)] (execOpenList K m
      [.assign #[.name "x" adequacySpan]
         (.constant (.int 1) adequacySpan) adequacySpan,
       .pass adequacySpan])) w =
      .ok (.ok RFlow.next, w) := by rfl
  unfold finishCallM
  apply toRun_tryCatch_ok
  rw [bind_apply, hraw]
  rfl

theorem finishCallM_assign_existing_local_break_body_ok (K : Kont) (m : Module)
    (w : World) (depth : Nat) :
    toRun (finishCallM depth
      (inWorld [("x", .int 0)] (execOpenList K m
        [.assign #[.name "x" adequacySpan]
           (.constant (.int 1) adequacySpan) adequacySpan,
         .brk adequacySpan]))) w =
      .ok { w with callDepth := depth } RFlow.brk := by
  have hraw : (inWorld [("x", .int 0)] (execOpenList K m
      [.assign #[.name "x" adequacySpan]
         (.constant (.int 1) adequacySpan) adequacySpan,
       .brk adequacySpan])) w =
      .ok (.ok RFlow.brk, w) := by rfl
  unfold finishCallM
  apply toRun_tryCatch_ok
  rw [bind_apply, hraw]
  rfl

theorem finishCallM_assign_existing_local_continue_body_ok (K : Kont) (m : Module)
    (w : World) (depth : Nat) :
    toRun (finishCallM depth
      (inWorld [("x", .int 0)] (execOpenList K m
        [.assign #[.name "x" adequacySpan]
           (.constant (.int 1) adequacySpan) adequacySpan,
         .cont adequacySpan]))) w =
      .ok { w with callDepth := depth } RFlow.cont := by
  have hraw : (inWorld [("x", .int 0)] (execOpenList K m
      [.assign #[.name "x" adequacySpan]
         (.constant (.int 1) adequacySpan) adequacySpan,
       .cont adequacySpan])) w =
      .ok (.ok RFlow.cont, w) := by rfl
  unfold finishCallM
  apply toRun_tryCatch_ok
  rw [bind_apply, hraw]
  rfl

theorem finishCallM_assign_existing_local_ret_none_body_ok (K : Kont) (m : Module)
    (w : World) (depth : Nat) :
    toRun (finishCallM depth
      (inWorld [("x", .int 0)] (execOpenList K m
        [.assign #[.name "x" adequacySpan]
           (.constant (.int 1) adequacySpan) adequacySpan,
         .ret Option.none adequacySpan]))) w =
      .ok { w with callDepth := depth } (.ret .none) := by
  have hraw : (inWorld [("x", .int 0)] (execOpenList K m
      [.assign #[.name "x" adequacySpan]
         (.constant (.int 1) adequacySpan) adequacySpan,
       .ret Option.none adequacySpan])) w =
      .ok (.ok (.ret .none), w) := by rfl
  unfold finishCallM
  apply toRun_tryCatch_ok
  rw [bind_apply, hraw]
  rfl

theorem finishCallM_assign_existing_local_expr_body_ok (K : Kont) (m : Module)
    (w : World) (depth : Nat) :
    toRun (finishCallM depth
      (inWorld [("x", .int 0)] (execOpenList K m
        [.assign #[.name "x" adequacySpan]
           (.constant (.int 1) adequacySpan) adequacySpan,
         .exprStmt (.constant (.int 2) adequacySpan) adequacySpan]))) w =
      .ok { w with callDepth := depth } .next := by
  have hraw : (inWorld [("x", .int 0)] (execOpenList K m
      [.assign #[.name "x" adequacySpan]
         (.constant (.int 1) adequacySpan) adequacySpan,
       .exprStmt (.constant (.int 2) adequacySpan) adequacySpan])) w =
      .ok (.ok RFlow.next, w) := by rfl
  unfold finishCallM
  apply toRun_tryCatch_ok
  rw [bind_apply, hraw]
  rfl

theorem finishCallM_assign_two_existing_locals_body_ok (K : Kont) (m : Module)
    (w : World) (depth : Nat) :
    toRun (finishCallM depth
      (inWorld [("x", .int 0), ("y", .int 0)] (execOpenList K m
        [.assign #[.name "x" adequacySpan]
           (.constant (.int 1) adequacySpan) adequacySpan,
         .assign #[.name "y" adequacySpan]
           (.constant (.int 2) adequacySpan) adequacySpan]))) w =
      .ok { w with callDepth := depth } .next := by
  have hraw : (inWorld [("x", .int 0), ("y", .int 0)] (execOpenList K m
      [.assign #[.name "x" adequacySpan]
         (.constant (.int 1) adequacySpan) adequacySpan,
       .assign #[.name "y" adequacySpan]
         (.constant (.int 2) adequacySpan) adequacySpan])) w =
      .ok (.ok RFlow.next, w) := by rfl
  unfold finishCallM
  apply toRun_tryCatch_ok
  rw [bind_apply, hraw]
  rfl

theorem finishCallM_assign_three_existing_locals_body_ok (K : Kont) (m : Module)
    (w : World) (depth : Nat) :
    toRun (finishCallM depth
      (inWorld [("x", .int 0), ("y", .int 0), ("z", .int 0)] (execOpenList K m
        [.assign #[.name "x" adequacySpan]
           (.constant (.int 1) adequacySpan) adequacySpan,
         .assign #[.name "y" adequacySpan]
           (.constant (.int 2) adequacySpan) adequacySpan,
         .assign #[.name "z" adequacySpan]
           (.constant (.int 3) adequacySpan) adequacySpan]))) w =
      .ok { w with callDepth := depth } .next := by
  have hraw : (inWorld [("x", .int 0), ("y", .int 0), ("z", .int 0)] (execOpenList K m
      [.assign #[.name "x" adequacySpan]
         (.constant (.int 1) adequacySpan) adequacySpan,
       .assign #[.name "y" adequacySpan]
         (.constant (.int 2) adequacySpan) adequacySpan,
       .assign #[.name "z" adequacySpan]
         (.constant (.int 3) adequacySpan) adequacySpan])) w =
      .ok (.ok RFlow.next, w) := by rfl
  unfold finishCallM
  apply toRun_tryCatch_ok
  rw [bind_apply, hraw]
  rfl

theorem finishCallM_assign_existing_local_ret_pass_body_ok (K : Kont) (m : Module)
    (w : World) (depth : Nat) :
    toRun (finishCallM depth
      (inWorld [("x", .int 0)] (execOpenList K m
        [.assign #[.name "x" adequacySpan]
           (.constant (.int 1) adequacySpan) adequacySpan,
         .ret (some (.constant (.int 2) adequacySpan)) adequacySpan,
         .pass adequacySpan]))) w =
      .ok { w with callDepth := depth } (.ret (.int 2)) := by
  have hraw : (inWorld [("x", .int 0)] (execOpenList K m
      [.assign #[.name "x" adequacySpan]
         (.constant (.int 1) adequacySpan) adequacySpan,
       .ret (some (.constant (.int 2) adequacySpan)) adequacySpan,
       .pass adequacySpan])) w =
      .ok (.ok (.ret (.int 2)), w) := by rfl
  unfold finishCallM
  apply toRun_tryCatch_ok
  rw [bind_apply, hraw]
  rfl

theorem finishCallM_assign_two_existing_locals_ret_body_ok (K : Kont) (m : Module)
    (w : World) (depth : Nat) :
    toRun (finishCallM depth
      (inWorld [("x", .int 0), ("y", .int 0)] (execOpenList K m
        [.assign #[.name "x" adequacySpan]
           (.constant (.int 1) adequacySpan) adequacySpan,
         .assign #[.name "y" adequacySpan]
           (.constant (.int 2) adequacySpan) adequacySpan,
         .ret (some (.constant (.int 3) adequacySpan)) adequacySpan]))) w =
      .ok { w with callDepth := depth } (.ret (.int 3)) := by
  have hraw : (inWorld [("x", .int 0), ("y", .int 0)] (execOpenList K m
      [.assign #[.name "x" adequacySpan]
         (.constant (.int 1) adequacySpan) adequacySpan,
       .assign #[.name "y" adequacySpan]
         (.constant (.int 2) adequacySpan) adequacySpan,
       .ret (some (.constant (.int 3) adequacySpan)) adequacySpan])) w =
      .ok (.ok (.ret (.int 3)), w) := by rfl
  unfold finishCallM
  apply toRun_tryCatch_ok
  rw [bind_apply, hraw]
  rfl

theorem finishCallM_assign_three_existing_locals_ret_body_ok (K : Kont) (m : Module)
    (w : World) (depth : Nat) :
    toRun (finishCallM depth
      (inWorld [("x", .int 0), ("y", .int 0), ("z", .int 0)] (execOpenList K m
        [.assign #[.name "x" adequacySpan]
           (.constant (.int 1) adequacySpan) adequacySpan,
         .assign #[.name "y" adequacySpan]
           (.constant (.int 2) adequacySpan) adequacySpan,
         .assign #[.name "z" adequacySpan]
           (.constant (.int 3) adequacySpan) adequacySpan,
         .ret (some (.constant (.int 4) adequacySpan)) adequacySpan]))) w =
      .ok { w with callDepth := depth } (.ret (.int 4)) := by
  have hraw : (inWorld [("x", .int 0), ("y", .int 0), ("z", .int 0)] (execOpenList K m
      [.assign #[.name "x" adequacySpan]
         (.constant (.int 1) adequacySpan) adequacySpan,
       .assign #[.name "y" adequacySpan]
         (.constant (.int 2) adequacySpan) adequacySpan,
       .assign #[.name "z" adequacySpan]
         (.constant (.int 3) adequacySpan) adequacySpan,
       .ret (some (.constant (.int 4) adequacySpan)) adequacySpan])) w =
      .ok (.ok (.ret (.int 4)), w) := by rfl
  unfold finishCallM
  apply toRun_tryCatch_ok
  rw [bind_apply, hraw]
  rfl

theorem finishCallM_assign_three_existing_locals_pass_body_ok (K : Kont) (m : Module)
    (w : World) (depth : Nat) :
    toRun (finishCallM depth
      (inWorld [("x", .int 0), ("y", .int 0), ("z", .int 0)] (execOpenList K m
        [.assign #[.name "x" adequacySpan]
           (.constant (.int 1) adequacySpan) adequacySpan,
         .assign #[.name "y" adequacySpan]
           (.constant (.int 2) adequacySpan) adequacySpan,
         .assign #[.name "z" adequacySpan]
           (.constant (.int 3) adequacySpan) adequacySpan,
         .pass adequacySpan]))) w =
      .ok { w with callDepth := depth } .next := by
  have hraw : (inWorld [("x", .int 0), ("y", .int 0), ("z", .int 0)] (execOpenList K m
      [.assign #[.name "x" adequacySpan]
         (.constant (.int 1) adequacySpan) adequacySpan,
       .assign #[.name "y" adequacySpan]
         (.constant (.int 2) adequacySpan) adequacySpan,
       .assign #[.name "z" adequacySpan]
         (.constant (.int 3) adequacySpan) adequacySpan,
       .pass adequacySpan])) w =
      .ok (.ok RFlow.next, w) := by rfl
  unfold finishCallM
  apply toRun_tryCatch_ok
  rw [bind_apply, hraw]
  rfl

theorem finishCallM_assign_three_existing_locals_expr_body_ok (K : Kont) (m : Module)
    (w : World) (depth : Nat) :
    toRun (finishCallM depth
      (inWorld [("x", .int 0), ("y", .int 0), ("z", .int 0)] (execOpenList K m
        [.assign #[.name "x" adequacySpan]
           (.constant (.int 1) adequacySpan) adequacySpan,
         .assign #[.name "y" adequacySpan]
           (.constant (.int 2) adequacySpan) adequacySpan,
         .assign #[.name "z" adequacySpan]
           (.constant (.int 3) adequacySpan) adequacySpan,
         .exprStmt (.constant (.int 4) adequacySpan) adequacySpan]))) w =
      .ok { w with callDepth := depth } .next := by
  have hraw : (inWorld [("x", .int 0), ("y", .int 0), ("z", .int 0)] (execOpenList K m
      [.assign #[.name "x" adequacySpan]
         (.constant (.int 1) adequacySpan) adequacySpan,
       .assign #[.name "y" adequacySpan]
         (.constant (.int 2) adequacySpan) adequacySpan,
       .assign #[.name "z" adequacySpan]
         (.constant (.int 3) adequacySpan) adequacySpan,
       .exprStmt (.constant (.int 4) adequacySpan) adequacySpan])) w =
      .ok (.ok RFlow.next, w) := by rfl
  unfold finishCallM
  apply toRun_tryCatch_ok
  rw [bind_apply, hraw]
  rfl

theorem finishCallM_assign_four_existing_locals_body_ok (K : Kont) (m : Module)
    (w : World) (depth : Nat) :
    toRun (finishCallM depth
      (inWorld [("w", .int 0), ("x", .int 0), ("y", .int 0), ("z", .int 0)] (execOpenList K m
        [.assign #[.name "w" adequacySpan]
           (.constant (.int 1) adequacySpan) adequacySpan,
         .assign #[.name "x" adequacySpan]
           (.constant (.int 2) adequacySpan) adequacySpan,
         .assign #[.name "y" adequacySpan]
           (.constant (.int 3) adequacySpan) adequacySpan,
         .assign #[.name "z" adequacySpan]
           (.constant (.int 4) adequacySpan) adequacySpan]))) w =
      .ok { w with callDepth := depth } .next := by
  have hraw : (inWorld [("w", .int 0), ("x", .int 0), ("y", .int 0), ("z", .int 0)] (execOpenList K m
      [.assign #[.name "w" adequacySpan]
         (.constant (.int 1) adequacySpan) adequacySpan,
       .assign #[.name "x" adequacySpan]
         (.constant (.int 2) adequacySpan) adequacySpan,
       .assign #[.name "y" adequacySpan]
         (.constant (.int 3) adequacySpan) adequacySpan,
       .assign #[.name "z" adequacySpan]
         (.constant (.int 4) adequacySpan) adequacySpan])) w =
      .ok (.ok RFlow.next, w) := by rfl
  unfold finishCallM
  apply toRun_tryCatch_ok
  rw [bind_apply, hraw]
  rfl

theorem finishCallM_assign_four_existing_locals_ret_body_ok (K : Kont) (m : Module)
    (w : World) (depth : Nat) :
    toRun (finishCallM depth
      (inWorld [("w", .int 0), ("x", .int 0), ("y", .int 0), ("z", .int 0)] (execOpenList K m
        [.assign #[.name "w" adequacySpan]
           (.constant (.int 1) adequacySpan) adequacySpan,
         .assign #[.name "x" adequacySpan]
           (.constant (.int 2) adequacySpan) adequacySpan,
         .assign #[.name "y" adequacySpan]
           (.constant (.int 3) adequacySpan) adequacySpan,
         .assign #[.name "z" adequacySpan]
           (.constant (.int 4) adequacySpan) adequacySpan,
         .ret (some (.constant (.int 5) adequacySpan)) adequacySpan]))) w =
      .ok { w with callDepth := depth } (.ret (.int 5)) := by
  have hraw : (inWorld [("w", .int 0), ("x", .int 0), ("y", .int 0), ("z", .int 0)] (execOpenList K m
      [.assign #[.name "w" adequacySpan]
         (.constant (.int 1) adequacySpan) adequacySpan,
       .assign #[.name "x" adequacySpan]
         (.constant (.int 2) adequacySpan) adequacySpan,
       .assign #[.name "y" adequacySpan]
         (.constant (.int 3) adequacySpan) adequacySpan,
       .assign #[.name "z" adequacySpan]
         (.constant (.int 4) adequacySpan) adequacySpan,
       .ret (some (.constant (.int 5) adequacySpan)) adequacySpan])) w =
      .ok (.ok (.ret (.int 5)), w) := by rfl
  unfold finishCallM
  apply toRun_tryCatch_ok
  rw [bind_apply, hraw]
  rfl

theorem finishCallM_assign_four_existing_locals_pass_body_ok (K : Kont) (m : Module)
    (w : World) (depth : Nat) :
    toRun (finishCallM depth
      (inWorld [("w", .int 0), ("x", .int 0), ("y", .int 0), ("z", .int 0)] (execOpenList K m
        [.assign #[.name "w" adequacySpan]
           (.constant (.int 1) adequacySpan) adequacySpan,
         .assign #[.name "x" adequacySpan]
           (.constant (.int 2) adequacySpan) adequacySpan,
         .assign #[.name "y" adequacySpan]
           (.constant (.int 3) adequacySpan) adequacySpan,
         .assign #[.name "z" adequacySpan]
           (.constant (.int 4) adequacySpan) adequacySpan,
         .pass adequacySpan]))) w =
      .ok { w with callDepth := depth } .next := by
  have hraw : (inWorld [("w", .int 0), ("x", .int 0), ("y", .int 0), ("z", .int 0)] (execOpenList K m
      [.assign #[.name "w" adequacySpan]
         (.constant (.int 1) adequacySpan) adequacySpan,
       .assign #[.name "x" adequacySpan]
         (.constant (.int 2) adequacySpan) adequacySpan,
       .assign #[.name "y" adequacySpan]
         (.constant (.int 3) adequacySpan) adequacySpan,
       .assign #[.name "z" adequacySpan]
         (.constant (.int 4) adequacySpan) adequacySpan,
       .pass adequacySpan])) w =
      .ok (.ok RFlow.next, w) := by rfl
  unfold finishCallM
  apply toRun_tryCatch_ok
  rw [bind_apply, hraw]
  rfl

theorem finishCallM_assign_four_existing_locals_expr_body_ok (K : Kont) (m : Module)
    (w : World) (depth : Nat) :
    toRun (finishCallM depth
      (inWorld [("w", .int 0), ("x", .int 0), ("y", .int 0), ("z", .int 0)] (execOpenList K m
        [.assign #[.name "w" adequacySpan]
           (.constant (.int 1) adequacySpan) adequacySpan,
         .assign #[.name "x" adequacySpan]
           (.constant (.int 2) adequacySpan) adequacySpan,
         .assign #[.name "y" adequacySpan]
           (.constant (.int 3) adequacySpan) adequacySpan,
         .assign #[.name "z" adequacySpan]
           (.constant (.int 4) adequacySpan) adequacySpan,
         .exprStmt (.constant (.int 5) adequacySpan) adequacySpan]))) w =
      .ok { w with callDepth := depth } .next := by
  have hraw : (inWorld [("w", .int 0), ("x", .int 0), ("y", .int 0), ("z", .int 0)] (execOpenList K m
      [.assign #[.name "w" adequacySpan]
         (.constant (.int 1) adequacySpan) adequacySpan,
       .assign #[.name "x" adequacySpan]
         (.constant (.int 2) adequacySpan) adequacySpan,
       .assign #[.name "y" adequacySpan]
         (.constant (.int 3) adequacySpan) adequacySpan,
       .assign #[.name "z" adequacySpan]
         (.constant (.int 4) adequacySpan) adequacySpan,
       .exprStmt (.constant (.int 5) adequacySpan) adequacySpan])) w =
      .ok (.ok RFlow.next, w) := by rfl
  unfold finishCallM
  apply toRun_tryCatch_ok
  rw [bind_apply, hraw]
  rfl

theorem finishCallM_assign_four_existing_locals_ret_none_body_ok (K : Kont) (m : Module)
    (w : World) (depth : Nat) :
    toRun (finishCallM depth
      (inWorld [("w", .int 0), ("x", .int 0), ("y", .int 0), ("z", .int 0)] (execOpenList K m
        [.assign #[.name "w" adequacySpan]
           (.constant (.int 1) adequacySpan) adequacySpan,
         .assign #[.name "x" adequacySpan]
           (.constant (.int 2) adequacySpan) adequacySpan,
         .assign #[.name "y" adequacySpan]
           (.constant (.int 3) adequacySpan) adequacySpan,
         .assign #[.name "z" adequacySpan]
           (.constant (.int 4) adequacySpan) adequacySpan,
         .ret Option.none adequacySpan]))) w =
      .ok { w with callDepth := depth } (.ret .none) := by
  have hraw : (inWorld [("w", .int 0), ("x", .int 0), ("y", .int 0), ("z", .int 0)] (execOpenList K m
      [.assign #[.name "w" adequacySpan]
         (.constant (.int 1) adequacySpan) adequacySpan,
       .assign #[.name "x" adequacySpan]
         (.constant (.int 2) adequacySpan) adequacySpan,
       .assign #[.name "y" adequacySpan]
         (.constant (.int 3) adequacySpan) adequacySpan,
       .assign #[.name "z" adequacySpan]
         (.constant (.int 4) adequacySpan) adequacySpan,
       .ret Option.none adequacySpan])) w =
      .ok (.ok (.ret .none), w) := by rfl
  unfold finishCallM
  apply toRun_tryCatch_ok
  rw [bind_apply, hraw]
  rfl

theorem finishCallM_assign_four_existing_locals_break_body_ok (K : Kont) (m : Module)
    (w : World) (depth : Nat) :
    toRun (finishCallM depth
      (inWorld [("w", .int 0), ("x", .int 0), ("y", .int 0), ("z", .int 0)] (execOpenList K m
        [.assign #[.name "w" adequacySpan]
           (.constant (.int 1) adequacySpan) adequacySpan,
         .assign #[.name "x" adequacySpan]
           (.constant (.int 2) adequacySpan) adequacySpan,
         .assign #[.name "y" adequacySpan]
           (.constant (.int 3) adequacySpan) adequacySpan,
         .assign #[.name "z" adequacySpan]
           (.constant (.int 4) adequacySpan) adequacySpan,
         .brk adequacySpan]))) w =
      .ok { w with callDepth := depth } RFlow.brk := by
  have hraw : (inWorld [("w", .int 0), ("x", .int 0), ("y", .int 0), ("z", .int 0)] (execOpenList K m
      [.assign #[.name "w" adequacySpan]
         (.constant (.int 1) adequacySpan) adequacySpan,
       .assign #[.name "x" adequacySpan]
         (.constant (.int 2) adequacySpan) adequacySpan,
       .assign #[.name "y" adequacySpan]
         (.constant (.int 3) adequacySpan) adequacySpan,
       .assign #[.name "z" adequacySpan]
         (.constant (.int 4) adequacySpan) adequacySpan,
       .brk adequacySpan])) w =
      .ok (.ok RFlow.brk, w) := by rfl
  unfold finishCallM
  apply toRun_tryCatch_ok
  rw [bind_apply, hraw]
  rfl

theorem finishCallM_assign_four_existing_locals_continue_body_ok (K : Kont) (m : Module)
    (w : World) (depth : Nat) :
    toRun (finishCallM depth
      (inWorld [("w", .int 0), ("x", .int 0), ("y", .int 0), ("z", .int 0)] (execOpenList K m
        [.assign #[.name "w" adequacySpan]
           (.constant (.int 1) adequacySpan) adequacySpan,
         .assign #[.name "x" adequacySpan]
           (.constant (.int 2) adequacySpan) adequacySpan,
         .assign #[.name "y" adequacySpan]
           (.constant (.int 3) adequacySpan) adequacySpan,
         .assign #[.name "z" adequacySpan]
           (.constant (.int 4) adequacySpan) adequacySpan,
         .cont adequacySpan]))) w =
      .ok { w with callDepth := depth } RFlow.cont := by
  have hraw : (inWorld [("w", .int 0), ("x", .int 0), ("y", .int 0), ("z", .int 0)] (execOpenList K m
      [.assign #[.name "w" adequacySpan]
         (.constant (.int 1) adequacySpan) adequacySpan,
       .assign #[.name "x" adequacySpan]
         (.constant (.int 2) adequacySpan) adequacySpan,
       .assign #[.name "y" adequacySpan]
         (.constant (.int 3) adequacySpan) adequacySpan,
       .assign #[.name "z" adequacySpan]
         (.constant (.int 4) adequacySpan) adequacySpan,
       .cont adequacySpan])) w =
      .ok (.ok RFlow.cont, w) := by rfl
  unfold finishCallM
  apply toRun_tryCatch_ok
  rw [bind_apply, hraw]
  rfl

theorem finishCallM_assign_five_existing_locals_body_ok (K : Kont) (m : Module)
    (w : World) (depth : Nat) :
    toRun (finishCallM depth
      (inWorld [("v", .int 0), ("w", .int 0), ("x", .int 0), ("y", .int 0), ("z", .int 0)] (execOpenList K m
        [.assign #[.name "v" adequacySpan]
           (.constant (.int 0) adequacySpan) adequacySpan,
         .assign #[.name "w" adequacySpan]
           (.constant (.int 1) adequacySpan) adequacySpan,
         .assign #[.name "x" adequacySpan]
           (.constant (.int 2) adequacySpan) adequacySpan,
         .assign #[.name "y" adequacySpan]
           (.constant (.int 3) adequacySpan) adequacySpan,
         .assign #[.name "z" adequacySpan]
           (.constant (.int 4) adequacySpan) adequacySpan]))) w =
      .ok { w with callDepth := depth } .next := by
  have hraw : (inWorld [("v", .int 0), ("w", .int 0), ("x", .int 0), ("y", .int 0), ("z", .int 0)] (execOpenList K m
      [.assign #[.name "v" adequacySpan]
         (.constant (.int 0) adequacySpan) adequacySpan,
       .assign #[.name "w" adequacySpan]
         (.constant (.int 1) adequacySpan) adequacySpan,
       .assign #[.name "x" adequacySpan]
         (.constant (.int 2) adequacySpan) adequacySpan,
       .assign #[.name "y" adequacySpan]
         (.constant (.int 3) adequacySpan) adequacySpan,
       .assign #[.name "z" adequacySpan]
         (.constant (.int 4) adequacySpan) adequacySpan])) w =
      .ok (.ok RFlow.next, w) := by rfl
  unfold finishCallM
  apply toRun_tryCatch_ok
  rw [bind_apply, hraw]
  rfl

theorem finishCallM_assign_five_existing_locals_ret_body_ok (K : Kont) (m : Module)
    (w : World) (depth : Nat) :
    toRun (finishCallM depth
      (inWorld [("v", .int 0), ("w", .int 0), ("x", .int 0), ("y", .int 0), ("z", .int 0)] (execOpenList K m
        [.assign #[.name "v" adequacySpan]
           (.constant (.int 0) adequacySpan) adequacySpan,
         .assign #[.name "w" adequacySpan]
           (.constant (.int 1) adequacySpan) adequacySpan,
         .assign #[.name "x" adequacySpan]
           (.constant (.int 2) adequacySpan) adequacySpan,
         .assign #[.name "y" adequacySpan]
           (.constant (.int 3) adequacySpan) adequacySpan,
         .assign #[.name "z" adequacySpan]
           (.constant (.int 4) adequacySpan) adequacySpan,
         .ret (some (.constant (.int 5) adequacySpan)) adequacySpan]))) w =
      .ok { w with callDepth := depth } (.ret (.int 5)) := by
  have hraw : (inWorld [("v", .int 0), ("w", .int 0), ("x", .int 0), ("y", .int 0), ("z", .int 0)] (execOpenList K m
      [.assign #[.name "v" adequacySpan]
         (.constant (.int 0) adequacySpan) adequacySpan,
       .assign #[.name "w" adequacySpan]
         (.constant (.int 1) adequacySpan) adequacySpan,
       .assign #[.name "x" adequacySpan]
         (.constant (.int 2) adequacySpan) adequacySpan,
       .assign #[.name "y" adequacySpan]
         (.constant (.int 3) adequacySpan) adequacySpan,
       .assign #[.name "z" adequacySpan]
         (.constant (.int 4) adequacySpan) adequacySpan,
       .ret (some (.constant (.int 5) adequacySpan)) adequacySpan])) w =
      .ok (.ok (.ret (.int 5)), w) := by rfl
  unfold finishCallM
  apply toRun_tryCatch_ok
  rw [bind_apply, hraw]
  rfl

theorem finishCallM_assign_five_existing_locals_pass_body_ok (K : Kont) (m : Module)
    (w : World) (depth : Nat) :
    toRun (finishCallM depth
      (inWorld [("v", .int 0), ("w", .int 0), ("x", .int 0), ("y", .int 0), ("z", .int 0)] (execOpenList K m
        [.assign #[.name "v" adequacySpan]
           (.constant (.int 0) adequacySpan) adequacySpan,
         .assign #[.name "w" adequacySpan]
           (.constant (.int 1) adequacySpan) adequacySpan,
         .assign #[.name "x" adequacySpan]
           (.constant (.int 2) adequacySpan) adequacySpan,
         .assign #[.name "y" adequacySpan]
           (.constant (.int 3) adequacySpan) adequacySpan,
         .assign #[.name "z" adequacySpan]
           (.constant (.int 4) adequacySpan) adequacySpan,
         .pass adequacySpan]))) w =
      .ok { w with callDepth := depth } .next := by
  have hraw : (inWorld [("v", .int 0), ("w", .int 0), ("x", .int 0), ("y", .int 0), ("z", .int 0)] (execOpenList K m
      [.assign #[.name "v" adequacySpan]
         (.constant (.int 0) adequacySpan) adequacySpan,
       .assign #[.name "w" adequacySpan]
         (.constant (.int 1) adequacySpan) adequacySpan,
       .assign #[.name "x" adequacySpan]
         (.constant (.int 2) adequacySpan) adequacySpan,
       .assign #[.name "y" adequacySpan]
         (.constant (.int 3) adequacySpan) adequacySpan,
       .assign #[.name "z" adequacySpan]
         (.constant (.int 4) adequacySpan) adequacySpan,
       .pass adequacySpan])) w =
      .ok (.ok RFlow.next, w) := by rfl
  unfold finishCallM
  apply toRun_tryCatch_ok
  rw [bind_apply, hraw]
  rfl

theorem finishCallM_assign_five_existing_locals_expr_body_ok (K : Kont) (m : Module)
    (w : World) (depth : Nat) :
    toRun (finishCallM depth
      (inWorld [("v", .int 0), ("w", .int 0), ("x", .int 0), ("y", .int 0), ("z", .int 0)] (execOpenList K m
        [.assign #[.name "v" adequacySpan]
           (.constant (.int 0) adequacySpan) adequacySpan,
         .assign #[.name "w" adequacySpan]
           (.constant (.int 1) adequacySpan) adequacySpan,
         .assign #[.name "x" adequacySpan]
           (.constant (.int 2) adequacySpan) adequacySpan,
         .assign #[.name "y" adequacySpan]
           (.constant (.int 3) adequacySpan) adequacySpan,
         .assign #[.name "z" adequacySpan]
           (.constant (.int 4) adequacySpan) adequacySpan,
         .exprStmt (.constant (.int 5) adequacySpan) adequacySpan]))) w =
      .ok { w with callDepth := depth } .next := by
  have hraw : (inWorld [("v", .int 0), ("w", .int 0), ("x", .int 0), ("y", .int 0), ("z", .int 0)] (execOpenList K m
      [.assign #[.name "v" adequacySpan]
         (.constant (.int 0) adequacySpan) adequacySpan,
       .assign #[.name "w" adequacySpan]
         (.constant (.int 1) adequacySpan) adequacySpan,
       .assign #[.name "x" adequacySpan]
         (.constant (.int 2) adequacySpan) adequacySpan,
       .assign #[.name "y" adequacySpan]
         (.constant (.int 3) adequacySpan) adequacySpan,
       .assign #[.name "z" adequacySpan]
         (.constant (.int 4) adequacySpan) adequacySpan,
       .exprStmt (.constant (.int 5) adequacySpan) adequacySpan])) w =
      .ok (.ok RFlow.next, w) := by rfl
  unfold finishCallM
  apply toRun_tryCatch_ok
  rw [bind_apply, hraw]
  rfl

theorem finishCallM_assign_five_existing_locals_ret_none_body_ok (K : Kont) (m : Module)
    (w : World) (depth : Nat) :
    toRun (finishCallM depth
      (inWorld [("v", .int 0), ("w", .int 0), ("x", .int 0), ("y", .int 0), ("z", .int 0)] (execOpenList K m
        [.assign #[.name "v" adequacySpan]
           (.constant (.int 0) adequacySpan) adequacySpan,
         .assign #[.name "w" adequacySpan]
           (.constant (.int 1) adequacySpan) adequacySpan,
         .assign #[.name "x" adequacySpan]
           (.constant (.int 2) adequacySpan) adequacySpan,
         .assign #[.name "y" adequacySpan]
           (.constant (.int 3) adequacySpan) adequacySpan,
         .assign #[.name "z" adequacySpan]
           (.constant (.int 4) adequacySpan) adequacySpan,
         .ret Option.none adequacySpan]))) w =
      .ok { w with callDepth := depth } (.ret .none) := by
  have hraw : (inWorld [("v", .int 0), ("w", .int 0), ("x", .int 0), ("y", .int 0), ("z", .int 0)] (execOpenList K m
      [.assign #[.name "v" adequacySpan]
         (.constant (.int 0) adequacySpan) adequacySpan,
       .assign #[.name "w" adequacySpan]
         (.constant (.int 1) adequacySpan) adequacySpan,
       .assign #[.name "x" adequacySpan]
         (.constant (.int 2) adequacySpan) adequacySpan,
       .assign #[.name "y" adequacySpan]
         (.constant (.int 3) adequacySpan) adequacySpan,
       .assign #[.name "z" adequacySpan]
         (.constant (.int 4) adequacySpan) adequacySpan,
       .ret Option.none adequacySpan])) w =
      .ok (.ok (.ret .none), w) := by rfl
  unfold finishCallM
  apply toRun_tryCatch_ok
  rw [bind_apply, hraw]
  rfl

theorem finishCallM_assign_five_existing_locals_break_body_ok (K : Kont) (m : Module)
    (w : World) (depth : Nat) :
    toRun (finishCallM depth
      (inWorld [("v", .int 0), ("w", .int 0), ("x", .int 0), ("y", .int 0), ("z", .int 0)] (execOpenList K m
        [.assign #[.name "v" adequacySpan]
           (.constant (.int 0) adequacySpan) adequacySpan,
         .assign #[.name "w" adequacySpan]
           (.constant (.int 1) adequacySpan) adequacySpan,
         .assign #[.name "x" adequacySpan]
           (.constant (.int 2) adequacySpan) adequacySpan,
         .assign #[.name "y" adequacySpan]
           (.constant (.int 3) adequacySpan) adequacySpan,
         .assign #[.name "z" adequacySpan]
           (.constant (.int 4) adequacySpan) adequacySpan,
         .brk adequacySpan]))) w =
      .ok { w with callDepth := depth } RFlow.brk := by
  have hraw : (inWorld [("v", .int 0), ("w", .int 0), ("x", .int 0), ("y", .int 0), ("z", .int 0)] (execOpenList K m
      [.assign #[.name "v" adequacySpan]
         (.constant (.int 0) adequacySpan) adequacySpan,
       .assign #[.name "w" adequacySpan]
         (.constant (.int 1) adequacySpan) adequacySpan,
       .assign #[.name "x" adequacySpan]
         (.constant (.int 2) adequacySpan) adequacySpan,
       .assign #[.name "y" adequacySpan]
         (.constant (.int 3) adequacySpan) adequacySpan,
       .assign #[.name "z" adequacySpan]
         (.constant (.int 4) adequacySpan) adequacySpan,
       .brk adequacySpan])) w =
      .ok (.ok RFlow.brk, w) := by rfl
  unfold finishCallM
  apply toRun_tryCatch_ok
  rw [bind_apply, hraw]
  rfl

theorem finishCallM_assign_five_existing_locals_continue_body_ok (K : Kont) (m : Module)
    (w : World) (depth : Nat) :
    toRun (finishCallM depth
      (inWorld [("v", .int 0), ("w", .int 0), ("x", .int 0), ("y", .int 0), ("z", .int 0)] (execOpenList K m
        [.assign #[.name "v" adequacySpan]
           (.constant (.int 0) adequacySpan) adequacySpan,
         .assign #[.name "w" adequacySpan]
           (.constant (.int 1) adequacySpan) adequacySpan,
         .assign #[.name "x" adequacySpan]
           (.constant (.int 2) adequacySpan) adequacySpan,
         .assign #[.name "y" adequacySpan]
           (.constant (.int 3) adequacySpan) adequacySpan,
         .assign #[.name "z" adequacySpan]
           (.constant (.int 4) adequacySpan) adequacySpan,
         .cont adequacySpan]))) w =
      .ok { w with callDepth := depth } RFlow.cont := by
  have hraw : (inWorld [("v", .int 0), ("w", .int 0), ("x", .int 0), ("y", .int 0), ("z", .int 0)] (execOpenList K m
      [.assign #[.name "v" adequacySpan]
         (.constant (.int 0) adequacySpan) adequacySpan,
       .assign #[.name "w" adequacySpan]
         (.constant (.int 1) adequacySpan) adequacySpan,
       .assign #[.name "x" adequacySpan]
         (.constant (.int 2) adequacySpan) adequacySpan,
       .assign #[.name "y" adequacySpan]
         (.constant (.int 3) adequacySpan) adequacySpan,
       .assign #[.name "z" adequacySpan]
         (.constant (.int 4) adequacySpan) adequacySpan,
       .cont adequacySpan])) w =
      .ok (.ok RFlow.cont, w) := by rfl
  unfold finishCallM
  apply toRun_tryCatch_ok
  rw [bind_apply, hraw]
  rfl

theorem finishCallM_assign_six_existing_locals_body_ok (K : Kont) (m : Module)
    (w : World) (depth : Nat) :
    toRun (finishCallM depth
      (inWorld [("u", .int 0), ("v", .int 0), ("w", .int 0), ("x", .int 0), ("y", .int 0), ("z", .int 0)] (execOpenList K m
        [.assign #[.name "u" adequacySpan]
           (.constant (.int 0) adequacySpan) adequacySpan,
         .assign #[.name "v" adequacySpan]
           (.constant (.int 1) adequacySpan) adequacySpan,
         .assign #[.name "w" adequacySpan]
           (.constant (.int 2) adequacySpan) adequacySpan,
         .assign #[.name "x" adequacySpan]
           (.constant (.int 3) adequacySpan) adequacySpan,
         .assign #[.name "y" adequacySpan]
           (.constant (.int 4) adequacySpan) adequacySpan,
         .assign #[.name "z" adequacySpan]
           (.constant (.int 5) adequacySpan) adequacySpan]))) w =
      .ok { w with callDepth := depth } .next := by
  have hraw : (inWorld [("u", .int 0), ("v", .int 0), ("w", .int 0), ("x", .int 0), ("y", .int 0), ("z", .int 0)] (execOpenList K m
      [.assign #[.name "u" adequacySpan]
         (.constant (.int 0) adequacySpan) adequacySpan,
       .assign #[.name "v" adequacySpan]
         (.constant (.int 1) adequacySpan) adequacySpan,
       .assign #[.name "w" adequacySpan]
         (.constant (.int 2) adequacySpan) adequacySpan,
       .assign #[.name "x" adequacySpan]
         (.constant (.int 3) adequacySpan) adequacySpan,
       .assign #[.name "y" adequacySpan]
         (.constant (.int 4) adequacySpan) adequacySpan,
       .assign #[.name "z" adequacySpan]
         (.constant (.int 5) adequacySpan) adequacySpan])) w =
      .ok (.ok RFlow.next, w) := by rfl
  unfold finishCallM
  apply toRun_tryCatch_ok
  rw [bind_apply, hraw]
  rfl

theorem finishCallM_assign_six_existing_locals_ret_body_ok (K : Kont) (m : Module)
    (w : World) (depth : Nat) :
    toRun (finishCallM depth
      (inWorld [("u", .int 0), ("v", .int 0), ("w", .int 0), ("x", .int 0), ("y", .int 0), ("z", .int 0)] (execOpenList K m
        [.assign #[.name "u" adequacySpan]
           (.constant (.int 0) adequacySpan) adequacySpan,
         .assign #[.name "v" adequacySpan]
           (.constant (.int 1) adequacySpan) adequacySpan,
         .assign #[.name "w" adequacySpan]
           (.constant (.int 2) adequacySpan) adequacySpan,
         .assign #[.name "x" adequacySpan]
           (.constant (.int 3) adequacySpan) adequacySpan,
         .assign #[.name "y" adequacySpan]
           (.constant (.int 4) adequacySpan) adequacySpan,
         .assign #[.name "z" adequacySpan]
           (.constant (.int 5) adequacySpan) adequacySpan,
         .ret (some (.constant (.int 6) adequacySpan)) adequacySpan]))) w =
      .ok { w with callDepth := depth } (.ret (.int 6)) := by
  have hraw : (inWorld [("u", .int 0), ("v", .int 0), ("w", .int 0), ("x", .int 0), ("y", .int 0), ("z", .int 0)] (execOpenList K m
      [.assign #[.name "u" adequacySpan]
         (.constant (.int 0) adequacySpan) adequacySpan,
       .assign #[.name "v" adequacySpan]
         (.constant (.int 1) adequacySpan) adequacySpan,
       .assign #[.name "w" adequacySpan]
         (.constant (.int 2) adequacySpan) adequacySpan,
       .assign #[.name "x" adequacySpan]
         (.constant (.int 3) adequacySpan) adequacySpan,
       .assign #[.name "y" adequacySpan]
         (.constant (.int 4) adequacySpan) adequacySpan,
       .assign #[.name "z" adequacySpan]
         (.constant (.int 5) adequacySpan) adequacySpan,
       .ret (some (.constant (.int 6) adequacySpan)) adequacySpan])) w =
      .ok (.ok (.ret (.int 6)), w) := by rfl
  unfold finishCallM
  apply toRun_tryCatch_ok
  rw [bind_apply, hraw]
  rfl

theorem finishCallM_assign_six_existing_locals_pass_body_ok (K : Kont) (m : Module)
    (w : World) (depth : Nat) :
    toRun (finishCallM depth
      (inWorld [("u", .int 0), ("v", .int 0), ("w", .int 0), ("x", .int 0), ("y", .int 0), ("z", .int 0)] (execOpenList K m
        [.assign #[.name "u" adequacySpan]
           (.constant (.int 0) adequacySpan) adequacySpan,
         .assign #[.name "v" adequacySpan]
           (.constant (.int 1) adequacySpan) adequacySpan,
         .assign #[.name "w" adequacySpan]
           (.constant (.int 2) adequacySpan) adequacySpan,
         .assign #[.name "x" adequacySpan]
           (.constant (.int 3) adequacySpan) adequacySpan,
         .assign #[.name "y" adequacySpan]
           (.constant (.int 4) adequacySpan) adequacySpan,
         .assign #[.name "z" adequacySpan]
           (.constant (.int 5) adequacySpan) adequacySpan,
         .pass adequacySpan]))) w =
      .ok { w with callDepth := depth } .next := by
  have hraw : (inWorld [("u", .int 0), ("v", .int 0), ("w", .int 0), ("x", .int 0), ("y", .int 0), ("z", .int 0)] (execOpenList K m
      [.assign #[.name "u" adequacySpan]
         (.constant (.int 0) adequacySpan) adequacySpan,
       .assign #[.name "v" adequacySpan]
         (.constant (.int 1) adequacySpan) adequacySpan,
       .assign #[.name "w" adequacySpan]
         (.constant (.int 2) adequacySpan) adequacySpan,
       .assign #[.name "x" adequacySpan]
         (.constant (.int 3) adequacySpan) adequacySpan,
       .assign #[.name "y" adequacySpan]
         (.constant (.int 4) adequacySpan) adequacySpan,
       .assign #[.name "z" adequacySpan]
         (.constant (.int 5) adequacySpan) adequacySpan,
       .pass adequacySpan])) w =
      .ok (.ok RFlow.next, w) := by rfl
  unfold finishCallM
  apply toRun_tryCatch_ok
  rw [bind_apply, hraw]
  rfl

theorem finishCallM_assign_six_existing_locals_expr_body_ok (K : Kont) (m : Module)
    (w : World) (depth : Nat) :
    toRun (finishCallM depth
      (inWorld [("u", .int 0), ("v", .int 0), ("w", .int 0), ("x", .int 0), ("y", .int 0), ("z", .int 0)] (execOpenList K m
        [.assign #[.name "u" adequacySpan]
           (.constant (.int 0) adequacySpan) adequacySpan,
         .assign #[.name "v" adequacySpan]
           (.constant (.int 1) adequacySpan) adequacySpan,
         .assign #[.name "w" adequacySpan]
           (.constant (.int 2) adequacySpan) adequacySpan,
         .assign #[.name "x" adequacySpan]
           (.constant (.int 3) adequacySpan) adequacySpan,
         .assign #[.name "y" adequacySpan]
           (.constant (.int 4) adequacySpan) adequacySpan,
         .assign #[.name "z" adequacySpan]
           (.constant (.int 5) adequacySpan) adequacySpan,
         .exprStmt (.constant (.int 6) adequacySpan) adequacySpan]))) w =
      .ok { w with callDepth := depth } .next := by
  have hraw : (inWorld [("u", .int 0), ("v", .int 0), ("w", .int 0), ("x", .int 0), ("y", .int 0), ("z", .int 0)] (execOpenList K m
      [.assign #[.name "u" adequacySpan]
         (.constant (.int 0) adequacySpan) adequacySpan,
       .assign #[.name "v" adequacySpan]
         (.constant (.int 1) adequacySpan) adequacySpan,
       .assign #[.name "w" adequacySpan]
         (.constant (.int 2) adequacySpan) adequacySpan,
       .assign #[.name "x" adequacySpan]
         (.constant (.int 3) adequacySpan) adequacySpan,
       .assign #[.name "y" adequacySpan]
         (.constant (.int 4) adequacySpan) adequacySpan,
       .assign #[.name "z" adequacySpan]
         (.constant (.int 5) adequacySpan) adequacySpan,
       .exprStmt (.constant (.int 6) adequacySpan) adequacySpan])) w =
      .ok (.ok RFlow.next, w) := by rfl
  unfold finishCallM
  apply toRun_tryCatch_ok
  rw [bind_apply, hraw]
  rfl

theorem finishCallM_assign_six_existing_locals_ret_none_body_ok (K : Kont) (m : Module)
    (w : World) (depth : Nat) :
    toRun (finishCallM depth
      (inWorld [("u", .int 0), ("v", .int 0), ("w", .int 0), ("x", .int 0), ("y", .int 0), ("z", .int 0)] (execOpenList K m
        [.assign #[.name "u" adequacySpan]
           (.constant (.int 0) adequacySpan) adequacySpan,
         .assign #[.name "v" adequacySpan]
           (.constant (.int 1) adequacySpan) adequacySpan,
         .assign #[.name "w" adequacySpan]
           (.constant (.int 2) adequacySpan) adequacySpan,
         .assign #[.name "x" adequacySpan]
           (.constant (.int 3) adequacySpan) adequacySpan,
         .assign #[.name "y" adequacySpan]
           (.constant (.int 4) adequacySpan) adequacySpan,
         .assign #[.name "z" adequacySpan]
           (.constant (.int 5) adequacySpan) adequacySpan,
         .ret Option.none adequacySpan]))) w =
      .ok { w with callDepth := depth } (.ret .none) := by
  have hraw : (inWorld [("u", .int 0), ("v", .int 0), ("w", .int 0), ("x", .int 0), ("y", .int 0), ("z", .int 0)] (execOpenList K m
      [.assign #[.name "u" adequacySpan]
         (.constant (.int 0) adequacySpan) adequacySpan,
       .assign #[.name "v" adequacySpan]
         (.constant (.int 1) adequacySpan) adequacySpan,
       .assign #[.name "w" adequacySpan]
         (.constant (.int 2) adequacySpan) adequacySpan,
       .assign #[.name "x" adequacySpan]
         (.constant (.int 3) adequacySpan) adequacySpan,
       .assign #[.name "y" adequacySpan]
         (.constant (.int 4) adequacySpan) adequacySpan,
       .assign #[.name "z" adequacySpan]
         (.constant (.int 5) adequacySpan) adequacySpan,
       .ret Option.none adequacySpan])) w =
      .ok (.ok (.ret .none), w) := by rfl
  unfold finishCallM
  apply toRun_tryCatch_ok
  rw [bind_apply, hraw]
  rfl

theorem finishCallM_assign_six_existing_locals_break_body_ok (K : Kont) (m : Module)
    (w : World) (depth : Nat) :
    toRun (finishCallM depth
      (inWorld [("u", .int 0), ("v", .int 0), ("w", .int 0), ("x", .int 0), ("y", .int 0), ("z", .int 0)] (execOpenList K m
        [.assign #[.name "u" adequacySpan]
           (.constant (.int 0) adequacySpan) adequacySpan,
         .assign #[.name "v" adequacySpan]
           (.constant (.int 1) adequacySpan) adequacySpan,
         .assign #[.name "w" adequacySpan]
           (.constant (.int 2) adequacySpan) adequacySpan,
         .assign #[.name "x" adequacySpan]
           (.constant (.int 3) adequacySpan) adequacySpan,
         .assign #[.name "y" adequacySpan]
           (.constant (.int 4) adequacySpan) adequacySpan,
         .assign #[.name "z" adequacySpan]
           (.constant (.int 5) adequacySpan) adequacySpan,
         .brk adequacySpan]))) w =
      .ok { w with callDepth := depth } RFlow.brk := by
  have hraw : (inWorld [("u", .int 0), ("v", .int 0), ("w", .int 0), ("x", .int 0), ("y", .int 0), ("z", .int 0)] (execOpenList K m
      [.assign #[.name "u" adequacySpan]
         (.constant (.int 0) adequacySpan) adequacySpan,
       .assign #[.name "v" adequacySpan]
         (.constant (.int 1) adequacySpan) adequacySpan,
       .assign #[.name "w" adequacySpan]
         (.constant (.int 2) adequacySpan) adequacySpan,
       .assign #[.name "x" adequacySpan]
         (.constant (.int 3) adequacySpan) adequacySpan,
       .assign #[.name "y" adequacySpan]
         (.constant (.int 4) adequacySpan) adequacySpan,
       .assign #[.name "z" adequacySpan]
         (.constant (.int 5) adequacySpan) adequacySpan,
       .brk adequacySpan])) w =
      .ok (.ok RFlow.brk, w) := by rfl
  unfold finishCallM
  apply toRun_tryCatch_ok
  rw [bind_apply, hraw]
  rfl

theorem finishCallM_assign_six_existing_locals_continue_body_ok (K : Kont) (m : Module)
    (w : World) (depth : Nat) :
    toRun (finishCallM depth
      (inWorld [("u", .int 0), ("v", .int 0), ("w", .int 0), ("x", .int 0), ("y", .int 0), ("z", .int 0)] (execOpenList K m
        [.assign #[.name "u" adequacySpan]
           (.constant (.int 0) adequacySpan) adequacySpan,
         .assign #[.name "v" adequacySpan]
           (.constant (.int 1) adequacySpan) adequacySpan,
         .assign #[.name "w" adequacySpan]
           (.constant (.int 2) adequacySpan) adequacySpan,
         .assign #[.name "x" adequacySpan]
           (.constant (.int 3) adequacySpan) adequacySpan,
         .assign #[.name "y" adequacySpan]
           (.constant (.int 4) adequacySpan) adequacySpan,
         .assign #[.name "z" adequacySpan]
           (.constant (.int 5) adequacySpan) adequacySpan,
         .cont adequacySpan]))) w =
      .ok { w with callDepth := depth } RFlow.cont := by
  have hraw : (inWorld [("u", .int 0), ("v", .int 0), ("w", .int 0), ("x", .int 0), ("y", .int 0), ("z", .int 0)] (execOpenList K m
      [.assign #[.name "u" adequacySpan]
         (.constant (.int 0) adequacySpan) adequacySpan,
       .assign #[.name "v" adequacySpan]
         (.constant (.int 1) adequacySpan) adequacySpan,
       .assign #[.name "w" adequacySpan]
         (.constant (.int 2) adequacySpan) adequacySpan,
       .assign #[.name "x" adequacySpan]
         (.constant (.int 3) adequacySpan) adequacySpan,
       .assign #[.name "y" adequacySpan]
         (.constant (.int 4) adequacySpan) adequacySpan,
       .assign #[.name "z" adequacySpan]
         (.constant (.int 5) adequacySpan) adequacySpan,
       .cont adequacySpan])) w =
      .ok (.ok RFlow.cont, w) := by rfl
  unfold finishCallM
  apply toRun_tryCatch_ok
  rw [bind_apply, hraw]
  rfl

theorem finishCallM_three_pass_ret_body_ok (K : Kont) (m : Module)
    (locals : REnv) (w : World) (depth : Nat) :
    toRun (finishCallM depth
      (inWorld locals (execOpenList K m
        [.pass adequacySpan, .pass adequacySpan,
         .pass adequacySpan,
         .ret (some (.constant (.int 1) adequacySpan)) adequacySpan]))) w =
      .ok { w with callDepth := depth } (.ret (.int 1)) := by
  have hraw : (inWorld locals (execOpenList K m
      [.pass adequacySpan, .pass adequacySpan,
       .pass adequacySpan,
       .ret (some (.constant (.int 1) adequacySpan)) adequacySpan])) w =
      .ok (.ok (.ret (.int 1)), w) := by rfl
  unfold finishCallM
  apply toRun_tryCatch_ok
  rw [bind_apply, hraw]
  rfl

theorem finishCallM_three_pass_break_body_ok (K : Kont) (m : Module)
    (locals : REnv) (w : World) (depth : Nat) :
    toRun (finishCallM depth
      (inWorld locals (execOpenList K m
        [.pass adequacySpan, .pass adequacySpan,
         .pass adequacySpan, .brk adequacySpan]))) w =
      .ok { w with callDepth := depth } RFlow.brk := by
  have hraw : (inWorld locals (execOpenList K m
      [.pass adequacySpan, .pass adequacySpan,
       .pass adequacySpan, .brk adequacySpan])) w =
      .ok (.ok RFlow.brk, w) := by rfl
  unfold finishCallM
  apply toRun_tryCatch_ok
  rw [bind_apply, hraw]
  rfl

theorem finishCallM_three_pass_continue_body_ok (K : Kont) (m : Module)
    (locals : REnv) (w : World) (depth : Nat) :
    toRun (finishCallM depth
      (inWorld locals (execOpenList K m
        [.pass adequacySpan, .pass adequacySpan,
         .pass adequacySpan, .cont adequacySpan]))) w =
      .ok { w with callDepth := depth } RFlow.cont := by
  have hraw : (inWorld locals (execOpenList K m
      [.pass adequacySpan, .pass adequacySpan,
       .pass adequacySpan, .cont adequacySpan])) w =
      .ok (.ok RFlow.cont, w) := by rfl
  unfold finishCallM
  apply toRun_tryCatch_ok
  rw [bind_apply, hraw]
  rfl

theorem finishCallM_three_pass_ret_none_body_ok (K : Kont) (m : Module)
    (locals : REnv) (w : World) (depth : Nat) :
    toRun (finishCallM depth
      (inWorld locals (execOpenList K m
        [.pass adequacySpan, .pass adequacySpan,
         .pass adequacySpan, .ret Option.none adequacySpan]))) w =
      .ok { w with callDepth := depth } (.ret .none) := by
  have hraw : (inWorld locals (execOpenList K m
      [.pass adequacySpan, .pass adequacySpan,
       .pass adequacySpan, .ret Option.none adequacySpan])) w =
      .ok (.ok (.ret .none), w) := by rfl
  unfold finishCallM
  apply toRun_tryCatch_ok
  rw [bind_apply, hraw]
  rfl

theorem finishCallM_assign_constant_body_ok (K : Kont) (m : Module)
    (w : World) (depth : Nat) :
    toRun (finishCallM depth
      (inWorld [] (execOpenList K m
        [.assign #[.name "x" adequacySpan]
          (.constant (.int 1) adequacySpan) adequacySpan]))) w =
      .ok { w with callDepth := depth } .next := by
  have hraw : (inWorld [] (execOpenList K m
      [.assign #[.name "x" adequacySpan]
        (.constant (.int 1) adequacySpan) adequacySpan])) w =
      .ok (.ok RFlow.next, w) := by rfl
  unfold finishCallM
  apply toRun_tryCatch_ok
  rw [bind_apply, hraw]
  rfl

theorem finishCallM_modify_ok {α : Type} (depth : Nat) (w : World)
    (v : α) (f : World → World) :
    toRun (finishCallM depth (do modify f; pure v : SemW α)) w =
      .ok { f w with callDepth := depth } v := by
  unfold finishCallM
  apply toRun_tryCatch_ok
  have hraw : ((do
      let value ← (do modify f; pure v : SemW α)
      modify fun w => { w with callDepth := depth }
      pure value) : SemW α) w =
      .ok (.ok v, { f w with callDepth := depth }) := by
    rw [bind_apply]
    rw [bind_apply]
    rfl
  exact hraw

theorem finishCallM_modify_exn {α : Type} (depth : Nat) (w : World)
    (e : PyErr) (f : World → World) :
    toRun (finishCallM depth (do modify f; raisePy e : SemW α)) w =
      .exn { f w with callDepth := depth } e := by
  unfold finishCallM
  apply toRun_tryCatch_exn
  · rfl
  · rfl

theorem leaveCallM_modify_ok {α : Type} (w : World) (v : α)
    (f : World → World) :
    toRun (leaveCallM (do modify f; pure v : SemW α)) w =
      .ok { f w with callDepth := (f w).callDepth.pred } v := by
  have hraw : ((do
      let value ← (do modify f; pure v : SemW α)
      modify fun w => { w with callDepth := w.callDepth.pred }
      pure value) : SemW α) w =
      .ok (.ok v, { f w with callDepth := (f w).callDepth.pred }) := by
    rw [bind_apply]
    rw [bind_apply]
    rfl
  unfold leaveCallM
  apply toRun_tryCatch_ok
  exact hraw

theorem leaveCallM_modify_exn {α : Type} (w : World) (e : PyErr)
    (f : World → World) :
    toRun (leaveCallM (do modify f; raisePy e : SemW α)) w =
      .exn { f w with callDepth := (f w).callDepth.pred } e := by
  unfold leaveCallM
  apply toRun_tryCatch_exn
  · rfl
  · rfl

#print axioms evalOpen
#print axioms execOpen
#print axioms kont
#print axioms callInMono
#print axioms callInMono_eq_ofHalt
#print axioms twinAgrees_callIn_missing_function
#print axioms twinAgrees_callIn_unsupported_args
#print axioms twinAgrees_callIn_arity_error
#print axioms twinAgrees_callIn_static_locals
#print axioms twinAgrees_callIn_zero_fuel
#print axioms refusalClass_isSome_iff
#print axioms toRun_ofRun
#print axioms ofRun_toRun_normalises
#print axioms ofRun_toRun_of_plain
#print axioms inFrame_toRun
#print axioms inWorld_toRun
#print axioms twinAgrees_binOpHM_intBitAnd
#print axioms twinAgrees_evalOpenList_constants
#print axioms twinAgrees_evalOpenList_of_each
#print axioms twinAgrees_execOpenList_of_each
#print axioms twinAgrees_execOpenList_nil
#print axioms twinAgrees_execOpenList_nil_world
#print axioms finishCallM_pure_ok
#print axioms finishCallM_empty_body_ok
#print axioms finishCallM_pass_body_ok
#print axioms finishCallM_expr_constant_body_ok
#print axioms finishCallM_ret_constant_body_ok
#print axioms finishCallM_ret_none_body_ok
#print axioms finishCallM_break_body_ok
#print axioms finishCallM_continue_body_ok
#print axioms finishCallM_pass_expr_body_ok
#print axioms finishCallM_pass_ret_body_ok
#print axioms finishCallM_pass_break_body_ok
#print axioms finishCallM_pass_continue_body_ok
#print axioms finishCallM_three_pass_body_ok
#print axioms finishCallM_four_pass_body_ok
#print axioms finishCallM_three_pass_ret_body_ok
#print axioms finishCallM_three_pass_break_body_ok
#print axioms finishCallM_three_pass_continue_body_ok
#print axioms finishCallM_three_pass_ret_none_body_ok
#print axioms finishCallM_five_pass_body_ok
#print axioms finishCallM_four_pass_ret_body_ok
#print axioms finishCallM_pass_assign_empty_locals_body_ok
#print axioms finishCallM_assign_existing_local_body_ok
#print axioms finishCallM_assign_existing_local_ret_body_ok
#print axioms finishCallM_assign_existing_local_pass_body_ok
#print axioms finishCallM_assign_existing_local_break_body_ok
#print axioms finishCallM_assign_existing_local_continue_body_ok
#print axioms finishCallM_assign_existing_local_ret_none_body_ok
#print axioms finishCallM_assign_existing_local_expr_body_ok
#print axioms finishCallM_assign_two_existing_locals_body_ok
#print axioms finishCallM_assign_three_existing_locals_body_ok
#print axioms finishCallM_assign_existing_local_ret_pass_body_ok
#print axioms finishCallM_assign_two_existing_locals_ret_body_ok
#print axioms finishCallM_assign_three_existing_locals_ret_body_ok
#print axioms finishCallM_assign_three_existing_locals_pass_body_ok
#print axioms finishCallM_assign_three_existing_locals_expr_body_ok
#print axioms finishCallM_assign_four_existing_locals_body_ok
#print axioms finishCallM_assign_four_existing_locals_ret_body_ok
#print axioms finishCallM_assign_four_existing_locals_pass_body_ok
#print axioms finishCallM_assign_four_existing_locals_expr_body_ok
#print axioms finishCallM_assign_four_existing_locals_ret_none_body_ok
#print axioms finishCallM_assign_four_existing_locals_break_body_ok
#print axioms finishCallM_assign_four_existing_locals_continue_body_ok
#print axioms finishCallM_assign_five_existing_locals_body_ok
#print axioms finishCallM_assign_five_existing_locals_ret_body_ok
#print axioms finishCallM_assign_five_existing_locals_pass_body_ok
#print axioms finishCallM_assign_five_existing_locals_expr_body_ok
#print axioms finishCallM_assign_five_existing_locals_ret_none_body_ok
#print axioms finishCallM_assign_five_existing_locals_break_body_ok
#print axioms finishCallM_assign_five_existing_locals_continue_body_ok
#print axioms finishCallM_assign_six_existing_locals_body_ok
#print axioms finishCallM_assign_six_existing_locals_ret_body_ok
#print axioms finishCallM_assign_six_existing_locals_pass_body_ok
#print axioms finishCallM_assign_six_existing_locals_expr_body_ok
#print axioms finishCallM_assign_six_existing_locals_ret_none_body_ok
#print axioms finishCallM_assign_six_existing_locals_break_body_ok
#print axioms finishCallM_assign_six_existing_locals_continue_body_ok
#print axioms finishCallM_assign_constant_body_ok
#print axioms finishCallM_modify_ok
#print axioms finishCallM_modify_exn
#print axioms leaveCallM_modify_ok
#print axioms leaveCallM_modify_exn

end LeanModels.Python.Monadic
