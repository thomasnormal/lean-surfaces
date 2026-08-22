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
  | some (.ref _) => .notYetArm "call: a callable bound in locals (closure/H7)"
  | some v => .notCallable v.typeName
  | Option.none =>
    match lookupG (moduleGlobals m).1 fname with
    | some (some (.ref _)) => .notCallable "dict"
    | some (some v) => .notCallable v.typeName
    | some Option.none => .notYetArm s!"call: statically-poisoned module binding '{fname}'"
    | Option.none =>
      if (findFunction m fname).isSome then
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
            else if hasExtraDunder c then
              .preRefuse s!"class '{fname}' defines dunder methods beyond __init__ — implicit-protocol dispatch is outside the H3 tier"
            else if (findFunction m (fname ++ ".__init__")).isSome then
              .preRefuse s!"'__init__' on the namedtuple subclass '{fname}' (immutable self) is outside the tier"
            else .ntMake nt.name nt.fields
          | Option.none =>
            if !c.ok then
              .preRefuse s!"class '{fname}' uses unsupported features (bases/metaclass/decorators/class-level statements) — instantiation is outside the H3 tier"
            else if hasExtraDunder c then
              .preRefuse s!"class '{fname}' defines dunder methods beyond __init__ — implicit-protocol dispatch is outside the H3 tier"
            else .instantiate ci fname (findFunction m (fname ++ ".__init__")).isSome
      | Option.none =>
      match findNamedTuple m fname with
      | some nt => .ntMake nt.tname nt.fields
      | Option.none =>
      if fname == "input" then
        -- The ONE builtin that refuses BEFORE its arguments evaluate: stdin is
        -- a runner-boundary effect, and the trunk refuses at the dispatch.
        .preRefuse "input() is outside the tier (stdin is a runner-boundary effect; docs/memory-model.md §effects)"
      else if isBuiltinName fname then .builtin fname
      else if isModuleDunder fname then
        .preRefuse s!"module attribute '{fname}' is bound by the import machinery, not by a statement — outside the G1 tier"
      else
        match Env.lookup globals fname with
        | some _ => .notYetArm s!"call: live module binding '{fname}'"
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
  | .tuple xs => pure xs.toList
  | .ntuple _ _ xs => pure xs.toList
  | .listV xs => pure xs.toList
  | .rangeV lo hi step => liftRes (rangeVals lo hi step)
  | .ref a => do
      match Heap.get? (← frameHeap) a with
      | some (.list xs) => pure xs.toList
      | some (.generator ..) =>
          if guardGen && moduleGenFree m then
            refuse s!"{fname}() over a generator DRAINS it (a stateful read) — outside the tier"
          else do
            inFrame (K.drainIter a)
      | some (.dict _ _) =>
          refuse s!"{fname}() over dict keys is outside the tier (live dict iteration; docs/memory-model.md)"
      | some (.pyset _) =>
          refuse s!"{fname}() over a set is outside the tier (hash order; docs/memory-model.md)"
      | some (.instance _ _) => raisePy (.typeError "'object' object is not iterable")
      | some (.cell _) => refuse cellInternal
      | some (.closure ..) => raisePy (.typeError "'function' object is not iterable")
      | Option.none => refuse danglingMsg
  | v => raisePy (.typeError s!"'{v.typeName}' object is not iterable")

/-- The builtin table. `isBuiltinName` (Ast.lean) is the AUTHORITATIVE
implemented set — 22 names — so a name reaching here is one the tier claims, and
a name it does not claim can never fall silently past the table. Arguments are
already values: `input` is the one builtin that refuses before they evaluate, and
it is handled in the PLAN, not here. -/
def applyBuiltin (K : Kont) (m : Module) (fname : String) (vs : List RVal) :
    SemF RVal := do
  if fname == "len" then
    match vs with
    | [v] => lenM v
    | _ => raisePy (.typeError s!"len() takes exactly one argument ({vs.length} given)")
  else if fname == "abs" then
    match vs with
    | [v] => liftRes (absVal v)
    | _ => raisePy (.typeError s!"abs() takes exactly one argument ({vs.length} given)")
  else if fname == "int" then
    match vs with
    | [] => pure (.int 0)
    | [v] => liftRes (intCastVal v)
    | _ => refuse "int() with a base argument is outside the v0 tier"
  else if fname == "ord" then
    match vs with
    | [v] => liftRes (ordVal v)
    | vs => raisePy (.typeError s!"ord() takes exactly one argument ({vs.length} given)")
  else if fname == "chr" then
    match vs with
    | [v] => liftRes (chrVal v)
    | vs => raisePy (.typeError s!"chr() takes exactly one argument ({vs.length} given)")
  else if fname == "str" then
    match vs with
    | [] => pure (.str "")
    | [v] => do liftRes (strOfValH (← frameHeap) v)
    | _ => refuse "str() with encoding/errors arguments is outside the tier (bytes decoding is not guessed; docs/memory-model.md §the cast tier)"
  else if fname == "print" then
    -- THE ONE EFFECT: stdout is `World` data, so `print` is an ORDINARY builtin
    -- here — reached only after every shadowing arm, so it works inside function
    -- bodies. It returns `None` and appends exactly one chunk.
    match strOfArgs (← frameHeap) vs with
    | some line => do emit line; pure .none
    | Option.none =>
        refuse "print() of a value the tier cannot render EXACTLY: a set (hash order), an instance/closure/generator (identity), a non-ASCII string (Unicode printability is never guessed), or a structure deeper than the repr budget — docs/memory-model.md §effects"
  else if fname == "range" then
    liftRes (rangeMake (← frameHeap) vs)
  else if fname == "max" || fname == "min" then
    match vs with
    | [.ref _] => notYet s!"builtin: {fname}() over a heap referent"
    | vs => do liftRes (extremumValH (← frameHeap) (fname == "max") vs)
  else if fname == "sorted" then
    match vs with
    | [.ref a] => do
        match Heap.get? (← frameHeap) a with
        | some (.generator ..) => notYet "builtin: sorted() over a generator (H6)"
        | _ => do
            let hr ← liftRes (sortedValH (← frameHeap) (.ref a))
            heapPut hr.1; pure hr.2
    | [v] => do
        let hr ← liftRes (sortedValH (← frameHeap) v)
        heapPut hr.1; pure hr.2
    | _ => raisePy (.typeError s!"sorted expected 1 argument, got {vs.length}")
  else if fname == "sum" then
    -- The element fold IS `evalBinOp .add` (`sumFold`); a str START is
    -- CPython's own special-cased refusal, not a guess.
    match sumArgs vs with
    | Option.none =>
        raisePy (.typeError s!"sum() takes at most 2 arguments ({vs.length} given)")
    | some (v, start) =>
      match start with
      | .str _ =>
          raisePy (.typeError "sum() can't sum strings [use ''.join(seq) instead]")
      | start => do
          let xs ← iterValues K m "sum" true v
          liftRes (sumFold start xs)
  else if fname == "tuple" then
    -- An IMMEDIATE value: `tuple()` allocates nothing.
    match vs with
    | [] => pure (.tuple #[])
    | [v] => do
        let xs ← iterValues K m "tuple" true v
        pure (.tuple xs.toArray)
    | vs => raisePy (.typeError s!"tuple expected at most 1 argument, got {vs.length}")
  else if fname == "list" then
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
        if isGen then notYet s!"builtin: {fname}() over a generator (H6 anyAllIter)"
        else do
          let xs ← iterValues K m fname true v
          let b ← liftRes (anyAllScan (← frameHeap) (fname == "all") xs)
          pure (.bool b)
    | vs => raisePy (.typeError s!"{fname}() takes exactly one argument ({vs.length} given)")
  else notYet s!"builtin: {fname}()"

/-- Apply a resolved plan to already-evaluated arguments. Not mutual with the
evaluator: the arguments are values, so nothing here evaluates syntax. -/
def applyCallPlan (K : Kont) (m : Module) : CallPlan → List RVal → SemF RVal
  | .preRefuse msg,   _  => refuse msg
  | .preNameError n,  _  => raisePy (.nameError n)
  | .notCallable t,   _  => raisePy (.typeError s!"'{t}' object is not callable")
  | .notYetArm arm,   _  => notYet arm
  | .builtin name,    vs => applyBuiltin K m name vs
  | .modFun qname,    vs => inFrame (K.call qname vs.toArray)
  | .ntMake tn flds,  vs =>
      -- Wrong arity is the faithful TypeError (CPython raises it through
      -- `tuple.__new__`); nothing allocates, so the world is exactly the
      -- arguments'.
      if vs.length == flds.size then pure (.ntuple tn flds vs.toArray)
      else raisePy (.typeError (ntArityErrorMsg flds vs.length))
  | .instantiate ci cname hasInit, vs =>
      if hasInit then do
        let a ← heapPush (.instance ci #[])
        let r ← inFrame (K.call (cname ++ ".__init__") ((RVal.ref a :: vs).toArray))
        match r with
        | .none => pure (.ref a)
        -- CPython checks `__init__`'s result: non-None raises.
        | r => raisePy (.typeError s!"__init__() should return None, not '{r.typeName}'")
      else
        match vs with
        -- The arity error fires BEFORE the allocation, so the failing run's
        -- world is the caller's untouched — the trunk raises from `st`, not
        -- from the post-allocation `st'`.
        | [] => do let a ← heapPush (.instance ci #[]); pure (.ref a)
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
      let h ← frameHeap
      match vs with
      | [k] => liftRes (heapGet h a k .none)
      | [k, d] => liftRes (heapGet h a k d)
      | vs => raisePy (.typeError s!"get expected at most 2 arguments, got {vs.length}")
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
  | .listAppend, vs =>
      match vs with
      | [v] => do
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
def applyStrMethod (sv : String) : StrPlan → List RVal → SemF RVal
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
      | vs =>
          if vs.length ≤ 3 then
            refuse "str.index() with start/end arguments is outside the tier (docs/memory-model.md §string semantics)"
          else raisePy (.typeError s!"index expected at most 3 arguments, got {vs.length}")
  | .refuse msg, _ => refuse msg

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
      envSet id r
      pure r
  | .name id _ => do
      -- Resolution order (LOAD-BEARING): local env → module globals (G1) →
      -- module function table → builtins → NameError, the last only when the
      -- globals are COMPLETE, else loudly unsupported.
      match ← envGet id with
      | some v => pure v
      | Option.none =>
        match lookupG (moduleGlobals m).1 id with
        | some (some v) => pure v
        | some Option.none =>
            -- a statically-POISONED name consults the LIVE view before refusing
            match Env.lookup (← frameGlobals) id with
            | some v => pure v
            | Option.none =>
                refuse s!"module-level value of '{id}' is outside the G1 tier"
        | Option.none =>
          if (findFunction m id).isSome then
            refuse s!"referencing function '{id}' as a value is outside the v0 tier"
          else if (findClass m id).isSome then
            refuse s!"referencing class '{id}' as a value is outside the H3 tier (classes are called, not passed)"
          else if (findNamedTuple m id).isSome then
            refuse s!"referencing namedtuple class '{id}' as a value is outside the tier (namedtuple classes are called, not passed)"
          else if isBuiltinName id then
            refuse s!"referencing builtin '{id}' as a value is outside the v0 tier"
          else if isModuleDunder id then
            refuse s!"module attribute '{id}' is bound by the import machinery, not by a statement — outside the G1 tier"
          else
            -- the statically-ABSENT arm consults the live view before deciding
            match Env.lookup (← frameGlobals) id with
            | some v => pure v
            | Option.none =>
              if isPyBuiltinName id then refuse (unmodelledBuiltinMsg id)
              else if (moduleGlobals m).2 then raisePy (.nameError id)
              else refuse s!"name '{id}' may be bound by an out-of-tier module-level statement"
  | .binOp l op r _ => do
      let a ← evalOpen K m l
      let b ← evalOpen K m r
      binOpM op a b
  | .unaryOp op operand _ => do
      let v ← evalOpen K m operand
      unaryOpM op v
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
              match callNamePlan m st.locals st.world.globals fname with
              | .preRefuse msg => refuse msg
              | .preNameError n => raisePy (.nameError n)
              | plan => do
                  let vs ← evalOpenList K m args.toList
                  applyCallPlan K m plan vs
          | .attribute recv attr _ => do
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
                      let vs ← evalOpenList K m args.toList
                      applyAttrPlan K a attr plan vs
              | .ntuple tn fs xs =>
                  -- namedtuple SUBCLASS method dispatch: methods ARE functions,
                  -- `self` is the ntuple VALUE. The plan precedes the arguments.
                  match ntupleCallPlan m tn fs attr with
                  | .instMethod qname => do
                      let vs ← evalOpenList K m args.toList
                      inFrame (K.call qname ((RVal.ntuple tn fs xs :: vs).toArray))
                  | .attrMissing => raisePy .attributeError
                  | .refuse msg => refuse msg
                  | _ => refuse "internal: namedtuple call plan out of range (report this)"
              | .str sv => do
                  let vs ← evalOpenList K m args.toList
                  applyStrMethod sv (strCallPlan attr) vs
              | r =>
                  refuse s!"method call '.{attr}' on '{r.typeName}' is outside the tier (heap receivers only; docs/memory-model.md)"
          | f => refuse s!"calling a non-name expression ('{f.kindName}') is outside the v0 tier"
        else notYet "call: keyword arguments (H6)"
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
      | r =>
          refuse s!"attribute access on '{r.typeName}' is outside the tier (heap receivers only; docs/memory-model.md)"
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
      sliceM cv lv uv sv
  | .genExp .. =>
      refuse "this generator expression is outside the tier (ingestion could not lower it to a generator function; docs/memory-model.md §generator semantics)"
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
      let b ← liftRes (evalCompareOpH h K.fuel op lhs rhs)
      if b then evalCompareChainM K m rhs ops' rest else pure (.bool false)
  | _, _ => refuse "Compare with mismatched ops/comparators"
  termination_by structural _ops es => es

end

/-! ## §2 THE FUEL-FREE STATEMENT HALF — structural on `Stmt` -/

mutual

/-- Execute one statement. Structural on `Stmt`; `while` and the `for` cursors
go out through `K` because their recursion is not structural. -/
def execOpen (K : Kont) (m : Module) : Stmt → SemF RFlow
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
              let h' ← liftRes (heapAttrStore (← frameHeap) a attr v)
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
            let he ← liftRes (unpackStoreH st.world.heap st.locals elts.toList xs)
            modify fun st => { st with world := { st.world with heap := he.1 }, locals := he.2 }
            pure .next
      | [t] => do
          let v ← evalOpen K m value
          assignM t v
          pure .next
      | _ => refuse "chained assignment (multiple targets) is outside the v0 tier"
  | .augAssign target op value _ =>
      match target with
      | .name id _ => do
          -- CPython order: the target is LOADED before the value is evaluated.
          match ← envGet id with
          | Option.none => raisePy (.nameError id)
          | some (.listV _) =>
              refuse "augmented assignment to a list ('+=' mutates in place, visible through aliases) is outside the v0 tier"
          | some (.ref _) =>
              refuse "augmented assignment to a heap object is outside the H1 tier (docs/memory-model.md)"
          | some old => do
              let v ← evalOpen K m value
              let r ← binOpM op old v
              envSet id r
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
              | .ref _ =>
                  refuse "augmented assignment to a heap-valued attribute is outside the tier (docs/memory-model.md §bound() end-to-end)"
              | old => do
                  let v ← evalOpen K m value
                  let res ← binOpM op old v
                  let h' ← liftRes (heapAttrStore (← frameHeap) a attr res)
                  heapPut h'; pure .next
          | _ => raisePy .attributeError
      | t => refuse s!"augmented assignment to '{t.kindName}' is outside the v0 tier"
  | .whileLoop test body orelse _ => K.whileLoop test body.toList orelse.toList
  | .forStmt target iter body orelse _ =>
      match orelse.toList with
      | [] => do
          let it ← evalOpen K m iter
          match it with
          | .listV xs => K.forSeq target xs.toList body.toList
          | .tuple xs => K.forSeq target xs.toList body.toList
          | .ntuple _ _ xs => K.forSeq target xs.toList body.toList
          -- H5 iteration: a str iterates its CODE POINTS; the snapshot IS the
          -- live semantics (strs are immutable).
          | .str s => K.forSeq target (strCharVals s) body.toList
          | .rangeV lo hi step => do
              let xs ← liftRes (rangeVals lo hi step)
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
  | .unsupported pyKind _ _ => refuse s!"unsupported statement '{pyKind}'"
  | .yieldStmt _ _ =>
      refuse "'yield' outside a generator body (the def is not marked `is_generator`) — outside the tier"
  | .yieldFromStmt .. =>
      refuse "un-lowered 'yield from' (the iterable is not an admitted genexp, or the genexp's target occurs elsewhere in the body) — outside the tier (docs/memory-model.md §yield from)"
  | .defStmt .. => notYet "statement: nested def / closure (H7)"
  | .raiseStmt exc cause _ =>
      -- The admitted shape is `raise N` of an admitted exception class,
      -- resolved to its class IDENTITY. The name must resolve UNAMBIGUOUSLY:
      -- any local/global/def shadow refuses, because CPython would raise the
      -- shadow's value.
      match cause with
      | some _ =>
          refuse "'raise … from …' (exception chaining) is outside the tier (docs/memory-model.md §exceptions)"
      | Option.none =>
        match exc with
        | Option.none =>
            refuse "bare 'raise' (re-raise of the active exception) is outside the tier (docs/memory-model.md §exceptions)"
        | some (.name id _) => do
            let st ← get
            if (Env.lookup st.locals id).isSome
                || (lookupG (moduleGlobals m).1 id).isSome
                || (Env.lookup st.world.globals id).isSome
                || (findFunction m id).isSome then
              refuse s!"'raise {id}': the name is shadowed by a local/global/def binding — outside the tier (docs/memory-model.md §exceptions)"
            else
              match findClass m id with
              | some (ci, c) =>
                  if c.isExc then raisePy (.user ci c.name)
                  else refuse s!"'raise {id}': only an admitted exception class (`class N(Exception): pass`) can be raised — outside the tier (docs/memory-model.md §exceptions)"
              | Option.none =>
                  refuse s!"'raise {id}': only an admitted exception class name can be raised — outside the tier (docs/memory-model.md §exceptions)"
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
        | Option.none => raisePy (.assertionError Option.none)
        | some e => do
            let v ← evalOpen K m e
            match printOne (← frameHeap) v with
            | some rendered => raisePy (.assertionError (some rendered))
            | Option.none =>
                refuse "assert message: the tier cannot render this value EXACTLY — a set (hash order), an instance/closure/generator (identity), a non-ASCII string (Unicode printability is never guessed), or a structure deeper than the repr budget — docs/memory-model.md §the assert statement"
  | .delStmt names _ => do
      -- `delNames` threads the locals left to right, so the PARTIAL effect is
      -- kept: earlier removals are already applied when a later target misses.
      let st ← get
      match delNames st.locals names.toList with
      | (env, Option.none) => do envPut env; pure .next
      | (_, some n) =>
          refuse s!"'del {n}': the name is not a bound local — CPython raises UnboundLocalError here and the model never invents one (docs/memory-model.md §the del statement)"
  | .tryStmt body excName handler tryUnsupported _ =>
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
        if (Env.lookup st.locals excName).isSome
            || (lookupG (moduleGlobals m).1 excName).isSome
            || (Env.lookup st.world.globals excName).isSome
            || (findFunction m excName).isSome then
          refuse s!"'except {excName}:': the name is shadowed by a local/global/def binding — outside the tier (docs/memory-model.md §exceptions)"
        else
          match findClass m excName with
          | Option.none =>
              -- The pinned two-name import-error table, consulted only after
              -- `findClass` missed, so a user class named `ImportError` wins.
              if importErrorHandlerMatch excName then
                tryCatch (execOpenList K m body.toList) (fun e =>
                  match e with
                  | .importError _ => execOpenList K m handler.toList
                  | e => raisePy e)
              else
                refuse s!"'except {excName}:': only an admitted exception class (`class N(Exception): pass`) or the pinned import-error names (`ImportError`/`ModuleNotFoundError` — docs/memory-model.md §import forms) can be matched — wider builtin-name matching is outside the tier (docs/memory-model.md §exceptions)"
          | some (ci, c) =>
              if !c.isExc then
                refuse s!"'except {excName}:': class '{excName}' is not an admitted exception class — outside the tier (docs/memory-model.md §exceptions)"
              else
                tryCatch (execOpenList K m body.toList) (fun e =>
                  match e with
                  | .user cid _ =>
                      if cid == ci then execOpenList K m handler.toList else raisePy e
                  | e => raisePy e)
  | .importFrom mod _ _ _ => notYet s!"statement: from {mod} import …"
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

/-! ## §2.5 THE DICT LOCKSTEP — the one walk that could not be a block member

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

/-! ## §3 THE FUELED KNOT — structural on FUEL, and the only place fuel is spent -/

/-- Enter a module-level function. The guard ORDER is the trunk's: parameter
features, then the static-locals rule, then arity, then the generator fork. -/
def callInM (K : Kont) (m : Module) (fname : String) (args : Array RVal) : SemW RVal :=
  match findFunction m fname with
  | Option.none => raisePy (.nameError fname)
  | some f =>
    if !f.argsOk then
      refuse s!"function '{fname}' uses unsupported parameter features (non-literal defaults/varargs/kwargs/decorators)"
    else if !f.localsOk then
      refuse s!"function '{fname}' calls a name it also assigns (CPython static-locals rule) — outside the v0 tier"
    else if !arityOk f.params args.size then
      raisePy (.typeError (arityErrorMsg fname (paramArity f.params) args.size))
    else if f.isGenerator then
      notYetW "call: generator function (H4)"
    else do
      let flow ← inWorld (mkCallEnv f.params args) (execOpenList K m f.body.toList)
      match flow with
      | .ret v => pure v
      | .next  => pure .none
      | .brk   => refuse "'break' outside loop"
      | .cont  => refuse "'continue' outside loop"

/-- The fueled operations at each fuel level. `kont m 0` is `Kont.bottom` —
every operation `.timeout`s — which is what makes fuel exhaustion loud rather
than wrong, and makes "the rebuild's only `.timeout` source" a checkable claim. -/
def kont (m : Module) : Nat → Kont
  | 0 => Kont.bottom
  | fuel + 1 =>
    let K := kont m fuel
    { fuel := fuel
      call := fun fname args => callInM K m fname args
      callClo := fun _ _ => notYetW "call: closure (H7)"
      dictItems := dictItemsAt K m
      whileLoop := fun test body orelse => do
          let t ← evalOpen K m test
          let b ← truthyM t
          if b then
            match ← execOpenList K m body with
            | .next | .cont => K.whileLoop test body orelse
            | .brk => pure .next
            | .ret v => pure (.ret v)
          else execOpenList K m orelse
      forSeq := fun target xs body =>
          match xs with
          | [] => pure .next
          | x :: rest => do
              assignM target x
              match ← execOpenList K m body with
              | .next | .cont => K.forSeq target rest body
              | .brk => pure .next
              | .ret v => pure (.ret v)
      forList := fun target a i body => do
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
          | some (.dict _ _) =>
              refuse "'for' over a dict is outside the tier (live dict iteration is deliberately NOT in the inventory — no snapshot shortcut; docs/memory-model.md)"
          | some (.instance _ _) => raisePy (.typeError "'object' object is not iterable")
          | some (.generator ..) => notYet "for: generator cursor (H4)"
          | some (.cell _) => refuse cellInternal
          | some (.closure ..) => refuse "internal: a list cursor over a function object (report this)"
          | some (.pyset _) => refuse "internal: a list cursor over a set (report this)"
          | Option.none => refuse danglingMsg
      stepIter := fun _ => notYetW "generator: stepIter (H4)"
      drainIter := fun _ => notYetW "generator: drainIter (H4/H6)"
      anyAllIter := fun _ _ => notYetW "generator: anyAllIter (H6)" }
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
  toRun ((kont m fuel).call fname args) w

/-! ## §5 NON-VACUITY FIRST — the rebuild RUNS, and the KERNEL decides it

The fuel ruling's whole claim is that both halves stay kernel-reducible. That is
a property to CHECK, not to assert: `#guard` is `Decidable.decide` plus `rfl`, so
a well-founded fallback would fail these outright. -/

private def sp0 : Span := ⟨0, 0, 0, 0⟩
private def emptyModule : Module := { functions := #[], classes := #[], namedtuples := #[], topLevel := #[] }
private def K0 : Kont := kont emptyModule 64
private def st0 : FrameState := ⟨{ heap := #[], globals := [] }, [("x", .int 7)]⟩

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
             "Stop"
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
          (.tryStmt #[ .unsupported "Global" "global x" sp0 ]
             "Stop"
             #[ .assign #[.name "caught" sp0] (.constant (.int 2) sp0) sp0 ]
             Option.none sp0)) stE with
        | .unsupported _ => true
        | _ => false)

/- 3. A NON-matching exception propagates rather than being caught. -/
#guard (match toRun (execOpen KE excModule
          (.tryStmt #[ .exprStmt (.name "nope" sp0) sp0 ]
             "Stop"
             #[ .assign #[.name "caught" sp0] (.constant (.int 2) sp0) sp0 ]
             Option.none sp0)) stE with
        | .exn _ e => e == .nameError "nope"
        | _ => false)

#print axioms evalOpen
#print axioms execOpen
#print axioms kont
#print axioms callInMono
#print axioms toRun_ofRun
#print axioms ofRun_toRun
#print axioms inFrame_toRun
#print axioms inWorld_toRun

end LeanModels.Python.Monadic
