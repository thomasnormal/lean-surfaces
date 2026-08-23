import LeanModels.Es.Convert
import LeanModels.Es.Ast

/-!
# The evaluator — ES2026 §13 (expressions), §14 (statements), §16.1 (scripts)

Inch 4(b) built the expression walk; inch 5 added statements, declaration
instantiation, and function-body evaluation, over the `Node` tree
`LeanModels/Es/Ast.lean` ingests. A Script now RUNS: `evalProgram` is the
entry point and `Examples/es/statements/guards.lean` is its acceptance.

**Three completion types are the monad's, one is the return value.** A
statement answers `Option Val` — the completion VALUE, with `none` for the
spec's `empty` — while `return`, `break` and `continue` are raised through
`ρ = Abrupt` exactly like `throw`. No statement threads them by hand, so
none can be dropped by forgetting a case, and `SemM.catchRaise` is the one
place each is absorbed. Collapsing `empty` into `undefined` at the leaves
would break §14.6.2, which is what `Examples/es/test262/if_cptn.json`
asserts.

**Structurally recursive on FUEL, never `partial`.** Fuel is an index on
the step function (`docs/family-architecture.md` §3.4), and the walk
decreases it at every subexpression, so the whole evaluator stays
kernel-reducible. §L82's law is why: a `partial` definition is opaque to
the kernel, so no lemma could be stated about an evaluator written that
way — and since `#guard` is NOT a kernel oracle either (2026-08-22-es-4),
a `partial` evaluator would be a thing nothing could check.

**The `Node` shape pays off here.** Inch 1 split a node's properties into
SCALARS and CHILDREN rather than making them one mutual sum; that is
exactly the split an evaluator wants — `operator` and `computed` are
read as flags, `left`/`right`/`object` are recursed into.
-/

namespace LeanModels.Es

/-- A scalar property, by name. -/
def Node.scalar? : Node → String → Option Scalar
  | Node.mk _ _ ss _, k => (ss.find? (fun p => p.1 == k)).map (·.2)
  | _, _ => none

def Node.str? (n : Node) (k : String) : Option String :=
  match Node.scalar? n k with | some (Scalar.str s) => some s | _ => none

def Node.flag (n : Node) (k : String) : Bool :=
  match Node.scalar? n k with | some (Scalar.bool b) => b | _ => false

/-- The FIRST child under a name — the shape a required child has
(`[some n]`, per `Ast.lean`'s uniform arity encoding). -/
def Node.child? : Node → String → Option Node
  | Node.mk _ _ _ cs, k =>
    match (cs.find? (fun p => p.1 == k)).map (·.2) with
    | some (some c :: _) => some c
    | _ => none
  | _, _ => none

/-- A child LIST **with its holes kept**, which `[1, , 3]` needs.

`Node.kids` drops them, and for `arguments` or `body` that is right. For an
array's `elements` it is not: §13.2.4.1 leaves an elision's index ABSENT and
only advances the counter, so `[1, , 3]` has `length` 3 and no own property
at 1. Dropping the hole would close the array up to `[1, 3]`; filling it
with `undefined` would make `hasOwnProperty(1)` true. Both are wrong, and
only a list that still contains the hole can be right. -/
def Node.kidsOpt : Node → String → List (Option Node)
  | Node.mk _ _ _ cs, k => ((cs.find? (fun p => p.1 == k)).map (·.2)).getD []
  | _, _ => []

/-- A child LIST, with holes dropped — `arguments`, `body`. -/
def Node.kids : Node → String → List Node
  | Node.mk _ _ _ cs, k =>
    match (cs.find? (fun p => p.1 == k)).map (·.2) with
    | some l => l.filterMap id
    | none => []
  | _, _ => []

def Node.kindOf : Node → Option NodeKind
  | Node.mk k _ _ _ => some k
  | _ => none


/-! ## Literals — §13.2.3 -/

/-- A `Literal`'s value. A numeric literal's SOURCE TEXT is converted
here, which is where `es-0.1`'s decision to carry the raw digits (rather
than a host double) is paid off: the conversion happens under this tier's
rules, not the extractor's. -/
def literalValue : Lit → EsW Val
  | .string s => return .str s
  | .boolean b => return .bool b
  | .null => return .null
  | .number raw => stringToNumber raw
  | .bigint d => match d.toInt? with
    | some i => return .bigint i
    | none => SemM.refuseConstruct s!"BigInt literal '{d}' is outside the decimal fragment"
  | .regexp _ _ => SemM.refuseIntrinsic
      "a RegExp literal builds a RegExp object, which needs %RegExp% (inch 6)"

/-- Resolve a name WITHOUT throwing — §9.4.2's `GetIdentifierReference`
answers an unresolvable Reference Record, and the throw happens later at
`GetValue`. `Env.resolveBinding` throws, so it is the wrong primitive
here: `typeof undeclared` is legal precisely because the reference is
built first and never read. -/
def resolveBinding? : Nat → EnvRef → String → EsW (Option EnvRef)
  | 0, _, _ => fun _ => .error .timeout
  | fuel + 1, env, name => do
    if ← envHasBinding env name then return some env
    match (← derefEnv env).outer with
    | some o => resolveBinding? fuel o name
    | none => return none

/-! ## The expression walk — §13

`evalExpr` answers a VALUE; `evalRef` answers a Reference Record, which is
what an assignment target or a `delete` needs. Keeping them apart is the
spec's own split (§6.2.5) and is why `x = 1` and `o.k = 1` are one rule
each rather than four. -/

/-! ## Static semantics — ES2026 §8.2

These are the spec's SYNTAX-DIRECTED OPERATIONS: functions of a Parse Node
that read no state and cannot throw. They are structurally recursive on
`Node` (the `Json.lean` idiom), **not fuel-indexed**, and that is
deliberate: a fuel-indexed `VarDeclaredNames` that ran out would silently
return too few names, and a missing `var` binding is a `ReferenceError`
the program never wrote — a wrong answer rather than a loud one. Structural
recursion cannot run out. -/

mutual

/-- `VarDeclaredNames` — §8.2.6, restricted to the names a `var` binds.

The recursion STOPS at a function or class boundary, which is the whole
content of the operation: `function f(){ var x }` does not put `x` in the
enclosing scope. Everything else is walked, including the bodies of
blocks, loops and `try`, because `var` is function-scoped and a nested
block does not contain it. -/
def Node.varNames : Node → List String
  | .mk k _ ss cs =>
    if k == .functionDeclaration || k == .functionExpression
       || k == .arrowFunctionExpression || k == .classDeclaration
       || k == .classExpression then []
    else if k == .variableDeclaration && (ss.find? (·.1 == "kind")).map (·.2) == some (.str "var") then
      Node.declaredNamesOfChildren cs
    else Node.varNamesOfChildren cs
  | .lit .. => []
  | .unsupported .. => []

def Node.varNamesOfChildren : List (String × List (Option Node)) → List String
  | [] => []
  | (_, ns) :: rest => Node.varNamesOpt ns ++ Node.varNamesOfChildren rest

def Node.varNamesOpt : List (Option Node) → List String
  | [] => []
  | some n :: rest => Node.varNames n ++ Node.varNamesOpt rest
  | none :: rest => Node.varNamesOpt rest

/-- The `BoundNames` (§8.2.1) under a declaration: every `Identifier` that
is not the `init` of a declarator. A destructuring pattern's names are NOT
collected here — patterns REFUSE at evaluation, and collecting their names
would hoist a binding the evaluator then cannot fill. -/
def Node.declaredNamesOfChildren : List (String × List (Option Node)) → List String
  | [] => []
  | ("init", _) :: rest => Node.declaredNamesOfChildren rest
  | (_, ns) :: rest => Node.declaredNamesOpt ns ++ Node.declaredNamesOfChildren rest

def Node.declaredNamesOpt : List (Option Node) → List String
  | [] => []
  | some n :: rest => Node.declaredNames n ++ Node.declaredNamesOpt rest
  | none :: rest => Node.declaredNamesOpt rest

def Node.declaredNames : Node → List String
  | .mk k _ ss cs =>
    if k == .identifier then
      match (ss.find? (·.1 == "name")).map (·.2) with
      | some (Scalar.str nm) => [nm]
      | _ => []
    else Node.declaredNamesOfChildren cs
  | .lit .. => []
  | .unsupported .. => []

end

mutual

/-- Does this subtree contain an `Identifier` with this name?

Used for ONE thing: `arguments`. §10.2.11 steps 19-22 create the
`arguments` exotic object, which needs `%Object.prototype%` and
`@@iterator` — realm intrinsics this tier does not have. Rather than bind
a half-built object (whose `Object.getPrototypeOf` would then be a wrong
answer) or leave the name unbound (a `ReferenceError` the program never
wrote), a body that MENTIONS the name refuses.

The test is deliberately over-eager: `o.arguments` matches too. An
over-eager refusal is loud and countable; an under-eager one is a
divergence. -/
def Node.mentions (n : Node) (nm : String) : Bool :=
  match n with
  | .mk k _ ss cs =>
    (k == .identifier && (ss.find? (·.1 == "name")).map (·.2) == some (.str nm))
      || Node.mentionsInChildren cs nm
  | .lit .. => false
  | .unsupported .. => false

def Node.mentionsInChildren : List (String × List (Option Node)) → String → Bool
  | [], _ => false
  | (_, ns) :: rest, nm => Node.mentionsOpt ns nm || Node.mentionsInChildren rest nm

def Node.mentionsOpt : List (Option Node) → String → Bool
  | [], _ => false
  | some n :: rest, nm => Node.mentions n nm || Node.mentionsOpt rest nm
  | none :: rest, nm => Node.mentionsOpt rest nm

end

/-- `LexicallyScopedDeclarations` — §8.2.9, at the TOP LEVEL of a
StatementList only. A `let` inside a nested block belongs to that block,
so this does not recurse; that is the difference from `varNames` and it is
why `let` is block-scoped. -/
def lexicalDecls (stmts : List Node) : List Node :=
  stmts.filter fun s =>
    s.kindOf == some .variableDeclaration && s.str? "kind" != some "var"

/-- The hoisted `FunctionDeclaration`s of a StatementList — §8.2.7's
`VarScopedDeclarations` for the function case. Top level only, for the
same reason. -/
def hoistedFunctions (stmts : List Node) : List Node :=
  stmts.filter (·.kindOf == some .functionDeclaration)

/-! ## Creating a function from source — §10.2.3, §15.2.4, §15.3.4 -/

/--
`InstantiateFunctionObject` / `InstantiateOrdinaryFunctionExpression` /
`InstantiateArrowFunctionExpression` — §15.2.4, §15.2.5, §15.3.4.

All three are `OrdinaryFunctionCreate` over the node's own
`params`/`body`, so they are one clause here and the node's kind picks the
two things that differ: an arrow gets `[[ThisMode]] = lexical` and no
`[[Construct]]`.

**`[[Strict]]` is `true` unconditionally.** The Directive Prologue
(§11.2.2) is not read yet, so this inherits inch 3's already-documented
choice rather than inventing a second one. It matters for `this`:
`OrdinaryCallBindThis`'s sloppy arm refuses, so a non-strict function
called bare would refuse instead of seeing the global object. Modelling
the prologue is `2026-08-23-es-2`.
-/
def instantiateFunction (env : EnvRef) (n : Node) : EsW Val := do
  if n.flag "generator" then
    SemM.refuseConstruct "generator function: needs the generator machinery (§27.5)"
  if n.flag "async" then
    SemM.refuseConstruct "async function: needs the job queue, which §0 defers with the event loop"
  match n.child? "body" with
  | none => SemM.refuseConstruct "internal: function node without a body (report this)"
  | some body => do
    let isArrow := n.kindOf == some .arrowFunctionExpression
    let code : Code :=
      { params := n.kids "params", body := body, exprBody := isArrow && n.flag "expression" }
    let f ← ordinaryFunctionCreate none (.ecmascript code) (some env)
              (if isArrow then .lexical else .strict) true
    -- §15.2.4 step 5 / §15.3.4: an arrow is NOT a constructor.
    if !isArrow then makeConstructor f none
    return .obj f

/-- `CreatePerIterationEnvironment(perIterationBindings)` — §14.7.4.4, 5
steps, and the reason `for (let i = 0; …)` gives each closure its OWN `i`.

A fresh record per iteration, seeded with the PREVIOUS one's values.
Skipping it (sharing one record) is the classic wrong answer where every
closure sees the final value; the empty-name case returns the record
unchanged, which is what a `var` or expression head gets. -/
def createPerIterationEnvironment (env : EnvRef) (names : List String) : EsW EnvRef := do
  if names.isEmpty then return env
  let last ← derefEnv env
  let fresh ← newDeclarativeEnvironment last.outer
  for nm in names do
    envCreateMutableBinding fresh nm false
    envInitializeBinding fresh nm (← envGetBindingValue env nm)
  return fresh

/-- `BindingInstantiation` for the parameter list — the simple-parameter
fragment of §10.2.11 steps 24-27.

Simple `Identifier` parameters only: a default (`AssignmentPattern`), a
pattern, or a rest element refuses, because each needs machinery this inch
does not have (a default needs its own environment, a pattern needs
destructuring). A missing argument is `undefined` and an extra argument is
dropped, which is §10.2.11 step 27.a-b exactly. -/
def bindParams : Nat → EnvRef → List Node → List Val → EsW Unit
  | _, _, [], _ => pure ()
  | 0, _, _, _ => fun _ => .error .timeout
  | fuel + 1, env, p :: ps, args => do
    match p.kindOf, p.str? "name" with
    | some .identifier, some nm => do
      envCreateMutableBinding env nm false
      envInitializeBinding env nm (args.headD .undef)
      bindParams fuel env ps args.tail
    | _, _ =>
      SemM.refuseConstruct
        "non-simple parameter (default, pattern, or rest) is not modeled yet"

/-- The lexical half of `BlockDeclarationInstantiation` (§14.2.3, 5 steps):
`let` uninitialized-mutable, `const` uninitialized-IMMUTABLE. Leaving them
uninitialized is what makes the temporal dead zone a `ReferenceError`
rather than `undefined` — `envGetBindingValue` is the clause that throws. -/
def instantiateLexical (env : EnvRef) (stmts : List Node) : EsW Unit := do
  for d in lexicalDecls stmts do
    let isConst := d.str? "kind" == some "const"
    for nm in Node.declaredNames d do
      if isConst then envCreateImmutableBinding env nm true
      else envCreateMutableBinding env nm false

/-- The function half of `BlockDeclarationInstantiation` (§14.2.3 step
3.a.ii) and of §10.2.11 step 34: a hoisted `FunctionDeclaration` is
created AND initialized before any statement runs, which is why calling it
above its own text works. -/
def instantiateFunctions (env : EnvRef) (stmts : List Node) : EsW Unit := do
  for fn in hoistedFunctions stmts do
    match (fn.child? "id").bind (·.str? "name") with
    | none => SemM.refuseConstruct "internal: FunctionDeclaration without a name (report this)"
    | some nm => do
      let fo ← instantiateFunction env fn
      if ← envHasBinding env nm then envSetMutableBinding env nm fo true
      else do
        envCreateMutableBinding env nm false
        envInitializeBinding env nm fo

/-- `BlockDeclarationInstantiation(code, env)` — §14.2.3. -/
def blockDeclarationInstantiation (env : EnvRef) (stmts : List Node) : EsW Unit := do
  instantiateLexical env stmts
  instantiateFunctions env stmts

/--
The var/function/lexical core shared by `FunctionDeclarationInstantiation`
(§10.2.11, **38 steps**) and `GlobalDeclarationInstantiation` (§16.1.7, 18
steps).

**One clause for two operations, and the difference is honest.** §16.1.7
puts `var` names on the GLOBAL OBJECT as properties (so `var x` at top
level makes `globalThis.x`) while §10.2.11 puts them in the function's
declarative record. There is no global object in this tier, so both land
in the record. The observable that separates them — `this.x` at top
level — needs the global object, and `resolveThisBinding` already refuses
there, so no test can reach the difference and score a pass.

Order matters and is the spec's: vars first (initialized `undefined`),
then hoisted functions (which OVERWRITE the `undefined`), then the
lexical names (left uninitialized). -/
def instantiateDeclarations (env : EnvRef) (stmts : List Node) : EsW Unit := do
  for nm in stmts.flatMap Node.varNames do
    unless ← envHasBinding env nm do
      envCreateMutableBinding env nm false
      envInitializeBinding env nm .undef
  instantiateFunctions env stmts
  instantiateLexical env stmts

/-- `FunctionDeclarationInstantiation(func, argumentsList)` — §10.2.11. -/
def functionDeclarationInstantiation (fuel : Nat) (env : EnvRef) (code : Code)
    (args : List Val) : EsW Unit := do
  bindParams fuel env code.params args
  if Node.mentions code.body "arguments" then
    SemM.refuseIntrinsic
      "the `arguments` object needs %Object.prototype% and @@iterator (§10.4.4)"
  if code.exprBody then pure ()
  else instantiateDeclarations env (code.body.kids "body")

mutual

/-- Evaluate an expression to a Reference Record — §13.1, §13.3.2. Only
the two forms that CAN be references have a case; everything else is a
value and cannot be assigned to, which is a program error the caller
raises. -/
def evalRef : Nat → EnvRef → Node → EsW Ref
  | 0, _, _ => fun _ => .error .timeout
  | fuel + 1, env, n =>
    match n.kindOf with
    | some .identifier =>
      match n.str? "name" with
      | some name => do
        match ← resolveBinding? fuel env name with
        | some e => return { base := .env e, name := .str name }
        | none => return { base := .unresolvable, name := .str name }
      | none => SemM.refuseConstruct "internal: Identifier without a name (report this)"
    | some .memberExpression => do
      match n.child? "object" with
      | none => SemM.refuseConstruct "internal: MemberExpression without an object"
      | some oNode => do
        let base ← evalExpr fuel env oNode
        let key ← if n.flag "computed" then do
            match n.child? "property" with
            | some p => toPropertyKey fuel (← evalExpr fuel env p)
            | none => SemM.refuseConstruct "internal: computed member without a property"
          else
            match (n.child? "property").bind (fun p => p.str? "name") with
            | some nm => pure (PropKey.str nm)
            | none => SemM.refuseConstruct "internal: static member without a name"
        return { base := .value base, name := key }
    | _ => SemM.refuseConstruct "expression is not a valid assignment target"

/-- The `PropertyKey` a `Property` node names — §13.2.5.5.

Three shapes. A COMPUTED key is evaluated and run through `ToPropertyKey`.
A LITERAL key goes through the same conversion, which is how `{2: 2}`
becomes the string key `"2"` — and therefore an array index, which is what
puts it before `"b"` in `Object.keys`. An IDENTIFIER key is its own text and
is deliberately NOT evaluated: `{a: 1}` does not read a binding named `a`. -/
def propKeyOf : Nat → EnvRef → Node → EsW PropKey
  | 0, _, _ => fun _ => .error .timeout
  | fuel + 1, env, p =>
    match p.child? "key" with
    | none => SemM.refuseConstruct "internal: Property without a key (report this)"
    | some k =>
      if p.flag "computed" then do toPropertyKey fuel (← evalExpr fuel env k)
      else
        match k with
        | Node.lit v _ _ => do toPropertyKey fuel (← literalValue v)
        | _ =>
          match k.str? "name" with
          | some nm => pure (PropKey.str nm)
          | none =>
            SemM.refuseConstruct
              "internal: a non-computed key is neither a Literal nor an Identifier"

/-- Evaluate an expression to a value — §13. -/
def evalExpr : Nat → EnvRef → Node → EsW Val
  | 0, _, _ => fun _ => .error .timeout
  | fuel + 1, env, n =>
    match n with
    | Node.lit v _ _ => literalValue v
    | Node.unsupported ty _ _ =>
      SemM.refuseConstruct s!"expression node '{ty}' is outside the pinned vocabulary"
    | Node.mk kind _ _ _ =>
      match kind with
      | .identifier => do getValue fuel (← evalRef fuel env n)
      | .thisExpression => resolveThisBinding fuel env
      | .memberExpression => do getValue fuel (← evalRef fuel env n)
      | .sequenceExpression => do
        -- §13.16: evaluate every operand, answer the LAST
        let mut last : Val := .undef
        for e in n.kids "expressions" do
          last ← evalExpr fuel env e
        return last
      | .conditionalExpression => do
        match n.child? "test", n.child? "consequent", n.child? "alternate" with
        | some t, some c, some a =>
          if Val.toBoolean (← evalExpr fuel env t) then evalExpr fuel env c
          else evalExpr fuel env a
        | _, _, _ => SemM.refuseConstruct "internal: malformed ConditionalExpression"
      | .logicalExpression => do
        -- §13.13: SHORT-CIRCUITING, so the right operand's world never
        -- exists when the left decides — the family's drain amendment.
        match n.child? "left", n.child? "right", n.str? "operator" with
        | some l, some r, some op => do
          let lv ← evalExpr fuel env l
          match op with
          | "&&" => if Val.toBoolean lv then evalExpr fuel env r else return lv
          | "||" => if Val.toBoolean lv then return lv else evalExpr fuel env r
          | "??" =>
            match lv with
            | .undef | .null => evalExpr fuel env r
            | _ => return lv
          | _ => SemM.refuseConstruct s!"logical operator '{op}' is not modeled"
        | _, _, _ => SemM.refuseConstruct "internal: malformed LogicalExpression"
      | .binaryExpression => do
        match n.child? "left", n.child? "right", n.str? "operator" with
        | some l, some r, some op => do
          let lv ← evalExpr fuel env l
          let rv ← evalExpr fuel env r
          match op with
          | "===" => return .bool (Val.strictEquals lv rv)
          | "!==" => return .bool (!(Val.strictEquals lv rv))
          | "<" => do
            match ← isLessThan fuel lv rv true with
            | some b => return .bool b
            | none => return .bool false            -- NaN: §13.10.1 step 6
          | ">" => do
            match ← isLessThan fuel rv lv false with
            | some b => return .bool b
            | none => return .bool false
          | "instanceof" => return .bool (← ordinaryHasInstance fuel rv lv)
          | _ => applyBinary fuel lv op rv
        | _, _, _ => SemM.refuseConstruct "internal: malformed BinaryExpression"
      | .unaryExpression => do
        match n.child? "argument", n.str? "operator" with
        | some a, some op =>
          match op with
          | "typeof" => do
            -- §13.5.1.1: the reference path exists ONLY so an unresolvable
            -- name answers "undefined" instead of throwing.  Every other
            -- argument is an ordinary value, and routing it through
            -- `evalRef` would refuse it as a non-target — which is what the
            -- first version did, making `typeof 1` a refusal.
            let v ←
              if a.kindOf == some .identifier then do
                let r ← evalRef fuel env a
                if r.isUnresolvable then return .str "undefined"
                else getValue fuel r
              else evalExpr fuel env a
            match v with
            | .obj o => do
              let callable := (← deref o).callable.isSome
              return .str (Val.typeofWith (fun _ => callable) v)
            | _ => return .str (Val.typeofWith (fun _ => false) v)
          | "!" => return .bool (!(Val.toBoolean (← evalExpr fuel env a)))
          | "void" => do let _ ← evalExpr fuel env a; return .undef
          | "-" => do
            match ← toNumber fuel (← evalExpr fuel env a) with
            | .num x => return .num (-x)
            | _ => throwError "TypeError" "Cannot negate a BigInt here"
          | "+" => toNumber fuel (← evalExpr fuel env a)
          | _ => SemM.refuseConstruct s!"unary operator '{op}' is not modeled"
        | _, _ => SemM.refuseConstruct "internal: malformed UnaryExpression"
      | .assignmentExpression => do
        match n.child? "left", n.child? "right", n.str? "operator" with
        | some l, some r, some "=" => do
          let target ← evalRef fuel env l
          let v ← evalExpr fuel env r
          putValue fuel target v
          return v                                   -- §13.15.2: the VALUE
        | _, _, some op =>
          SemM.refuseConstruct s!"compound assignment '{op}' is not modeled yet"
        | _, _, _ => SemM.refuseConstruct "internal: malformed AssignmentExpression"
      | .callExpression => do
        match n.child? "callee" with
        | none => SemM.refuseConstruct "internal: CallExpression without a callee"
        | some callee => do
          -- §13.3.6.1: the THIS value comes from the callee's reference —
          -- `o.m()` passes `o`, a bare `f()` passes undefined.
          let (fv, thisArg) ←
            if (callee.kindOf == some .memberExpression) then do
              let r ← evalRef fuel env callee
              pure (← getValue fuel r, r.getThisValue)
            else do
              pure (← evalExpr fuel env callee, Val.undef)
          let mut args : List Val := []
          for a in n.kids "arguments" do
            args := args ++ [← evalExpr fuel env a]
          callComplete fuel fv thisArg args
      | .newExpression => do
        match n.child? "callee" with
        | none => SemM.refuseConstruct "internal: NewExpression without a callee"
        | some callee => do
          let fv ← evalExpr fuel env callee
          let mut args : List Val := []
          for a in n.kids "arguments" do
            args := args ++ [← evalExpr fuel env a]
          constructComplete fuel fv args
      | .objectExpression => do
        -- §13.2.5.5 PropertyDefinitionEvaluation. EVERY property goes through
        -- `CreateDataPropertyOrThrow` — never through `props` directly. That
        -- discipline is the whole correctness argument here: it is what makes
        -- a duplicate key UPDATE in place (so `{b:1, a:2, b:3}` keeps `b`
        -- first) and what would carry an Array's live `length` if this were
        -- one.
        let obj ← ordinaryObjectCreate none
        for prop in n.kids "properties" do
          match prop.kindOf with
          | some .property =>
            if prop.str? "kind" != some "init" then
              SemM.refuseConstruct
                "get/set in an object literal needs the accessor path (2026-08-23-es-1)"
            else if prop.flag "method" then
              SemM.refuseConstruct "a shorthand method needs [[HomeObject]] (the class inch)"
            else do
              let k ← propKeyOf fuel env prop
              match prop.child? "value" with
              | none => SemM.refuseConstruct "internal: Property without a value (report this)"
              | some ve => do
                let v ← evalExpr fuel env ve
                createDataPropertyOrThrow obj k v
          | some .spreadElement =>
            SemM.refuseConstruct "object spread needs CopyDataProperties (§7.3.25)"
          | _ => SemM.refuseConstruct "internal: unexpected node in an ObjectExpression"
        return .obj obj
      | .arrayExpression => do
        -- §13.2.4.1 ArrayAccumulation. The counter advances past an elision
        -- WITHOUT defining anything, which is what leaves `[1, , 3]` with a
        -- hole at 1 and a `length` of 3.
        let arr ← arrayCreate 0
        let mut i : Nat := 0
        for el in n.kidsOpt "elements" do
          match el with
          | none => i := i + 1
          | some e =>
            if e.kindOf == some .spreadElement then
              SemM.refuseConstruct "array spread needs the iterator protocol (§7.4)"
            else do
              let v ← evalExpr fuel env e
              let _ ← createDataProperty arr (.str (toString i)) v
              i := i + 1
        -- §13.2.4.2 step 5: `length` counts TRAILING elisions, which the
        -- per-element writes never reached.
        let _ ← esDefineOwnProperty arr (.str "length") { value := some (.num i.toFloat) }
        return .obj arr
      | .updateExpression => do
        match n.child? "argument", n.str? "operator" with
        | some a, some op => do
          let r ← evalRef fuel env a
          -- §13.4.2.1 step 2: `ToNumeric` runs BEFORE the answer is chosen,
          -- so `s = "3"; s++` answers the NUMBER 3, not the string. An
          -- implementation that saved the old value and converted afterwards
          -- returns `"3"` and is wrong in a way no numeric test would catch.
          let oldValue ← toNumber fuel (← getValue fuel r)
          let newValue ←
            match oldValue with
            | .num x =>
              if op == "++" then pure (Val.num (x + 1.0))
              else if op == "--" then pure (Val.num (x - 1.0))
              else SemM.refuseConstruct s!"update operator '{op}' is not modeled"
            | _ => SemM.refuseConstruct "BigInt increment needs a BigInt tier"
          putValue fuel r newValue
          -- §13.4.2.1 vs §13.4.4.1: postfix answers the OLD value, prefix the new.
          return (if n.flag "prefix" then newValue else oldValue)
        | _, _ => SemM.refuseConstruct "internal: malformed UpdateExpression"
      -- §15.2.5, §15.3.4: a function EXPRESSION and an arrow are the same
      -- clause; the node's kind is what makes an arrow lexical-`this` and
      -- non-constructible.
      | .functionExpression => instantiateFunction env n
      | .arrowFunctionExpression => instantiateFunction env n
      | k =>
        SemM.refuseConstruct s!"expression kind '{kindName k}' is not modeled yet"


/- ## Statements — ES2026 §14

Every statement answers an `Option Val`: the spec's completion VALUE, with
`none` for its `empty`. `empty` is not `undefined` — `if (true) { }`
completes empty and `eval` of it answers `undefined` only because §14.6.2
runs `UpdateEmpty` on the way out. Collapsing the two at the leaves would
make `eval("1; if (true) { }")` answer `undefined` instead of `1`, which
is precisely what `if_cptn.json` asserts.

**The other three completion types are not here.** `return`, `break` and
`continue` are `ρ = Abrupt`, raised through the monad exactly like
`throw`, so no statement threads them by hand and none can be dropped by
forgetting a case. `SemM.catchRaise` is where each is absorbed:
`OrdinaryCallEvaluateBody` takes the `return`, an iteration statement
takes an unlabelled `break`/`continue`, `try` takes the `throw`. -/

/-- One `VariableDeclarator` — §14.3.1.2 (`let`/`const`) and §14.3.2.1
(`var`).

The asymmetry is the point: a `var` declarator ASSIGNS to a binding that
declaration instantiation already created, so `var x;` alone is a no-op
and does not re-initialize; a lexical declarator INITIALIZES a binding
that is sitting uninitialized in the temporal dead zone, and `let x;`
initializes it to `undefined`. -/
def evalDeclarator : Nat → EnvRef → Bool → Node → EsW Unit
  | 0, _, _, _ => fun _ => .error .timeout
  | fuel + 1, env, isVar, d => do
    match d.child? "id" with
    | none => SemM.refuseConstruct "internal: VariableDeclarator without an id (report this)"
    | some idn =>
      match idn.kindOf, idn.str? "name" with
      | some .identifier, some nm =>
        match d.child? "init" with
        | some e => do
          let v ← evalExpr fuel env e
          let r ← resolveBinding fuel env nm
          if isVar then envSetMutableBinding r nm v true
          else envInitializeBinding r nm v
        | none =>
          if isVar then pure ()
          else do
            let r ← resolveBinding fuel env nm
            envInitializeBinding r nm .undef
      | _, _ =>
        SemM.refuseConstruct "destructuring declaration is not modeled yet"

/-- `CatchClauseEvaluation` — §14.15.3 steps 5-8. The parameter gets its
OWN record, outside the block's, which is why `catch (e) { let e }` is a
SyntaxError and not a shadowing. An absent parameter (`try {} catch {}`)
skips the record entirely, per §14.15's optional binding. -/
def evalCatchClause : Nat → EnvRef → Node → Val → EsW (Option Val)
  | 0, _, _, _ => fun _ => .error .timeout
  | fuel + 1, env, h, thrown => do
    match h.child? "body" with
    | none => SemM.refuseConstruct "internal: CatchClause without a body (report this)"
    | some blk =>
      match h.child? "param" with
      | none => evalStmt fuel env blk
      | some p =>
        match p.kindOf, p.str? "name" with
        | some .identifier, some nm => do
          let catchEnv ← newDeclarativeEnvironment (some env)
          envCreateMutableBinding catchEnv nm false
          envInitializeBinding catchEnv nm thrown
          evalStmt fuel catchEnv blk
        | _, _ =>
          SemM.refuseConstruct "destructuring catch parameter is not modeled yet"

/--
The repeat step shared by §14.7's three iteration statements —
`WhileLoopEvaluation` (§14.7.3.2), `DoWhileLoopEvaluation` (§14.7.2.2) and
`ForBodyEvaluation` (§14.7.4.4).

`testFirst` is the only thing that separates `while` from `do…while`, and
it is `false` for exactly one iteration: every recursive call passes
`true`, which is the spec's "evaluate the body, THEN the condition, then
repeat from the condition".

`perIter` carries §14.7.4.4's `perIterationBindings`. The fresh record is
made AFTER the body and BEFORE the increment, so the increment writes the
NEXT iteration's binding — get that order wrong and every closure in the
loop shares one variable.

`LoopContinues` (§14.7.1.1) is the `catchRaise` handler: an unlabelled
`continue` is absorbed and falls through to the increment, an unlabelled
`break` ends the loop with `UpdateEmpty(result, V)`, and everything else —
a labelled jump, a `return`, a `throw` — is re-raised untouched.

`acc` is the spec's `V`, and the callers seed it with **`undefined`, not
`empty`** (§14.7.4.4 step 1). A loop whose test is false at once therefore
completes `undefined`, which is why `eval("1; while (false);")` answers
`undefined` and not `1`. -/
def runLoop : Nat → EnvRef → Bool → List String → Option Node → Option Node →
    Node → Option Val → EsW (Option Val)
  | 0, _, _, _, _, _, _, _ => fun _ => .error .timeout
  | fuel + 1, env, testFirst, perIter, test, update, body, acc => do
    let go ←
      if testFirst then
        match test with
        | some t => do pure (Val.toBoolean (← evalExpr fuel env t))
        | none => pure true
      else pure true
    if !go then return acc
    let r ← SemM.catchRaise
              (do pure (Except.ok (← evalStmt fuel env body)))
              (fun a =>
                match a with
                | .cont none cv => pure (Except.ok cv)
                | .brk none bv => pure (Except.error (Abrupt.brk none bv))
                | other => SemM.raise other)
    match r with
    -- §14.7.4.4 step 3.c: `UpdateEmpty(result, V)` — the break's own value
    -- when it has one, the loop's accumulated `V` otherwise.
    | .error (.brk _ bv) => return (match bv with | some _ => bv | none => acc)
    | .error other => SemM.raise other
    | .ok v =>
      let acc' := match v with | some _ => v | none => acc
      let env' ← createPerIterationEnvironment env perIter
      match update with
      | some u => do
        let _ ← evalExpr fuel env' u
        runLoop fuel env' true perIter test update body acc'
      | none => runLoop fuel env' true perIter test update body acc'

/-- The case that matches, by index — §14.12.4's phase A and phase B in
one left-to-right walk.

The two phases scan the cases BEFORE the default and then the cases AFTER
it, in that order, skipping the default itself; source order is A then B,
so a single walk that skips the default evaluates exactly the same tests
in exactly the same order. Both phases stop at the first match, and this
does too. -/
def selectCase : Nat → EnvRef → List Node → Val → Nat → EsW (Option Nat)
  | _, _, [], _, _ => return none
  | 0, _, _, _, _ => fun _ => .error .timeout
  | fuel + 1, env, c :: rest, dv, i => do
    match c.child? "test" with
    | none => selectCase fuel env rest dv (i + 1)
    | some t =>
      if Val.strictEquals dv (← evalExpr fuel env t) then return some i
      else selectCase fuel env rest dv (i + 1)

/-- `CaseBlockEvaluation` — §14.12.4.

FALL-THROUGH is why this concatenates the consequents from the selected
case to the END of the block rather than running one case: `switch (1) {
case 1: a(); case 2: b(); }` runs both. When nothing matches, execution
starts at the `default` — wherever it sits — and falls through the cases
after it, which is the same "drop and concatenate". -/
def evalCaseBlock : Nat → EnvRef → List Node → Val → EsW (Option Val)
  | 0, _, _, _ => fun _ => .error .timeout
  | fuel + 1, env, cases, dv => do
    -- §14.12.4 step 2: `V` starts at *undefined*, NOT at `empty`, so a
    -- `switch` always completes with a value.
    match ← selectCase fuel env cases dv 0 with
    | some i => evalStmtList fuel env ((cases.drop i).flatMap (·.kids "consequent")) (some .undef)
    | none =>
      match cases.findIdx? (fun c => (c.child? "test").isNone) with
      | some d => evalStmtList fuel env ((cases.drop d).flatMap (·.kids "consequent")) (some .undef)
      | none => return (some .undef)

/-- `StatementList : StatementList StatementListItem` — §14.2.2 step 3,
whose whole content is `UpdateEmpty`: a statement that completes EMPTY
leaves the list's value at whatever the previous statement left. That is
how `eval("1; ;")` answers `1`. -/
def evalStmtList : Nat → EnvRef → List Node → Option Val → EsW (Option Val)
  | _, _, [], acc => return acc
  | 0, _, _, _ => fun _ => .error .timeout
  | fuel + 1, env, s :: rest, acc => do
    -- `UpdateEmpty(s, sl)` applies to an ABRUPT `s` as well as a normal one,
    -- which is how the `break` out of `{ 5; break; }` leaves carrying the
    -- `5` that the loop then completes with.
    let v ← SemM.catchRaise (evalStmt fuel env s)
              (fun a => SemM.raise (match acc with
                                    | some av => Abrupt.updateEmpty a av
                                    | none => a))
    evalStmtList fuel env rest (match v with | some _ => v | none => acc)

/-- Evaluate a statement — §14. -/
def evalStmt : Nat → EnvRef → Node → EsW (Option Val)
  | 0, _, _ => fun _ => .error .timeout
  | fuel + 1, env, n =>
    match n with
    | Node.lit .. => SemM.refuseConstruct "internal: a Literal is not a statement (report this)"
    | Node.unsupported ty _ _ =>
      SemM.refuseConstruct s!"statement node '{ty}' is outside the pinned vocabulary"
    | Node.mk kind _ _ _ =>
      match kind with
      -- §14.4.1, §14.16.1: both complete EMPTY, which is NOT `undefined`.
      | .emptyStatement => return none
      | .debuggerStatement => return none
      -- §15.2.6: a hoisted declaration has already run; the statement itself
      -- completes empty.
      | .functionDeclaration => return none
      | .expressionStatement =>
        match n.child? "expression" with
        | some e => do return some (← evalExpr fuel env e)
        | none => SemM.refuseConstruct "internal: ExpressionStatement without an expression"
      | .blockStatement => do
        -- §14.2.2 step 1: an EMPTY block completes empty without a record.
        let stmts := n.kids "body"
        if stmts.isEmpty then return none
        let blockEnv ← newDeclarativeEnvironment (some env)
        blockDeclarationInstantiation blockEnv stmts
        evalStmtList fuel blockEnv stmts none
      | .variableDeclaration => do
        let isVar := n.str? "kind" == some "var"
        for d in n.kids "declarations" do
          evalDeclarator fuel env isVar d
        return none
      | .ifStatement =>
        match n.child? "test", n.child? "consequent" with
        | some t, some c => do
          let b := Val.toBoolean (← evalExpr fuel env t)
          let r ←
            if b then evalStmt fuel env c
            else match n.child? "alternate" with
                 | some a => evalStmt fuel env a
                 | none => pure none
          -- §14.6.2 step 5: `Completion(UpdateEmpty(stmtCompletion, undefined))`.
          -- THIS is the clause `if_cptn.json` is about.
          return some (r.getD .undef)
        | _, _ => SemM.refuseConstruct "internal: malformed IfStatement"
      | .returnStatement => do
        let v ← match n.child? "argument" with
          | some a => evalExpr fuel env a
          | none => pure Val.undef
        SemM.raise (.ret v)
      | .throwStatement =>
        match n.child? "argument" with
        | some a => do SemM.raise (.throw (← evalExpr fuel env a))
        | none => SemM.refuseConstruct "internal: ThrowStatement without an argument"
      | .breakStatement => SemM.raise (.brk ((n.child? "label").bind (·.str? "name")) none)
      | .continueStatement => SemM.raise (.cont ((n.child? "label").bind (·.str? "name")) none)
      | .tryStatement =>
        match n.child? "block" with
        | none => SemM.refuseConstruct "internal: TryStatement without a block"
        | some blk =>
          let guarded : EsW (Option Val) :=
            match n.child? "handler" with
            | none => evalStmt fuel env blk
            | some h =>
              -- §14.15.3: ONLY a throw is caught. A `return` crossing a
              -- `try` must keep going, which is what re-raising does.
              SemM.catchRaise (evalStmt fuel env blk) (fun a =>
                match a with
                | .throw v => evalCatchClause fuel env h v
                | other => SemM.raise other)
          match n.child? "finalizer" with
          | none => do return some ((← guarded).getD .undef)
          | some f => do
            -- §14.15.3 steps 6-7: the finalizer runs on BOTH paths, and if
            -- IT completes abruptly its completion WINS — which is why
            -- `try { return 1 } finally { return 2 }` answers 2.
            let r ← SemM.catchRaise
                      (do pure (Except.ok (← guarded)))
                      (fun a => pure (Except.error a))
            let _ ← evalStmt fuel env f
            match r with
            | .ok v => return some (v.getD .undef)
            | .error a => SemM.raise a
      | .whileStatement =>
        match n.child? "body", n.child? "test" with
        | some b, some t => runLoop fuel env true [] (some t) none b (some .undef)
        | _, _ => SemM.refuseConstruct "internal: malformed WhileStatement"
      | .doWhileStatement =>
        match n.child? "body", n.child? "test" with
        | some b, some t => runLoop fuel env false [] (some t) none b (some .undef)
        | _, _ => SemM.refuseConstruct "internal: malformed DoWhileStatement"
      | .forStatement =>
        match n.child? "body" with
        | none => SemM.refuseConstruct "internal: ForStatement without a body"
        | some body => do
          -- §14.7.4.2: a LEXICAL head gets its own record and, for `let`,
          -- per-iteration copies; a `var` or expression head does not.
          let (loopEnv, perIter) ←
            match n.child? "init" with
            | none => pure (env, ([] : List String))
            | some i =>
              if i.kindOf == some .variableDeclaration then
                if i.str? "kind" == some "var" then do
                  let _ ← evalStmt fuel env i
                  pure (env, ([] : List String))
                else do
                  let e ← newDeclarativeEnvironment (some env)
                  instantiateLexical e [i]
                  let _ ← evalStmt fuel e i
                  -- §14.7.4.2 step 3: `const` is NOT copied per iteration.
                  pure (e, if i.str? "kind" == some "const" then [] else Node.declaredNames i)
              else do
                let _ ← evalExpr fuel env i
                pure (env, ([] : List String))
          let start ← createPerIterationEnvironment loopEnv perIter
          runLoop fuel start true perIter (n.child? "test") (n.child? "update") body (some .undef)
      | .switchStatement =>
        match n.child? "discriminant" with
        | none => SemM.refuseConstruct "internal: SwitchStatement without a discriminant"
        | some d => do
          let dv ← evalExpr fuel env d
          let cases := n.kids "cases"
          -- §14.12.4 step 3: ONE record for the whole case block, so a
          -- `let` in one case is in scope in the next.
          let blockEnv ← newDeclarativeEnvironment (some env)
          blockDeclarationInstantiation blockEnv (cases.flatMap (·.kids "consequent"))
          let r ← SemM.catchRaise
                    (do pure (Except.ok (← evalCaseBlock fuel blockEnv cases dv)))
                    (fun a => match a with
                      | .brk none bv => pure (Except.error (Abrupt.brk none bv))
                      | other => SemM.raise other)
          match r with
          | .error (.brk _ bv) => return some (bv.getD .undef)
          | .error other => SemM.raise other
          | .ok v => return some (v.getD .undef)
      | k =>
        SemM.refuseConstruct s!"statement kind '{kindName k}' is not modeled yet"

/- ## The call protocol, COMPLETED — ES2026 §10.2.1

`Function.lean` holds the fragment of `OrdinaryCallEvaluateBody` that runs
a builtin and refuses an ECMAScript body, because the statement evaluator
imports it and Lean forbids the cycle. This is the complete clause, in the
same relationship `getV` has to `ordinaryGet`: nothing calls the fragment
any more.

**What is still on the fragment.** `Convert.ordinaryToPrimitive` and
`Function.getV` reach `[[Call]]` through the OLD `callValue`, because they
sit below this file. So a user-defined `valueOf`/`toString` reached by
coercion, and a user-defined GETTER, still refuse — loudly, at the
boundary, with their own message. Closing that needs the coercion chain
and the accessor walk to move into this mutual block; it is
`2026-08-23-es-1` and it is a restructuring, not a gap in the semantics. -/

/-- `OrdinaryCallEvaluateBody(F, argumentsList)` — §10.2.1.4, complete.

An arrow's concise body is an EXPRESSION: its value is the result and
there is no `return` to absorb (§15.3.5 step 4). A `FunctionBody` runs its
statement list and completes `undefined` unless a `return` says otherwise,
which is the one place `Abrupt.ret` is taken off the wire. -/
def evalCallBody : Nat → ObjRef → EnvRef → Val → List Val → EsW Val
  | 0, _, _, _, _ => fun _ => .error .timeout
  | fuel + 1, f, calleeEnv, thisArg, args => do
    match (← deref f).callable with
    | none => SemM.refuseConstruct "internal: evaluate the body of a non-callable (report this)"
    | some fd =>
      match fd.body with
      | .builtin nm => callBuiltin nm thisArg args
      | .ecmascript code => do
        functionDeclarationInstantiation fuel calleeEnv code args
        if code.exprBody then evalExpr fuel calleeEnv code.body
        else
          SemM.catchRaise
            (do let _ ← evalStmtList fuel calleeEnv (code.body.kids "body") none
                pure Val.undef)
            (fun a => match a with
              | .ret v => pure v
              | other => SemM.raise other)

/-- `[[Call]](thisArgument, argumentsList)` — §10.2.1, complete. -/
def esCallComplete : Nat → ObjRef → Val → List Val → EsW Val
  | 0, _, _, _ => fun _ => .error .timeout
  | fuel + 1, f, thisArg, args => do
    let calleeEnv ← prepareForOrdinaryCall f .undef
    ordinaryCallBindThis f calleeEnv thisArg
    evalCallBody fuel f calleeEnv thisArg args

/-- `Call(F, V, argumentsList)` — §7.3.14, complete. -/
def callComplete : Nat → Val → Val → List Val → EsW Val
  | 0, _, _, _ => fun _ => .error .timeout
  | fuel + 1, fv, thisArg, args => do
    if ← isCallable fv then
      match fv with
      | .obj r => esCallComplete fuel r thisArg args
      | _ => throwError "TypeError" "not a function"
    else throwError "TypeError" "is not a function"

/-- `Construct(F, argumentsList, newTarget)` — §7.3.15 over the complete
§10.2.2, whose step 13 is the rule people meet first: an object the body
RETURNS wins, and otherwise the `this` the constructor was given comes
back, which is why `function F(){ this.x = 1 }` yields the object. -/
def constructComplete : Nat → Val → List Val → EsW Val
  | 0, _, _ => fun _ => .error .timeout
  | fuel + 1, fv, args => do
    match fv with
    | .obj f =>
      if !(← isConstructor fv) then throwError "TypeError" "is not a constructor"
      else
        match (← deref f).callable with
        | none => throwError "TypeError" "is not a constructor"
        | some fd => do
          let derived := fd.constructorDerived == some true
          let thisArg ← if derived then pure Val.undef
                        else do pure (Val.obj (← ordinaryCreateFromConstructor fuel f))
          let calleeEnv ← prepareForOrdinaryCall f (.obj f)
          if !derived then ordinaryCallBindThis f calleeEnv thisArg
          let result ← evalCallBody fuel f calleeEnv thisArg args
          match result with
          | .obj _ => return result
          | _ => envGetThisBinding calleeEnv
    | _ => throwError "TypeError" "is not a constructor"

end

/-! ## Running a Script — ES2026 §16.1 -/

/--
`ScriptEvaluation(scriptRecord)` — §16.1.6, over
`GlobalDeclarationInstantiation` (§16.1.7).

`env` is the caller's global record: this tier has no global OBJECT, so
§16.1.7's `CreateGlobalVarBinding` (which would make `var x` a property of
`globalThis`) lands in the declarative record instead. The observable that
separates the two is `this.x` at top level, and `resolveThisBinding`
already refuses without the global object, so nothing can reach the
difference and score a pass. `docs/backlog/es.md` carries it.

The answer is the Script's completion VALUE, `none` for `empty` — which is
what a `directEval` would return and what §16.1.6 step 12 hands back.
-/
def evalProgram (fuel : Nat) (env : EnvRef) (p : Node) : EsW (Option Val) := do
  if p.kindOf != some .program then
    SemM.refuseConstruct "internal: evalProgram on a node that is not a Program (report this)"
  let stmts := p.kids "body"
  instantiateDeclarations env stmts
  evalStmtList fuel env stmts none

end LeanModels.Es
