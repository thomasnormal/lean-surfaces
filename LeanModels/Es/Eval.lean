import LeanModels.Es.Convert
import LeanModels.Es.Ast

/-!
# The expression walk — ES2026 §13

M2 inch 4(b), first half: evaluation of the seed vocabulary's EXPRESSION
kinds, over the `Node` tree `LeanModels/Es/Ast.lean` ingests.

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

/-- A child LIST, with holes dropped — `arguments`, `elements`, `body`. -/
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
  | 0, _, _ => fun _ => Halt.timeout
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

mutual

/-- Evaluate an expression to a Reference Record — §13.1, §13.3.2. Only
the two forms that CAN be references have a case; everything else is a
value and cannot be assigned to, which is a program error the caller
raises. -/
def evalRef : Nat → EnvRef → Node → EsW Ref
  | 0, _, _ => fun _ => Halt.timeout
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

/-- Evaluate an expression to a value — §13. -/
def evalExpr : Nat → EnvRef → Node → EsW Val
  | 0, _, _ => fun _ => Halt.timeout
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
          callValue fv thisArg args
      | .newExpression => do
        match n.child? "callee" with
        | none => SemM.refuseConstruct "internal: NewExpression without a callee"
        | some callee => do
          let fv ← evalExpr fuel env callee
          let mut args : List Val := []
          for a in n.kids "arguments" do
            args := args ++ [← evalExpr fuel env a]
          constructValue fuel fv args
      | k =>
        SemM.refuseConstruct s!"expression kind '{kindName k}' is not modeled yet (inch 4c/5)"

end

end LeanModels.Es
