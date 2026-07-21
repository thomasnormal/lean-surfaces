import LeanModels.Python.Ast

/-!
# Fuel-based definitional interpreter (`LeanModels.Python`)

Implements the v0 Python semantic tier of `docs/DESIGN.md` ("Semantic decisions",
normative). The interpreter is total and executable:

* **Fuel discipline** (normative): every function in the mutual block takes
  `fuel : Nat` and starts `match fuel with | 0 => .timeout | fuel + 1 => …`,
  passing the *decremented* fuel to **every** recursive call (expressions
  included). Termination is structural on fuel; proofs do induction on fuel.
  Fuel is a *depth* bound, not a step count: sibling calls receive the same
  (already decremented) fuel.
* **Loud failure**: anything outside the tier yields `Res.unsupported` with a
  message naming the construct — never a silently wrong value. Real Python
  runtime errors yield `Res.exn` with the corresponding `PyErr`.
* **Provability**: the semantics is factored into small, pure, fuel-free
  helpers (`truthy`, `asInt`, `valEq`, `evalBinOp`, `evalUnaryOp`,
  `evalCompareOp`, `Env.lookup`, `Env.set`, `indexVal`, `lenVal`, `assignTo`,
  …) that proofs can `simp`-unfold, plus a mutual block of the four normative
  functions (`evalExpr`, `execStmt`, `execStmts`, `callFunction`) and four
  fueled chain helpers (`evalExprs`, `evalBoolChain`, `evalCompareChain`,
  `execWhile`).

Tier-boundary decisions refining DESIGN.md (Python supports these, v0 does
not — so they are `unsupported`, never a fake `TypeError`):
sequence repetition (`"a" * 2`), `%` string formatting, `str` unpacking
(`a, b = "xy"`), nested/starred unpacking targets, `break`/`continue`
escaping a function body, negative `**` exponents (incl. `0 ** -1`),
referencing a function (or `len`) as a value, calling a non-`Name` expression.

`Env` is an abbrev for `List (String × Val)`, so `Env.lookup` / `Env.set` must
be called by their full names (dot notation on an `Env` value resolves into
the `List` namespace).
-/

namespace LeanModels.Python

/-! ## Pure helpers (fuel-free; proofs `simp`-unfold these) -/

/-- Python type name of a value, as used in CPython error messages. -/
def Val.typeName : Val → String
  | .none => "NoneType"
  | .bool _ => "bool"
  | .int _ => "int"
  | .str _ => "str"
  | .list _ => "list"
  | .tuple _ => "tuple"

/-- Is this value one of the sequence types (`str`/`list`/`tuple`)? -/
def Val.isSeq : Val → Bool
  | .str _ | .list _ | .tuple _ => true
  | _ => false

/-- Python surface syntax of a binary operator (error messages). -/
def BinOp.symbol : BinOp → String
  | .add => "+"
  | .sub => "-"
  | .mult => "*"
  | .floorDiv => "//"
  | .mod => "%"
  | .pow => "**"

/-- Python surface syntax of a comparison operator (error messages). -/
def CmpOp.symbol : CmpOp → String
  | .eq => "=="
  | .notEq => "!="
  | .lt => "<"
  | .ltE => "<="
  | .gt => ">"
  | .gtE => ">="

/-- Schema `kind` name of an expression node (error messages). For
`unsupported` nodes this is the recorded CPython class name. -/
def Expr.kindName : Expr → String
  | .constant .. => "Constant"
  | .name .. => "Name"
  | .binOp .. => "BinOp"
  | .unaryOp .. => "UnaryOp"
  | .boolOp .. => "BoolOp"
  | .compare .. => "Compare"
  | .call .. => "Call"
  | .list .. => "List"
  | .tuple .. => "Tuple"
  | .subscript .. => "Subscript"
  | .unsupported pyKind _ _ => pyKind

/-- Python truthiness `bool(x)`: `None` → false; `bool` → itself;
`int` → `≠ 0`; `str`/`list`/`tuple` → nonempty. -/
def truthy : Val → Bool
  | .none => false
  | .bool b => b
  | .int n => n != 0
  | .str s => !s.isEmpty
  | .list xs => xs.size != 0
  | .tuple xs => xs.size != 0

/-- bool→int coercion (Python's `bool` is an `int` subtype): `int` passes
through, `True`/`False` become `1`/`0`, everything else is `none`. -/
def asInt : Val → Option Int
  | .int n => some n
  | .bool b => some (if b then 1 else 0)
  | _ => Option.none

mutual
  /-- Python `==` on values. Never raises. Numeric (`int`/`bool`) compare by
  value after bool→int coercion (`True == 1`); `str` by string equality;
  `list`/`tuple` elementwise (recursively, so `[True] == [1]`);
  `None == None`; any cross-type combination (after coercion) is `False`. -/
  def valEq : Val → Val → Bool
    | .none, .none => true
    | .bool a, .bool b => a == b
    | .bool a, .int m => (if a then (1 : Int) else 0) == m
    | .int n, .bool b => n == (if b then (1 : Int) else 0)
    | .int n, .int m => n == m
    | .str s, .str t => s == t
    | .list xs, .list ys => valEqList xs.toList ys.toList
    | .tuple xs, .tuple ys => valEqList xs.toList ys.toList
    | _, _ => false

  /-- Elementwise `valEq`; `false` on length mismatch. -/
  def valEqList : List Val → List Val → Bool
    | [], [] => true
    | a :: as, b :: bs => valEq a b && valEqList as bs
    | _, _ => false
end

/-- Ordering comparison on `Int` (only called with `.lt/.ltE/.gt/.gtE`;
the equality cases are handled by `valEq` and never reach here, but are
given their by-value meaning for totality). -/
def intCmp : CmpOp → Int → Int → Bool
  | .eq, x, y => x == y
  | .notEq, x, y => x != y
  | .lt, x, y => x < y
  | .ltE, x, y => x ≤ y
  | .gt, x, y => y < x
  | .gtE, x, y => y ≤ x

/-- Ordering comparison on `String` (lexicographic by Unicode code points,
which is Lean's `String` `<`). See `intCmp` for the equality cases. -/
def strCmp : CmpOp → String → String → Bool
  | .eq, s, t => s == t
  | .notEq, s, t => s != t
  | .lt, s, t => s < t
  | .ltE, s, t => s < t || s == t
  | .gt, s, t => t < s
  | .gtE, s, t => t < s || s == t

/-- One comparison step. `==`/`!=` never raise (`valEq`). Ordering: int/bool
by value (bool→int coercion), str lexicographic; ordering any other type
combination is outside the v0 tier. -/
def evalCompareOp (op : CmpOp) (a b : Val) : Res Bool :=
  match op with
  | .eq => .ok (valEq a b)
  | .notEq => .ok (!valEq a b)
  | op =>
    match asInt a, asInt b with
    | some x, some y => .ok (intCmp op x y)
    | _, _ =>
      match a, b with
      | .str s, .str t => .ok (strCmp op s t)
      | a, b =>
        .unsupported
          s!"comparison '{op.symbol}' between '{a.typeName}' and '{b.typeName}' is outside the v0 tier"

/-- Binary operator on already-evaluated operands. int/bool operands are
coerced to `Int`; arithmetic results are always `int`, never `bool`.
`//`/`%` floor (`Int.fdiv`/`Int.fmod`); divisor 0 → `ZeroDivisionError`.
`**` requires a nonnegative exponent (float result otherwise → unsupported).
`+` concatenates matching sequence types. Python-valid combinations outside
the tier (sequence repetition, `%` formatting) → unsupported; Python-invalid
combinations → `TypeError`. -/
def evalBinOp (op : BinOp) (a b : Val) : Res Val :=
  match asInt a, asInt b with
  | some x, some y =>
    match op with
    | .add => .ok (.int (x + y))
    | .sub => .ok (.int (x - y))
    | .mult => .ok (.int (x * y))
    | .floorDiv =>
        if y = 0 then .exn .zeroDivisionError else .ok (.int (Int.fdiv x y))
    | .mod =>
        if y = 0 then .exn .zeroDivisionError else .ok (.int (Int.fmod x y))
    | .pow =>
        if y < 0 then
          -- CPython: 0 ** -1 raises (no float involved); other negative
          -- exponents produce floats, which are outside the v0 tier.
          if x = 0 then .exn .zeroDivisionError
          else .unsupported "'**' with a negative exponent (float result) is outside the v0 tier"
        else .ok (.int (x ^ y.toNat))
  | _, _ =>
    match op, a, b with
    | .add, .str s, .str t => .ok (.str (s ++ t))
    | .add, .list xs, .list ys => .ok (.list (xs ++ ys))
    | .add, .tuple xs, .tuple ys => .ok (.tuple (xs ++ ys))
    | .mult, a, b =>
        if (a.isSeq && (asInt b).isSome) || ((asInt a).isSome && b.isSeq) then
          .unsupported
            s!"sequence repetition ('{a.typeName}' * '{b.typeName}') is outside the v0 tier"
        else
          .exn (.typeError s!"unsupported operand type(s) for *: '{a.typeName}' and '{b.typeName}'")
    | .mod, .str _, _ =>
        .unsupported "'%' string formatting is outside the v0 tier"
    | op, a, b =>
        .exn (.typeError
          s!"unsupported operand type(s) for {op.symbol}: '{a.typeName}' and '{b.typeName}'")

/-- Unary operator: `not` is truthiness negation (never fails);
unary `-` needs an int/bool operand (`-True == -1`). -/
def evalUnaryOp (op : UnaryOp) (v : Val) : Res Val :=
  match op with
  | .not => .ok (.bool (!truthy v))
  | .usub =>
    match asInt v with
    | some n => .ok (.int (-n))
    | Option.none => .exn (.typeError s!"bad operand type for unary -: '{v.typeName}'")

/-- First match wins (shadowing is by position in the list). -/
def Env.lookup : Env → String → Option Val
  | [], _ => Option.none
  | (k, v) :: rest, name => if k == name then some v else Env.lookup rest name

/-- Replace an existing binding in place, else append at the end. -/
def Env.set : Env → String → Val → Env
  | [], name, v => [(name, v)]
  | (k, w) :: rest, name, v =>
    if k == name then (name, v) :: rest else (k, w) :: Env.set rest name v

/-- Constant literal → runtime value. -/
def Const.toVal : Const → Val
  | .none => .none
  | .bool b => .bool b
  | .int n => .int n
  | .str s => .str s

/-- `len(v)` for `str`/`list`/`tuple` (str counts code points), else `TypeError`. -/
def lenVal : Val → Res Val
  | .str s => .ok (.int s.length)
  | .list xs => .ok (.int xs.size)
  | .tuple xs => .ok (.int xs.size)
  | v => .exn (.typeError s!"object of type '{v.typeName}' has no len()")

/-- Normalize a Python index into `[0, len)`: negative indices count from the
end (`len + i`). `none` = out of range. -/
def normIndex (i : Int) (len : Nat) : Option Nat :=
  let j := if i < 0 then i + (len : Int) else i
  if 0 ≤ j ∧ j < (len : Int) then some j.toNat else Option.none

/-- `container[index]` for `list`/`tuple`/`str` (str yields a 1-char str).
Index must be int/bool (bool coerces: `"ab"[True] == "b"`), else `TypeError`;
out of range → `IndexError`; non-subscriptable container → `TypeError`. -/
def indexVal (container index : Val) : Res Val :=
  match container with
  | .list xs =>
    match asInt index with
    | some i =>
      match normIndex i xs.size with
      | some n => .ok (xs.getD n .none)
      | Option.none => .exn .indexError
    | Option.none =>
      .exn (.typeError s!"list indices must be integers, not {index.typeName}")
  | .tuple xs =>
    match asInt index with
    | some i =>
      match normIndex i xs.size with
      | some n => .ok (xs.getD n .none)
      | Option.none => .exn .indexError
    | Option.none =>
      .exn (.typeError s!"tuple indices must be integers, not {index.typeName}")
  | .str s =>
    match asInt index with
    | some i =>
      match normIndex i s.length with
      | some n => .ok (.str (String.singleton (s.toList.getD n ' ')))
      | Option.none => .exn .indexError
    | Option.none =>
      .exn (.typeError s!"string indices must be integers, not {index.typeName}")
  | v => .exn (.typeError s!"'{v.typeName}' object is not subscriptable")

/-- The names of an unpacking target's elements; `none` if any element is not
a plain `Name` (nested or starred patterns are outside the v0 tier). -/
def targetNames (elts : Array Expr) : Option (List String) :=
  elts.foldr (init := some []) fun e acc =>
    match e, acc with
    | .name id _, some ids => some (id :: ids)
    | _, _ => Option.none

/-- Bind names to values pairwise, left to right (arity already checked). -/
def bindAll (env : Env) : List String → List Val → Env
  | n :: ns, v :: vs => bindAll (Env.set env n v) ns vs
  | _, _ => env

/-- Assign an already-evaluated value to a single assignment target:
a `Name`, or a `Tuple`/`List` of `Name`s (tuple unpacking — the unpacked
value must be a `list`/`tuple`; arity mismatch → `ValueError`; non-iterable →
`TypeError`; `str` unpacking is Python-valid but outside the v0 tier). -/
def assignTo (env : Env) (target : Expr) (v : Val) : Res Env :=
  match target with
  | .name id _ => .ok (Env.set env id v)
  | .tuple elts _ | .list elts _ =>
    match targetNames elts with
    | Option.none =>
      .unsupported "unpacking targets other than plain names are outside the v0 tier"
    | some names =>
      match v with
      | .list xs | .tuple xs =>
        if xs.size = names.length then .ok (bindAll env names xs.toList)
        else if names.length < xs.size then
          .exn (.valueError s!"too many values to unpack (expected {names.length})")
        else
          .exn (.valueError
            s!"not enough values to unpack (expected {names.length}, got {xs.size})")
      | .str _ => .unsupported "unpacking a str is outside the v0 tier"
      | v => .exn (.typeError s!"cannot unpack non-iterable {v.typeName} object")
  | .subscript .. => .unsupported "assignment to a subscript is outside the v0 tier"
  | t => .unsupported s!"assignment target '{t.kindName}' is outside the v0 tier"

/-- Module function table lookup. Each `def` rebinds the module-level name, so
with duplicate definitions the LAST one wins, exactly as in CPython. -/
def findFunction (m : Module) (fname : String) : Option FunctionDefn :=
  m.functions.findRev? (fun f => f.name == fname)

/-- Fresh local environment of a call: parameters bound to arguments
pairwise (arity already checked). -/
def mkCallEnv (params : Array Param) (args : Array Val) : Env :=
  (params.toList.map Param.arg).zip args.toList

/-! ## The interpreter (mutual block, normative signatures)

Every function matches fuel first (`0 => .timeout`) and passes the
decremented fuel to every recursive call. -/

mutual

/-- Evaluate an expression. Expressions cannot mutate the environment in v0
(calls run in fresh envs; no globals), hence the result is just `Res Val`.
Evaluation order is left to right, each operand evaluated once. -/
def evalExpr (m : Module) (fuel : Nat) (env : Env) (e : Expr) : Res Val :=
  match fuel with
  | 0 => .timeout
  | fuel + 1 =>
    match e with
    | .constant c _ => .ok (Const.toVal c)
    | .name id _ =>
      -- Resolution order: local env → module function table → builtin `len` → NameError.
      match Env.lookup env id with
      | some v => .ok v
      | Option.none =>
        if (findFunction m id).isSome then
          .unsupported s!"referencing function '{id}' as a value is outside the v0 tier"
        else if id == "len" then
          .unsupported "referencing builtin 'len' as a value is outside the v0 tier"
        else
          .exn (.nameError id)
    | .binOp l op r _ => do
        let a ← evalExpr m fuel env l
        let b ← evalExpr m fuel env r
        evalBinOp op a b
    | .unaryOp op operand _ => do
        let v ← evalExpr m fuel env operand
        evalUnaryOp op v
    | .boolOp op values _ =>
      match values.toList with
      | [] => .unsupported "BoolOp with no operands"
      | e :: es => evalBoolChain m fuel env op e es
    | .compare l ops comparators _ => do
        let a ← evalExpr m fuel env l
        evalCompareChain m fuel env a ops.toList comparators.toList
    | .call f args callUnsupported _ =>
      match callUnsupported with
      | some reason => .unsupported s!"call uses unsupported features: {reason}"
      | Option.none =>
        match f with
        | .name fname _ =>
          -- The callee NAME is resolved before the arguments (an unbound name
          -- is a NameError without evaluating args, CPython order), but the
          -- callable CHECK happens at call time, AFTER argument evaluation:
          -- `x(1//0)` with `x = 5` raises ZeroDivisionError, not TypeError.
          match Env.lookup env fname with
          | some v => do
              let _ ← evalExprs m fuel env args.toList
              .exn (.typeError s!"'{v.typeName}' object is not callable")
          | Option.none =>
            if (findFunction m fname).isSome then do
              let vs ← evalExprs m fuel env args.toList
              callFunction m fname vs.toArray fuel
            else if fname == "len" then do
              let vs ← evalExprs m fuel env args.toList
              match vs with
              | [v] => lenVal v
              | _ => .exn (.typeError s!"len() takes exactly one argument ({vs.length} given)")
            else
              .exn (.nameError fname)
        | f => .unsupported s!"calling a non-name expression ('{f.kindName}') is outside the v0 tier"
    | .list elts _ => do
        let vs ← evalExprs m fuel env elts.toList
        return .list vs.toArray
    | .tuple elts _ => do
        let vs ← evalExprs m fuel env elts.toList
        return .tuple vs.toArray
    | .subscript v idx _ => do
        let c ← evalExpr m fuel env v
        let i ← evalExpr m fuel env idx
        indexVal c i
    | .unsupported pyKind _ _ => .unsupported s!"unsupported expression '{pyKind}'"

/-- Evaluate a list of expressions left to right, each exactly once. -/
def evalExprs (m : Module) (fuel : Nat) (env : Env) (es : List Expr) : Res (List Val) :=
  match fuel with
  | 0 => .timeout
  | fuel + 1 =>
    match es with
    | [] => .ok []
    | e :: rest => do
        let v ← evalExpr m fuel env e
        let vs ← evalExprs m fuel env rest
        return v :: vs

/-- `and`/`or` chain: short-circuits and returns the deciding *operand value*
(not a bool): `0 or "x"` is `"x"`; the last operand is returned as-is. -/
def evalBoolChain (m : Module) (fuel : Nat) (env : Env) (op : BoolOp)
    (e : Expr) (rest : List Expr) : Res Val :=
  match fuel with
  | 0 => .timeout
  | fuel + 1 => do
    let v ← evalExpr m fuel env e
    match rest with
    | [] => .ok v
    | e' :: rest' =>
      match op with
      | .and => if truthy v then evalBoolChain m fuel env op e' rest' else .ok v
      | .or => if truthy v then .ok v else evalBoolChain m fuel env op e' rest'

/-- Chained comparison `a < b < c …`: each operand is evaluated exactly once,
left to right; short-circuits to `False` on the first failing link (the
remaining comparators are not evaluated). `lhs` is the already-evaluated
value of the previous operand. -/
def evalCompareChain (m : Module) (fuel : Nat) (env : Env) (lhs : Val)
    (ops : List CmpOp) (comparators : List Expr) : Res Val :=
  match fuel with
  | 0 => .timeout
  | fuel + 1 =>
    match ops, comparators with
    | [], [] => .ok (.bool true)
    | op :: ops', e :: rest => do
        let rhs ← evalExpr m fuel env e
        let b ← evalCompareOp op lhs rhs
        if b then evalCompareChain m fuel env rhs ops' rest
        else .ok (.bool false)
    | _, _ => .unsupported "Compare with mismatched ops/comparators"

/-- Execute one statement. Returns the updated environment and how control
continues (`Flow.next/ret/brk/cont`). -/
def execStmt (m : Module) (fuel : Nat) (env : Env) (s : Stmt) : Res (Env × Flow) :=
  match fuel with
  | 0 => .timeout
  | fuel + 1 =>
    match s with
    | .ret Option.none _ => .ok (env, .ret .none)
    | .ret (some e) _ => do
        let v ← evalExpr m fuel env e
        return (env, .ret v)
    | .assign targets value _ =>
      match targets.toList with
      | [t] => do
          -- CPython order: the value is evaluated before the store.
          let v ← evalExpr m fuel env value
          let env' ← assignTo env t v
          return (env', .next)
      | _ => .unsupported "chained assignment (multiple targets) is outside the v0 tier"
    | .augAssign target op value _ =>
      match target with
      | .name id _ =>
        -- CPython order: the target is loaded before the value is evaluated.
        match Env.lookup env id with
        | Option.none => .exn (.nameError id)
        | some (.list _) =>
            -- CPython `list += x` mutates the object IN PLACE (observable
            -- through aliases); the v0 value semantics would silently rebind
            -- only this name. Loud, not wrong: refuse the construct.
            -- (str/tuple/int/bool are immutable, so rebinding is faithful.)
            .unsupported
              "augmented assignment to a list ('+=' mutates in place, visible through aliases) is outside the v0 tier"
        | some old => do
            let v ← evalExpr m fuel env value
            let r ← evalBinOp op old v
            return (Env.set env id r, .next)
      | t => .unsupported s!"augmented assignment to '{t.kindName}' is outside the v0 tier"
    | .whileLoop test body orelse _ =>
      execWhile m fuel env test body.toList orelse.toList
    | .ifStmt test body orelse _ => do
        let t ← evalExpr m fuel env test
        if truthy t then execStmts m fuel env body.toList
        else execStmts m fuel env orelse.toList
    | .exprStmt e _ => do
        let _ ← evalExpr m fuel env e
        return (env, .next)
    | .pass _ => .ok (env, .next)
    | .brk _ => .ok (env, .brk)
    | .cont _ => .ok (env, .cont)
    | .unsupported pyKind _ _ => .unsupported s!"unsupported statement '{pyKind}'"

/-- Execute statements in order; stop at the first non-`next` flow (or error). -/
def execStmts (m : Module) (fuel : Nat) (env : Env) (ss : List Stmt) : Res (Env × Flow) :=
  match fuel with
  | 0 => .timeout
  | fuel + 1 =>
    match ss with
    | [] => .ok (env, .next)
    | s :: rest => do
        let (env', flow) ← execStmt m fuel env s
        match flow with
        | .next => execStmts m fuel env' rest
        | flow => .ok (env', flow)

/-- `while test: body else: orelse`. `break` exits the loop skipping `orelse`;
`continue` re-tests; `return` propagates; on normal exit (test falsy) the
`orelse` runs (a `break` inside it belongs to an enclosing loop and
propagates). -/
def execWhile (m : Module) (fuel : Nat) (env : Env) (test : Expr)
    (body orelse : List Stmt) : Res (Env × Flow) :=
  match fuel with
  | 0 => .timeout
  | fuel + 1 => do
    let t ← evalExpr m fuel env test
    if truthy t then do
      let (env', flow) ← execStmts m fuel env body
      match flow with
      | .next | .cont => execWhile m fuel env' test body orelse
      | .brk => .ok (env', .next)
      | .ret v => .ok (env', .ret v)
    else
      execStmts m fuel env orelse

/-- Call a module-level function by name with already-evaluated positional
arguments, in a fresh environment (v0: no globals, no closures; top-level
non-`def` statements are ignored). Falling off the end (or bare `return`)
yields `Val.none`. Unknown name → `NameError`; unsupported parameter features
(`argsOk = false`) → unsupported; arity mismatch → `TypeError`. -/
def callFunction (m : Module) (fname : String) (args : Array Val) (fuel : Nat) : Res Val :=
  match fuel with
  | 0 => .timeout
  | fuel + 1 =>
    match findFunction m fname with
    | Option.none => .exn (.nameError fname)
    | some f =>
      if !f.argsOk then
        .unsupported
          s!"function '{fname}' uses unsupported parameter features (defaults/varargs/kwargs/decorators)"
      else if !f.localsOk then
        .unsupported
          s!"function '{fname}' calls a name it also assigns (CPython static-locals rule) — outside the v0 tier"
      else if args.size ≠ f.params.size then
        .exn (.typeError
          s!"{fname}() takes {f.params.size} positional arguments but {args.size} were given")
      else do
        let (_, flow) ← execStmts m fuel (mkCallEnv f.params args) f.body.toList
        match flow with
        | .ret v => .ok v
        | .next => .ok .none
        | .brk => .unsupported "'break' outside loop"
        | .cont => .unsupported "'continue' outside loop"

end

end LeanModels.Python
