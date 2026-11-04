import LeanModels.Es

/-!
# M2 inch 4(b)'s acceptance: the expression walk

`docs/backlog/es.md`'s inch 4(b). Nodes are built by hand here rather than
ingested, so the guards test the EVALUATOR and not the extractor — the
extractor has its own round-trip gate (`Examples/es/test262/`).

**These guards run through the compiler, not the kernel** — 2026-08-22-es-4
measured that `#guard` honours `@[extern]`. That is fine here and stated
rather than assumed: nothing below touches a float primitive, and the
evaluator is structurally recursive on fuel (never `partial`), so the same
claims are `rfl`-reachable when a lemma wants them.
-/

namespace Examples.es.eval

open LeanModels.Es

def sp : EsSpan := { start := 0, stop := 0, line := 0, col := 0, endLine := 0, endCol := 0 }

/-! ### Node builders -/
def lit (l : Lit) : Node := Node.lit l "" sp
def num (s : String) : Node := lit (.number s)
def str (s : String) : Node := lit (.string s)
def ident (n : String) : Node := Node.mk .identifier sp [("name", .str n)] []
def bin (op : String) (l r : Node) : Node :=
  Node.mk .binaryExpression sp [("operator", .str op)] [("left", [some l]), ("right", [some r])]
def logical (op : String) (l r : Node) : Node :=
  Node.mk .logicalExpression sp [("operator", .str op)] [("left", [some l]), ("right", [some r])]
def unary (op : String) (a : Node) : Node :=
  Node.mk .unaryExpression sp [("operator", .str op)] [("argument", [some a])]
def cond (t c a : Node) : Node :=
  Node.mk .conditionalExpression sp [] [("test", [some t]), ("consequent", [some c]), ("alternate", [some a])]
def assign (l r : Node) : Node :=
  Node.mk .assignmentExpression sp [("operator", .str "=")] [("left", [some l]), ("right", [some r])]
def member (o : Node) (k : String) : Node :=
  Node.mk .memberExpression sp [("computed", .bool false)]
    [("object", [some o]), ("property", [some (ident k)])]

/-- Evaluate in a fresh realm with one empty declarative environment. -/
def ev (n : Node) : Option Val :=
  match SemM.run (do
    let e ← newDeclarativeEnvironment none
    evalExpr 50 e n) default with
  | .ok (.ok v, _) => some v
  | _ => none

def evIs (n : Node) (v : Val) : Bool :=
  match ev n with | some r => Val.sameValue r v | none => false

def evThrows (n : Node) (k : String) : Bool :=
  match SemM.run (do
    let e ← newDeclarativeEnvironment none
    evalExpr 50 e n) default with
  | .ok (.error (.throw (.str s)), _) => s.startsWith k
  | _ => false

/-! ## Literals and operators -/

#guard evIs (num "42") (.num 42.0)
#guard evIs (str "hi") (.str "hi")
#guard evIs (lit .null) .null
#guard evIs (lit (.boolean true)) (.bool true)

#guard evIs (bin "+" (num "1") (num "2")) (.num 3.0)
#guard evIs (bin "-" (num "5") (num "2")) (.num 3.0)

/- `+` concatenates when either primitive is a String — §13.15.3 -/
#guard evIs (bin "+" (num "1") (str "2")) (.str "12")
/- …and every other operator goes numeric, so `1 - "2"` is `-1`. -/
#guard evIs (bin "-" (num "1") (str "2")) (.num (-1.0))

#guard evIs (bin "===" (num "1") (num "1")) (.bool true)
#guard evIs (bin "===" (num "1") (str "1")) (.bool false)
#guard evIs (bin "!==" (num "1") (str "1")) (.bool true)
#guard evIs (bin "<" (num "1") (num "2")) (.bool true)

/- NaN makes `<` FALSE, via `IsLessThan`'s third answer — §13.10.1 step 6. -/
#guard evIs (bin "<" (bin "/" (num "0") (num "0")) (num "1")) (.bool false)

/-! ## `typeof` — §13.5.1, and the row that needs a REFERENCE

`typeof undeclared` is `"undefined"`, NOT a `ReferenceError`. It is the one
operator that tolerates an unresolvable reference, and it only works because
`evalRef` builds the reference WITHOUT reading it. -/

#guard evIs (unary "typeof" (ident "neverDeclared")) (.str "undefined")
#guard evIs (unary "typeof" (num "1")) (.str "number")
#guard evIs (unary "typeof" (str "s")) (.str "string")
#guard evIs (unary "typeof" (lit .null)) (.str "object")

/- …but READING an undeclared name DOES throw — the same reference, read. -/
#guard evThrows (ident "neverDeclared") "ReferenceError"

#guard evIs (unary "!" (num "0")) (.bool true)
#guard evIs (unary "-" (num "5")) (.num (-5.0))
#guard evIs (unary "void" (num "5")) .undef

/-! ## SHORT-CIRCUITING — §13.13, and the right operand's world never exists

The right operand here is a read of an undeclared name, which THROWS if
evaluated. If these pass, the short-circuit is real and not a post-hoc
selection of an already-computed pair. -/

#guard evIs (logical "&&" (lit (.boolean false)) (ident "boom")) (.bool false)
#guard evIs (logical "||" (lit (.boolean true)) (ident "boom")) (.bool true)
#guard evIs (logical "??" (num "1") (ident "boom")) (.num 1.0)

/- …and when the left does NOT decide, the right IS evaluated — so the
guards above are not passing merely because the right is never reached. -/
#guard evThrows (logical "&&" (lit (.boolean true)) (ident "boom")) "ReferenceError"
#guard evThrows (logical "||" (lit (.boolean false)) (ident "boom")) "ReferenceError"

/-! ## The conditional operator — §13.14, also short-circuiting -/

#guard evIs (cond (lit (.boolean true)) (num "1") (ident "boom")) (.num 1.0)
#guard evIs (cond (num "0") (ident "boom") (num "2")) (.num 2.0)

/-! ## Assignment — §13.15.2 answers the VALUE, and writes through -/

#guard match SemM.run (do
    let e ← newDeclarativeEnvironment none
    envCreateMutableBinding e "x" false
    envInitializeBinding e "x" .undef
    let r ← evalExpr 50 e (assign (ident "x") (num "7"))
    let after ← lookupName 50 e "x"
    return (r, after)) default with
  | .ok (.ok (a, b), _) => Val.sameValue a (.num 7.0) && Val.sameValue b (.num 7.0)
  | _ => false

/-! ## Member access and calls -/

#guard match SemM.run (do
    let e ← newDeclarativeEnvironment none
    let o ← ordinaryObjectCreate none
    let _ ← ordinaryDefineOwnProperty o (.str "k") (PropDesc.data (.num 9.0) true true true)
    envCreateMutableBinding e "o" false
    envInitializeBinding e "o" (.obj o)
    evalExpr 50 e (member (ident "o") "k")) default with
  | .ok (.ok v, _) => Val.sameValue v (.num 9.0)
  | _ => false

/- A method call passes the RECEIVER as `this` — §13.3.6.1, which is what
`o.m()` means and a bare `f()` does not. -/
#guard match SemM.run (do
    let e ← newDeclarativeEnvironment none
    let f ← ordinaryFunctionCreate none (.builtin "%thisValue%") none .strict true
    let o ← ordinaryObjectCreate none
    let _ ← ordinaryDefineOwnProperty o (.str "m") (PropDesc.data (.obj f) true true true)
    envCreateMutableBinding e "o" false
    envInitializeBinding e "o" (.obj o)
    let call := Node.mk .callExpression sp [] [("callee", [some (member (ident "o") "m")]), ("arguments", [])]
    let got ← evalExpr 50 e call
    return Val.sameValue got (.obj o)) default with
  | .ok (.ok true, _) => true
  | _ => false

/- …while a BARE call passes `undefined` in strict mode. -/
#guard match SemM.run (do
    let e ← newDeclarativeEnvironment none
    let f ← ordinaryFunctionCreate none (.builtin "%thisValue%") none .strict true
    envCreateMutableBinding e "f" false
    envInitializeBinding e "f" (.obj f)
    let call := Node.mk .callExpression sp [] [("callee", [some (ident "f")]), ("arguments", [])]
    let got ← evalExpr 50 e call
    return Val.sameValue got .undef) default with
  | .ok (.ok true, _) => true
  | _ => false

/-! ## Fuel is an INDEX: exhaustion is `timeout`, never a wrong answer -/

#guard match SemM.run (do
    let e ← newDeclarativeEnvironment none
    evalExpr 0 e (num "1")) default with
  | .error .timeout => true
  | _ => false

end Examples.es.eval
