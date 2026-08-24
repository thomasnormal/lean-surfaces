import LeanModels.Es

/-!
# The object-destructuring inch's acceptance

`docs/backlog/es.md`'s `2026-08-24-es-4`. `ObjectPattern`,
`AssignmentPattern` defaults, and object rest — in BOTH forms, declaration
(§8.6.2 `BindingInitialization`) and assignment (§13.15.5
`DestructuringAssignmentEvaluation`).

Every expected value was read off a running engine in source spelling
before the Lean was written. The three that DISCRIMINATE — the default's
trigger, the default's laziness, and `BoundNames` over a pattern — are
called out where they appear.
-/

namespace Examples.es.destructuring

open LeanModels.Es

def sp : EsSpan := { start := 0, stop := 0, line := 0, col := 0, endLine := 0, endCol := 0 }

/-! ### Builders -/
def num (s : String) : Node := Node.lit (.number s) "" sp
def str (s : String) : Node := Node.lit (.string s) "" sp
def nul : Node := Node.lit .null "" sp
/-- `void 0`. **Not `ident "undefined"`** — in the language `undefined` is a
property of the global object, and this tier has no realm (inch 6), so the
identifier is genuinely unbound here and would be a `ReferenceError`. `void 0`
is the spelling that needs no binding, which is why minifiers use it. -/
def undef : Node :=
  Node.mk .unaryExpression sp [("operator", .str "void")] [("argument", [some (num "0")])]
def ident (n : String) : Node := Node.mk .identifier sp [("name", .str n)] []
def bin (op : String) (l r : Node) : Node :=
  Node.mk .binaryExpression sp [("operator", .str op)] [("left", [some l]), ("right", [some r])]
def assign (l r : Node) : Node :=
  Node.mk .assignmentExpression sp [("operator", .str "=")] [("left", [some l]), ("right", [some r])]
def member (o : Node) (k : String) : Node :=
  Node.mk .memberExpression sp [("computed", .bool false)]
    [("object", [some o]), ("property", [some (ident k)])]
def call (c : Node) (args : List Node) : Node :=
  Node.mk .callExpression sp [] [("callee", [some c]), ("arguments", args.map some)]

def prop (key : Node) (value : Node) (computed : Bool := false) : Node :=
  Node.mk .property sp [("kind", .str "init"), ("computed", .bool computed),
                        ("method", .bool false), ("shorthand", .bool false)]
    [("key", [some key]), ("value", [some value])]
def objE (ps : List Node) : Node := Node.mk .objectExpression sp [] [("properties", ps.map some)]
def arrE (es : List Node) : Node := Node.mk .arrayExpression sp [] [("elements", es.map some)]

/-- An `ObjectPattern`. Its `properties` are `Property` nodes whose `value`
is the TARGET, plus at most a trailing `RestElement`. -/
def objP (ps : List Node) : Node := Node.mk .objectPattern sp [] [("properties", ps.map some)]
/-- `AssignmentPattern` — a target with a default. -/
def defP (target : Node) (dflt : Node) : Node :=
  Node.mk .assignmentPattern sp [] [("left", [some target]), ("right", [some dflt])]
def restP (target : Node) : Node :=
  Node.mk .restElement sp [] [("argument", [some target])]
def arrP (ps : List Node) : Node := Node.mk .arrayPattern sp [] [("elements", ps.map some)]

def exprS (e : Node) : Node := Node.mk .expressionStatement sp [] [("expression", [some e])]
def decl (kind : String) (ds : List (Node × Option Node)) : Node :=
  Node.mk .variableDeclaration sp [("kind", .str kind)]
    [("declarations", ds.map fun (id, i) =>
        some (Node.mk .variableDeclarator sp [] [("id", [some id]), ("init", [i])]))]
def funcD (name : String) (ps : List String) (body : List Node) : Node :=
  Node.mk .functionDeclaration sp [("generator", .bool false), ("async", .bool false)]
    [("id", [some (ident name)]), ("params", ps.map (some ∘ ident)),
     ("body", [some (Node.mk .blockStatement sp [] [("body", body.map some)])])]
def ret (e : Node) : Node := Node.mk .returnStatement sp [] [("argument", [some e])]
def program (ss : List Node) : Node := Node.mk .program sp [] [("body", ss.map some)]

/-! ### Running -/

def prog (ss : List Node) : Option Val :=
  match SemM.run (ρ := Abrupt) (do
    let env ← newDeclarativeEnvironment none
    evalProgram 500 env (program ss)) default with
  | .ok (.ok (some v), _) => some v
  | _ => none

def progIs (ss : List Node) (v : Val) : Bool :=
  match prog ss with | some r => Val.sameValue r v | none => false

def progThrows (ss : List Node) (k : String) : Bool :=
  match SemM.run (ρ := Abrupt) (do
    let env ← newDeclarativeEnvironment none
    evalProgram 500 env (program ss)) default with
  | .ok (.error (.throw (.str s)), _) => s.startsWith k
  | _ => false

def progRefuses (ss : List Node) : Bool :=
  match SemM.run (ρ := Abrupt) (do
    let env ← newDeclarativeEnvironment none
    evalProgram 500 env (program ss)) default with
  | .error (.unsupported _ _ _) => true
  | _ => false

/-! ## Declaration form — §8.6.2 -/

/- `var {a, b} = {a:1, b:2}` — shorthand: key and value are the SAME
identifier node, so `BoundNames` must yield `a` once, not twice. -/
#guard progIs [decl "var" [(objP [prop (ident "a") (ident "a"),
                                  prop (ident "b") (ident "b")],
                            some (objE [prop (ident "a") (num "1"),
                                        prop (ident "b") (num "2")]))],
               exprS (bin "+" (ident "a") (ident "b"))] (.num 3.0)

/- **THE `BoundNames` DISCRIMINATOR.** `var {a: x} = {a:1}` binds `x` and
NOT `a`. Collecting a Property's KEY would hoist `a` too — and a hoisted
`a` initialized to `undefined` turns the ReferenceError below into a
silent `undefined`. -/
#guard progIs [decl "var" [(objP [prop (ident "a") (ident "x")],
                            some (objE [prop (ident "a") (num "1")]))],
               exprS (ident "x")] (.num 1.0)
#guard progThrows [decl "var" [(objP [prop (ident "a") (ident "x")],
                                some (objE [prop (ident "a") (num "1")]))],
                   exprS (ident "a")] "ReferenceError"

/- …and the same for a default's right-hand side: `var {a = b} = o` binds
`a` and READS `b`, so `b` must stay unbound. -/
#guard progThrows [decl "var" [(objP [prop (ident "a") (defP (ident "a") (num "1"))],
                                some (objE []))],
                   exprS (ident "b")] "ReferenceError"

/- The lexical form initializes a TDZ binding rather than assigning. -/
#guard progIs [decl "let" [(objP [prop (ident "a") (ident "a")],
                            some (objE [prop (ident "a") (num "7")]))],
               exprS (ident "a")] (.num 7.0)

/-! ### THE DEFAULT'S TRIGGER — §8.6.3 step 2

The test is on the FETCHED value, never on `HasProperty`. So an explicit
`undefined` fires the default and `null` does not. "If the key is absent,
use the default" gets the first of these wrong and answers `undefined`. -/

#guard progIs [decl "var" [(objP [prop (ident "a") (defP (ident "a") (num "5"))],
                            some (objE []))],
               exprS (ident "a")] (.num 5.0)
#guard progIs [decl "var" [(objP [prop (ident "a") (defP (ident "a") (num "5"))],
                            some (objE [prop (ident "a") undef]))],
               exprS (ident "a")] (.num 5.0)
#guard progIs [decl "var" [(objP [prop (ident "a") (defP (ident "a") (num "5"))],
                            some (objE [prop (ident "a") nul]))],
               exprS (ident "a")] .null

/-! ### THE DEFAULT IS LAZY

With the property PRESENT the initializer is not evaluated at all. Only a
side effect can see this, so an implementation that computes the default
and then overrides it passes every value test above and fails here. -/

#guard progIs [decl "var" [(ident "n", some (num "0"))],
               funcD "f" [] [exprS (assign (ident "n") (bin "+" (ident "n") (num "1"))),
                             ret (num "5")],
               decl "var" [(objP [prop (ident "q") (defP (ident "q") (call (ident "f") []))],
                            some (objE [prop (ident "q") (num "1")]))],
               exprS (ident "n")] (.num 0.0)
#guard progIs [decl "var" [(ident "n", some (num "0"))],
               funcD "f" [] [exprS (assign (ident "n") (bin "+" (ident "n") (num "1"))),
                             ret (num "5")],
               decl "var" [(objP [prop (ident "q") (defP (ident "q") (call (ident "f") []))],
                            some (objE []))],
               exprS (ident "n")] (.num 1.0)

/-! ### Computed keys, nesting, rest -/

#guard progIs [decl "var" [(objP [prop (bin "+" (str "x") (num "1")) (ident "v") true],
                            some (objE [prop (ident "x1") (num "7")]))],
               exprS (ident "v")] (.num 7.0)

#guard progIs [decl "var" [(objP [prop (ident "a") (objP [prop (ident "b") (ident "b")])],
                            some (objE [prop (ident "a")
                                          (objE [prop (ident "b") (num "9")])]))],
               exprS (ident "b")] (.num 9.0)

/- Object rest copies the own enumerable properties the pattern did NOT
take — §7.3.25 with the taken keys as `excludedItems`. -/
#guard progIs [decl "var" [(objP [prop (ident "a") (ident "a"), restP (ident "rest")],
                            some (objE [prop (ident "a") (num "1"),
                                        prop (ident "b") (num "2"),
                                        prop (ident "c") (num "3")]))],
               exprS (bin "+" (member (ident "rest") "b") (member (ident "rest") "c"))]
       (.num 5.0)
/- …and the taken key is EXCLUDED, not merely shadowed. -/
#guard progIs [decl "var" [(objP [prop (ident "a") (ident "a"), restP (ident "rest")],
                            some (objE [prop (ident "a") (num "1"),
                                        prop (ident "b") (num "2")]))],
               exprS (member (ident "rest") "a")] .undef

/- Destructuring is ordinary property reads, so it works on an Array. -/
#guard progIs [decl "var" [(objP [prop (ident "length") (ident "length")],
                            some (arrE [num "1", num "2", num "3"]))],
               exprS (ident "length")] (.num 3.0)

/-! ### `RequireObjectCoercible` — §7.2.1

`var {} = null` throws even though the pattern binds nothing; `var {} = {}`
is legal. -/

#guard progThrows [decl "var" [(objP [], some nul)]] "TypeError"
#guard progThrows [decl "var" [(objP [prop (ident "a") (ident "a")],
                                some undef)]] "TypeError"
#guard progIs [decl "var" [(objP [], some (objE []))], exprS (num "1")] (.num 1.0)

/-! ## Assignment form — §13.15.5

Same walk, different leaf: `PutValue` instead of a binding initialization. -/

#guard progIs [decl "var" [(ident "a", none), (ident "b", none)],
               exprS (assign (objP [prop (ident "a") (ident "a"),
                                    prop (ident "b") (ident "b")])
                             (objE [prop (ident "a") (num "1"),
                                    prop (ident "b") (num "2")])),
               exprS (bin "+" (ident "a") (ident "b"))] (.num 3.0)

/- **A MEMBER as a destructuring target** — `({a: o.p} = {a:3})`. This is
what the assignment form's leaf buys, and it needs no new machinery
because `evalRef`/`putValue` already handle member references. -/
#guard progIs [decl "var" [(ident "o", some (objE []))],
               exprS (assign (objP [prop (ident "a") (member (ident "o") "p")])
                             (objE [prop (ident "a") (num "3")])),
               exprS (member (ident "o") "p")] (.num 3.0)

/- A destructuring assignment's VALUE is the right-hand side (§13.15.2). -/
#guard progIs [decl "var" [(ident "a", none)],
               exprS (member (assign (objP [prop (ident "a") (ident "a")])
                                     (objE [prop (ident "a") (num "1")])) "a")] (.num 1.0)

/-! ## The boundary this inch does NOT cross -/

/- Array destructuring needs `GetIterator` (§7.4) — the iterator inch. -/
#guard progRefuses [decl "var" [(arrP [ident "a", ident "b"],
                                 some (arrE [num "1", num "2"]))]]

end Examples.es.destructuring
