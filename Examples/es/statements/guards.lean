import LeanModels.Es

/-!
# M2 inch 5's acceptance: statements, declarations, and function bodies

`docs/backlog/es.md`'s `2026-08-23-es-0`. Nodes are built by hand, so
these test the EVALUATOR and not the extractor — the extractor has its own
round-trip gate in `Examples/es/test262/`.

**These guards run through the compiler, not the kernel** — `2026-08-22-es-4`
measured that `#guard` honours `@[extern]`, so it is not a kernel oracle.
That is stated rather than assumed: nothing below touches a float
primitive, and every function here is structurally recursive on fuel
(never `partial`), so the same claims stay `rfl`-reachable when a lemma
wants them.

What the file is FOR: the three claims of the inch. A statement's
completion value obeys `UpdateEmpty` rather than collapsing to
`undefined`; declarations are instantiated before any statement runs; and
an ECMAScript function body actually executes, which retires inch 3's
`OrdinaryCallEvaluateBody` refusal.
-/

namespace Examples.es.statements

open LeanModels.Es

def sp : EsSpan := { start := 0, stop := 0, line := 0, col := 0, endLine := 0, endCol := 0 }

/-! ### Expression builders -/
def num (s : String) : Node := Node.lit (.number s) "" sp
def str (s : String) : Node := Node.lit (.string s) "" sp
def bool (b : Bool) : Node := Node.lit (.boolean b) "" sp
def ident (n : String) : Node := Node.mk .identifier sp [("name", .str n)] []
def thisE : Node := Node.mk .thisExpression sp [] []
def bin (op : String) (l r : Node) : Node :=
  Node.mk .binaryExpression sp [("operator", .str op)] [("left", [some l]), ("right", [some r])]
def assign (l r : Node) : Node :=
  Node.mk .assignmentExpression sp [("operator", .str "=")] [("left", [some l]), ("right", [some r])]
def member (o : Node) (k : String) : Node :=
  Node.mk .memberExpression sp [("computed", .bool false)]
    [("object", [some o]), ("property", [some (ident k)])]
def call (callee : Node) (args : List Node) : Node :=
  Node.mk .callExpression sp [] [("callee", [some callee]), ("arguments", args.map some)]
def newE (callee : Node) (args : List Node) : Node :=
  Node.mk .newExpression sp [] [("callee", [some callee]), ("arguments", args.map some)]

/-! ### Statement builders -/
def exprS (e : Node) : Node := Node.mk .expressionStatement sp [] [("expression", [some e])]
def emptyS : Node := Node.mk .emptyStatement sp [] []
def block (ss : List Node) : Node := Node.mk .blockStatement sp [] [("body", ss.map some)]
def decl (kind : String) (ds : List (String × Option Node)) : Node :=
  Node.mk .variableDeclaration sp [("kind", .str kind)]
    [("declarations", ds.map fun (n, i) =>
        some (Node.mk .variableDeclarator sp []
                [("id", [some (ident n)]), ("init", [i])]))]
def ifS (t c : Node) (a : Option Node) : Node :=
  Node.mk .ifStatement sp []
    [("test", [some t]), ("consequent", [some c]), ("alternate", [a])]
def ret (e : Option Node) : Node := Node.mk .returnStatement sp [] [("argument", [e])]
def throwS (e : Node) : Node := Node.mk .throwStatement sp [] [("argument", [some e])]
def brk : Node := Node.mk .breakStatement sp [] [("label", [none])]
def cont : Node := Node.mk .continueStatement sp [] [("label", [none])]
def whileS (t b : Node) : Node :=
  Node.mk .whileStatement sp [] [("test", [some t]), ("body", [some b])]
def doWhileS (b t : Node) : Node :=
  Node.mk .doWhileStatement sp [] [("body", [some b]), ("test", [some t])]
def forS (i t u b : Option Node) : Node :=
  Node.mk .forStatement sp []
    [("init", [i]), ("test", [t]), ("update", [u]), ("body", [b])]
def tryS (b : Node) (h f : Option Node) : Node :=
  Node.mk .tryStatement sp [] [("block", [some b]), ("handler", [h]), ("finalizer", [f])]
def catchC (p : Option String) (b : Node) : Node :=
  Node.mk .catchClause sp [] [("param", [p.map ident]), ("body", [some b])]
def caseC (t : Option Node) (cs : List Node) : Node :=
  Node.mk .switchCase sp [] [("test", [t]), ("consequent", cs.map some)]
def switchS (d : Node) (cs : List Node) : Node :=
  Node.mk .switchStatement sp [] [("discriminant", [some d]), ("cases", cs.map some)]
def funcD (name : String) (params : List String) (body : List Node) : Node :=
  Node.mk .functionDeclaration sp [("generator", .bool false), ("async", .bool false)]
    [("id", [some (ident name)]), ("params", params.map (some ∘ ident)),
     ("body", [some (block body)])]
def funcE (params : List String) (body : List Node) : Node :=
  Node.mk .functionExpression sp [("generator", .bool false), ("async", .bool false)]
    [("id", [none]), ("params", params.map (some ∘ ident)), ("body", [some (block body)])]
def arrowE (params : List String) (body : Node) : Node :=
  Node.mk .arrowFunctionExpression sp
    [("generator", .bool false), ("async", .bool false), ("expression", .bool true)]
    [("params", params.map (some ∘ ident)), ("body", [some body])]

/-! ### Running a Script -/

def program (ss : List Node) : Node := Node.mk .program sp [] [("body", ss.map some)]

/-- The Script's outcome. `none` for anything that is not a normal
completion — the sharper predicates below say WHICH. -/
def prog (ss : List Node) : Option (Option Val) :=
  match SemM.run (ρ := Abrupt) (do
    let e ← newDeclarativeEnvironment none
    evalProgram 400 e (program ss)) default with
  | .ok (.ok v, _) => some v
  | _ => none

/-- The Script completes normally with this value. -/
def progIs (ss : List Node) (v : Val) : Bool :=
  match prog ss with | some (some r) => Val.sameValue r v | _ => false

/-- The Script completes normally and EMPTY — which is not `undefined`. -/
def progEmpty (ss : List Node) : Bool :=
  match prog ss with | some none => true | _ => false

/-- The Script throws, and the error's text starts with this class. -/
def progThrows (ss : List Node) (k : String) : Bool :=
  match SemM.run (ρ := Abrupt) (do
    let e ← newDeclarativeEnvironment none
    evalProgram 400 e (program ss)) default with
  | .ok (.error (.throw (.str s)), _) => s.startsWith k
  | _ => false

/-- The Script REFUSES — the loud, fuel-independent outcome. A guard that
asserts this is asserting a BOUNDARY, and it fails the day the boundary
moves, which is the point. -/
def progRefuses (ss : List Node) : Bool :=
  match SemM.run (ρ := Abrupt) (do
    let e ← newDeclarativeEnvironment none
    evalProgram 400 e (program ss)) default with
  | .error (.unsupported _ _ _) => true
  | _ => false

/-! ## Completion values — §14, and why `empty` is not `undefined`

The whole reason `evalStmt` answers `Option Val`. -/

#guard progIs [exprS (num "1")] (.num 1.0)
/- An empty Script completes EMPTY. -/
#guard progEmpty []
/- …and so does a lone `;` (§14.4.1) and an empty block (§14.2.2 step 1). -/
#guard progEmpty [emptyS]
#guard progEmpty [block []]
/- `UpdateEmpty`: an empty statement leaves the previous value standing. -/
#guard progIs [exprS (num "1"), emptyS] (.num 1.0)

/- **`if_cptn.json`'s clause.** §14.6.2 step 5 runs `UpdateEmpty(…,
undefined)`, so an `if` whose branch completes empty answers `undefined`
and ERASES the `1` before it. Collapsing `empty` into `undefined` at the
leaves would make this `1`, and collapsing it the other way would make it
`empty`; both are wrong and only the three-way distinction gets it right. -/
#guard progIs [exprS (num "1"), ifS (bool true) (block []) none] .undef
#guard progIs [exprS (num "2"), ifS (bool true) (block [exprS (num "3")]) none] (.num 3.0)
/- A false test with no `else` is the same clause. -/
#guard progIs [exprS (num "1"), ifS (bool false) (block [exprS (num "9")]) none] .undef

/-! ## Declarations -/

#guard progIs [decl "var" [("x", some (num "5"))], exprS (ident "x")] (.num 5.0)
#guard progIs [decl "let" [("x", some (num "5"))], exprS (ident "x")] (.num 5.0)
/- `let x;` initializes to `undefined`; `var x;` is a NO-OP (§14.3.2.1),
which is why it cannot clobber a value already there. -/
#guard progIs [decl "let" [("x", none)], exprS (ident "x")] .undef
#guard progIs [decl "var" [("x", some (num "1"))], decl "var" [("x", none)],
               exprS (ident "x")] (.num 1.0)

/- **The temporal dead zone.** The binding EXISTS (declaration
instantiation made it) but is uninitialized, so reading it is a
`ReferenceError` — not `undefined`, which is what `var` would give. -/
#guard progThrows [exprS (ident "x"), decl "let" [("x", some (num "1"))]] "ReferenceError"

/- `var` is function-scoped, so a `var` inside a block is visible after
it; a `let` is not. `Node.varNames` walking THROUGH blocks and stopping at
functions is what makes both true. -/
#guard progIs [block [decl "var" [("x", some (num "7"))]], exprS (ident "x")] (.num 7.0)
#guard progThrows [block [decl "let" [("x", some (num "7"))]], exprS (ident "x")]
        "ReferenceError"

/- A `const` cannot be assigned. -/
#guard progThrows [decl "const" [("c", some (num "1"))],
                   exprS (assign (ident "c") (num "2"))] "TypeError"

/-! ## Function bodies — inch 3's refusal, retired -/

#guard progIs [funcD "f" [] [ret (some (num "42"))], exprS (call (ident "f") [])] (.num 42.0)
/- HOISTING: the call is BEFORE the declaration's text. -/
#guard progIs [exprS (call (ident "f") []), funcD "f" [] [ret (some (num "1"))]] (.num 1.0)
/- A body with no `return` completes `undefined` (§10.2.1.4). -/
#guard progIs [funcD "f" [] [exprS (num "9")], exprS (call (ident "f") [])] .undef
/- Parameters: missing is `undefined`, extra is dropped. -/
#guard progIs [funcD "f" ["a", "b"] [ret (some (ident "b"))],
               exprS (call (ident "f") [num "1"])] .undef
#guard progIs [funcD "f" ["a"] [ret (some (ident "a"))],
               exprS (call (ident "f") [num "1", num "2"])] (.num 1.0)

/- CLOSURE: the inner function reads the outer binding through
`[[Environment]]`, which is why the value survives the outer call's
return. -/
#guard progIs [funcD "outer" [] [decl "let" [("n", some (num "3"))],
                                 ret (some (funcE [] [ret (some (ident "n"))]))],
               exprS (call (call (ident "outer") []) [])] (.num 3.0)

/- An arrow's concise body IS its return value — no statement list, no
`return` to absorb (§15.3.5 step 4). -/
#guard progIs [decl "let" [("f", some (arrowE ["x"] (bin "+" (ident "x") (num "1"))))],
               exprS (call (ident "f") [num "1"])] (.num 2.0)

/- `return` crosses a `try` — the handler re-raises what it does not want. -/
#guard progIs [funcD "f" [] [tryS (block [ret (some (num "1"))])
                                  (some (catchC (some "e") (block [ret (some (num "2"))]))) none],
               exprS (call (ident "f") [])] (.num 1.0)

/- **§10.2.2 step 13.** `new F()` answers the bound `this`, not the body's
`undefined`. -/
#guard progIs [funcD "F" [] [exprS (assign (member thisE "x") (num "8"))],
               exprS (member (newE (ident "F") []) "x")] (.num 8.0)

/-! ## Iteration -/

/- A counting loop, and the loop's completion value is the body's last
non-empty one (§14.7.1.1's `UpdateEmpty`). -/
#guard progIs [decl "var" [("i", some (num "0")), ("s", some (num "0"))],
               whileS (bin "<" (ident "i") (num "3"))
                 (block [exprS (assign (ident "s") (bin "+" (ident "s") (ident "i"))),
                         exprS (assign (ident "i") (bin "+" (ident "i") (num "1")))]),
               exprS (ident "s")] (.num 3.0)

/- `do…while` runs its body BEFORE the first test, which is the only thing
`testFirst` decides. -/
#guard progIs [decl "var" [("n", some (num "0"))],
               doWhileS (block [exprS (assign (ident "n") (bin "+" (ident "n") (num "1")))])
                 (bool false),
               exprS (ident "n")] (.num 1.0)

/- `break` ends the loop; `continue` skips to the update. -/
#guard progIs [decl "var" [("i", some (num "0"))],
               whileS (bool true)
                 (block [exprS (assign (ident "i") (bin "+" (ident "i") (num "1"))),
                         ifS (bin "<" (ident "i") (num "4")) (block [cont]) none,
                         brk]),
               exprS (ident "i")] (.num 4.0)

/- **`CreatePerIterationEnvironment`, §14.7.4.4.** The closure made in the
first iteration must see `0`, not the loop's final `2`. This is the guard
that fails the moment the per-iteration record is dropped and every
closure starts sharing one `i`. -/
#guard progIs [decl "var" [("f", none)],
               forS (some (decl "let" [("i", some (num "0"))]))
                    (some (bin "<" (ident "i") (num "2")))
                    (some (assign (ident "i") (bin "+" (ident "i") (num "1"))))
                    (some (block [ifS (bin "===" (ident "i") (num "0"))
                                   (block [exprS (assign (ident "f")
                                                    (funcE [] [ret (some (ident "i"))]))])
                                   none])),
               exprS (call (ident "f") [])] (.num 0.0)

/-! ### Loop and `switch` completion VALUES — §14.7.4.4, §14.12.4

These four are the guards that were MISSING when the first version of this
inch shipped, and their absence hid two wrong answers. `Abrupt.brk` carried
no value and `V` started at `empty` instead of `undefined`; both were
caught by reading §14.7.4.4 against the model rather than by any test
failing, which is why they are pinned here now. -/

/- **`V` starts at *undefined*, not `empty`** (§14.7.4.4 step 1). A loop
whose test is false at once therefore ERASES the value before it. -/
#guard progIs [exprS (num "1"), whileS (bool false) emptyS] .undef

/- **`UpdateEmpty` gives the `break` the list's value** (§14.2.2 step 3),
and §14.7.4.4 step 3.c hands it to the loop. Without the value field this
answered `undefined`. -/
#guard progIs [whileS (bool true) (block [exprS (num "5"), brk])] (.num 5.0)

/- A `continue` carries its value the same way, through step 3.d. -/
#guard progIs [decl "var" [("i", some (num "0"))],
               whileS (bin "<" (ident "i") (num "2"))
                 (block [exprS (assign (ident "i") (bin "+" (ident "i") (num "1"))),
                         exprS (num "7"), cont])] (.num 7.0)

/- `switch` reads it back through §14.12.4's own `UpdateEmpty(R, V)`. -/
#guard progIs [switchS (num "1")
                 [caseC (some (num "1")) [exprS (num "5"), brk]]] (.num 5.0)
/- …and a `switch` that matches nothing completes `undefined`, never
`empty`, because its `V` starts there too. -/
#guard progIs [exprS (num "1"), switchS (num "9") []] .undef

/-! ## `try`/`catch`/`finally` — §14.15 -/

#guard progIs [tryS (block [throwS (str "boom")])
                    (some (catchC (some "e") (block [exprS (ident "e")]))) none] (.str "boom")
/- An optional binding (`catch {}`) skips the record entirely. -/
#guard progIs [tryS (block [throwS (str "x")])
                    (some (catchC none (block [exprS (num "1")]))) none] (.num 1.0)
/- The state SURVIVES the throw: the write before it is still there. -/
#guard progIs [decl "var" [("n", some (num "0"))],
               tryS (block [exprS (assign (ident "n") (num "5")), throwS (str "x")])
                    (some (catchC none (block []))) none,
               exprS (ident "n")] (.num 5.0)
/- The finalizer's own abrupt completion WINS — §14.15.3 step 7. -/
#guard progIs [funcD "f" [] [tryS (block [ret (some (num "1"))]) none
                                  (some (block [ret (some (num "2"))]))],
               exprS (call (ident "f") [])] (.num 2.0)
/- …and it runs on the throwing path too, without swallowing the throw. -/
#guard progThrows [decl "var" [("n", some (num "0"))],
                   tryS (block [throwS (str "TypeError: x")]) none
                        (some (block [exprS (assign (ident "n") (num "1"))]))] "TypeError"

/-! ## `switch` — §14.12.4 -/

/- FALL-THROUGH: a matched case runs every consequent after it too. -/
#guard progIs [decl "var" [("s", some (str ""))],
               switchS (num "1")
                 [caseC (some (num "1")) [exprS (assign (ident "s") (bin "+" (ident "s") (str "a")))],
                  caseC (some (num "2")) [exprS (assign (ident "s") (bin "+" (ident "s") (str "b")))]],
               exprS (ident "s")] (.str "ab")
/- `break` stops it. -/
#guard progIs [decl "var" [("s", some (str ""))],
               switchS (num "1")
                 [caseC (some (num "1"))
                    [exprS (assign (ident "s") (bin "+" (ident "s") (str "a"))), brk],
                  caseC (some (num "2")) [exprS (assign (ident "s") (bin "+" (ident "s") (str "b")))]],
               exprS (ident "s")] (.str "a")
/- **`default` IN THE MIDDLE.** No case matches, so execution starts at
the default and falls through what follows it — but NOT through the case
before it. -/
#guard progIs [decl "var" [("s", some (str ""))],
               switchS (num "9")
                 [caseC (some (num "1")) [exprS (assign (ident "s") (bin "+" (ident "s") (str "a")))],
                  caseC none [exprS (assign (ident "s") (bin "+" (ident "s") (str "d")))],
                  caseC (some (num "2")) [exprS (assign (ident "s") (bin "+" (ident "s") (str "b")))]],
               exprS (ident "s")] (.str "db")
/- Matching is STRICT (§14.12.4 step 6.a.i.1), so `"1"` misses `1`. -/
#guard progIs [decl "var" [("s", some (str ""))],
               switchS (str "1")
                 [caseC (some (num "1")) [exprS (assign (ident "s") (str "a"))],
                  caseC none [exprS (assign (ident "s") (str "d"))]],
               exprS (ident "s")] (.str "d")

/-! ## The boundaries this inch does NOT cross

Each of these is a REFUSAL, not a wrong answer. A guard that asserts a
refusal is asserting where the tier stops, and it fails the day the
boundary moves — which is how the scoreboard stays honest. -/

/- The `arguments` object needs `%Object.prototype%` and `@@iterator`. -/
#guard progRefuses [funcD "f" [] [ret (some (ident "arguments"))],
                    exprS (call (ident "f") [])]
/- A non-simple parameter list — a default is an `AssignmentPattern`, and
it needs its own environment (§10.2.11 step 28). -/
#guard progRefuses
  [Node.mk .functionDeclaration sp [("generator", .bool false), ("async", .bool false)]
     [("id", [some (ident "f")]),
      ("params", [some (Node.mk .assignmentPattern sp []
                          [("left", [some (ident "a")]), ("right", [some (num "1")])])]),
      ("body", [some (block [ret (some (ident "a"))])])],
   exprS (call (ident "f") [])]
/- A generator. -/
#guard progRefuses
  [Node.mk .functionDeclaration sp [("generator", .bool true), ("async", .bool false)]
     [("id", [some (ident "g")]), ("params", []), ("body", [some (block [])])]]
/- A statement kind outside the modeled set — `for…of` needs the iterator
protocol (§7.4). -/
#guard progRefuses [Node.mk .forOfStatement sp [] [("left", [some (ident "x")]),
                                                   ("right", [some (ident "y")]),
                                                   ("body", [some (block [])])]]
/- An unsupported node INGESTS and refuses at evaluation, never at ingest. -/
#guard progRefuses [exprS (Node.unsupported "AwaitExpression" "await x" sp)]

end Examples.es.statements
