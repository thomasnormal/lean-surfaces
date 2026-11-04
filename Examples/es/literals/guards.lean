import LeanModels.Es

/-!
# The data-literal inch's acceptance

`docs/backlog/es.md`'s `2026-08-24-es-1`. Object and array literals,
`UpdateExpression`, and the Array exotic object's live `length`.

**Every expected value below was read off a running engine in source
spelling before the Lean was written**, not derived from the prose. The
table is in the inch's design note; the three that discriminate are called
out where they appear.

These guards run through the compiler, not the kernel (`2026-08-22-es-4`
measured that `#guard` honours `@[extern]`). Nothing here touches a float
primitive except through `isExactUint32`, which is a `Float.Model` round
trip precisely so it stays kernel-reachable.
-/

namespace Examples.es.literals

open LeanModels.Es

def sp : EsSpan := { start := 0, stop := 0, line := 0, col := 0, endLine := 0, endCol := 0 }

/-! ### Builders -/
def num (s : String) : Node := Node.lit (.number s) "" sp
def str (s : String) : Node := Node.lit (.string s) "" sp
def ident (n : String) : Node := Node.mk .identifier sp [("name", .str n)] []
def bin (op : String) (l r : Node) : Node :=
  Node.mk .binaryExpression sp [("operator", .str op)] [("left", [some l]), ("right", [some r])]
def assign (l r : Node) : Node :=
  Node.mk .assignmentExpression sp [("operator", .str "=")] [("left", [some l]), ("right", [some r])]
def memberC (o : Node) (k : Node) : Node :=
  Node.mk .memberExpression sp [("computed", .bool true)] [("object", [some o]), ("property", [some k])]
def member (o : Node) (k : String) : Node :=
  Node.mk .memberExpression sp [("computed", .bool false)]
    [("object", [some o]), ("property", [some (ident k)])]
def update (op : String) (prefix_ : Bool) (a : Node) : Node :=
  Node.mk .updateExpression sp [("operator", .str op), ("prefix", .bool prefix_)]
    [("argument", [some a])]

/-- A `Property` in an object literal. `key` is an Identifier unless
`computed`, in which case it is an arbitrary expression. -/
def prop (key : Node) (value : Node) (computed : Bool := false) : Node :=
  Node.mk .property sp [("kind", .str "init"), ("computed", .bool computed),
                        ("method", .bool false), ("shorthand", .bool false)]
    [("key", [some key]), ("value", [some value])]
def obj (ps : List Node) : Node :=
  Node.mk .objectExpression sp [] [("properties", ps.map some)]
/-- An array literal. `none` is an ELISION and must stay one. -/
def arr (es : List (Option Node)) : Node :=
  Node.mk .arrayExpression sp [] [("elements", es)]

def exprS (e : Node) : Node := Node.mk .expressionStatement sp [] [("expression", [some e])]
def decl (kind : String) (ds : List (String × Option Node)) : Node :=
  Node.mk .variableDeclaration sp [("kind", .str kind)]
    [("declarations", ds.map fun (n, i) =>
        some (Node.mk .variableDeclarator sp [] [("id", [some (ident n)]), ("init", [i])]))]
def program (ss : List Node) : Node := Node.mk .program sp [] [("body", ss.map some)]

/-! ### Running -/

/-- Evaluate an expression, then ask a question of the world it left. -/
def probe (e : Node) (q : Val → EsW α) : Option α :=
  match SemM.run (ρ := Abrupt) (do
    let env ← newDeclarativeEnvironment none
    q (← evalExpr 200 env e)) default with
  | .ok (.ok a, _) => some a
  | _ => none

/-- The object's own keys, in `OrdinaryOwnPropertyKeys` order (§10.1.11.1) —
the observable a naive association list gets wrong. -/
def keysOf (e : Node) : Option (List String) :=
  probe e fun v =>
    match v with
    | .obj r => do return (← ordinaryOwnPropertyKeys r).map PropKey.text
    | _ => SemM.refuseConstruct "not an object"

/-- One own property's value, or `none` when the property is ABSENT — which
is a different answer from `undefined` and is the whole point for a hole. -/
def ownOf (e : Node) (k : String) : Option (Option Val) :=
  probe e fun v =>
    match v with
    | .obj r => do return (← ordinaryGetOwnProperty r (.str k)).bind (·.value)
    | _ => SemM.refuseConstruct "not an object"

/-- One own property's full descriptor. -/
def descOf (e : Node) (k : String) : Option (Option PropDesc) :=
  probe e fun v =>
    match v with
    | .obj r => do return (← ordinaryGetOwnProperty r (.str k))
    | _ => SemM.refuseConstruct "not an object"

/-- An own property's value, compared by `SameValue`.

**`Val` derives no `BEq`, deliberately** — §7.2.9's `SameValue`, §7.2.10's
`SameValueZero` and §7.2.11's `IsStrictlyEqual` disagree on `NaN` and `±0`,
so the tier refuses to pick one behind the caller's back. `PropDesc` has
none either, so its attributes are compared field-wise below. -/
def ownIs (e : Node) (k : String) (v : Val) : Bool :=
  match ownOf e k with | some (some r) => Val.sameValue r v | _ => false

/-- The property is ABSENT — which is not the same answer as `undefined`,
and is the whole point for an elision. -/
def ownAbsent (e : Node) (k : String) : Bool :=
  match ownOf e k with | some none => true | _ => false

/-- A descriptor, value by `SameValue` and attributes by `BEq`. -/
def descIs (e : Node) (k : String) (v : Val) (w en c : Bool) : Bool :=
  match descOf e k with
  | some (some d) =>
    (match d.value with | some x => Val.sameValue x v | none => false)
      && d.writable == some w && d.enumerable == some en && d.configurable == some c
  | _ => false

/-- Run a Script and report its completion value. -/
def prog (ss : List Node) : Option Val :=
  match SemM.run (ρ := Abrupt) (do
    let env ← newDeclarativeEnvironment none
    evalProgram 400 env (program ss)) default with
  | .ok (.ok (some v), _) => some v
  | _ => none

def progIs (ss : List Node) (v : Val) : Bool :=
  match prog ss with | some r => Val.sameValue r v | none => false

def refuses (e : Node) : Bool :=
  match SemM.run (ρ := Abrupt) (do
    let env ← newDeclarativeEnvironment none
    evalExpr 200 env e) default with
  | .error (.unsupported _ _ _) => true
  | _ => false

/-! ## Object literals — §13.2.5

### THE FOUR-WAY DISCRIMINATOR

`{ b:1, 2:2, 1:3, a:4, b:5 }`. Integer-index keys come first in ASCENDING
NUMERIC order, then string keys in CREATION order — and a duplicate key
UPDATES in place rather than moving, so `b` keeps the slot it took first
while taking the LAST value. Four plausible implementations, four different
wrong answers:

* append, no sort            → `["b","2","1","a","b"]`  (duplicate, unsorted)
* insertion order + dedupe   → `["b","2","1","a"]`      (indices not hoisted)
* index sort, dedupe-to-end  → `["1","2","a","b"]`      (`b` moved past `a`)
* **the spec**               → `["1","2","b","a"]`

Testable here WITHOUT the realm: these guards are Lean, so they ask
`ordinaryOwnPropertyKeys` directly instead of needing `Object.keys`, which
is an inch-6 intrinsic. -/

#guard keysOf (obj [prop (ident "b") (num "1"), prop (num "2") (num "2"),
                    prop (num "1") (num "3"), prop (ident "a") (num "4"),
                    prop (ident "b") (num "5")])
       == some ["1", "2", "b", "a"]
/- …and the duplicate takes the LAST value while keeping the FIRST slot. -/
#guard ownIs (obj [prop (ident "b") (num "1"), prop (num "2") (num "2"),
                   prop (num "1") (num "3"), prop (ident "a") (num "4"),
                   prop (ident "b") (num "5")]) "b" (.num 5.0)

#guard keysOf (obj []) == some []

/- A numeric literal key becomes the STRING `"2"`, which is then an array
index — that is the mechanism that puts it before `"b"`. -/
#guard keysOf (obj [prop (ident "b") (num "1"), prop (num "2") (num "2")])
       == some ["2", "b"]

/- A COMPUTED key is evaluated and run through `ToPropertyKey`. -/
#guard keysOf (obj [prop (bin "+" (str "x") (num "1")) (num "7") true])
       == some ["x1"]

/- An IDENTIFIER key is its own text and is NOT evaluated: `{a: 1}` does
not read a binding `a`, so this cannot be a ReferenceError. -/
#guard keysOf (obj [prop (ident "a") (num "1")]) == some ["a"]

/-! ## Array literals — §13.2.4

### THE ELISION DISCRIMINATOR

`[1, , 3]` has `length` 3 and **no own property at index 1**. Dropping the
hole gives `[1, 3]` (length 2); filling it with `undefined` gives an own
property that should not exist. Only a hole that survives ingestion AND
evaluation is right. -/

#guard ownIs (arr [some (num "1"), none, some (num "3")]) "length" (.num 3.0)
/- The hole is ABSENT, not `undefined` — `none` here is "no such property". -/
#guard ownAbsent (arr [some (num "1"), none, some (num "3")]) "1"
#guard ownIs (arr [some (num "1"), none, some (num "3")]) "2" (.num 3.0)

#guard ownIs (arr [some (num "10"), some (num "20")]) "length" (.num 2.0)
#guard ownIs (arr []) "length" (.num 0.0)
/- A trailing comma is NOT an element: `[1,2,3,]` has length 3. The parser
gives three elements, so this pins that nothing invents a fourth. -/
#guard ownIs (arr [some (num "1"), some (num "2"), some (num "3")]) "length" (.num 3.0)
/- A TRAILING elision does count — `[1, ,]`'s length is 2 — which is why
`length` is set from the counter after the loop and not from the writes. -/
#guard ownIs (arr [some (num "1"), none]) "length" (.num 2.0)

/-! ### The descriptors — §10.4.2.2 step 6, §10.4.2.1

`length` is writable but NOT enumerable and NOT configurable; an index is
all three. Getting `length` enumerable would put it in every `for…in`. -/

#guard descIs (arr [some (num "1")]) "length" (.num 1.0) true false false
#guard descIs (arr [some (num "1")]) "0" (.num 1.0) true true true

/-! ## The live `length`, both directions — §10.4.2.1, §10.4.2.4

An ordinary object with a `length` data property fails BOTH of these, which
is why `Obj` carries `ExoticKind`. -/

/- GROWTH: writing an index at or past the end moves `length` to index + 1. -/
#guard progIs [decl "var" [("a", some (arr [some (num "10"), some (num "20")]))],
               exprS (assign (memberC (ident "a") (num "5")) (num "99")),
               exprS (member (ident "a") "length")] (.num 6.0)

/- TRUNCATION: writing a smaller `length` DELETES the elements above it.
`hasOwnProperty(1)` must go false — renumbering alone is not enough. -/
#guard progIs [decl "var" [("a", some (arr [some (num "10"), some (num "20")]))],
               exprS (assign (member (ident "a") "length") (num "1")),
               exprS (memberC (ident "a") (num "1"))] .undef
#guard progIs [decl "var" [("a", some (arr [some (num "10"), some (num "20")]))],
               exprS (assign (member (ident "a") "length") (num "1")),
               exprS (member (ident "a") "length")] (.num 1.0)
/- …and the survivor is untouched. -/
#guard progIs [decl "var" [("a", some (arr [some (num "10"), some (num "20")]))],
               exprS (assign (member (ident "a") "length") (num "1")),
               exprS (memberC (ident "a") (num "0"))] (.num 10.0)

/-! ### `ToUint32` is a FIXPOINT test, not a range check — §10.4.2.4 step 5 -/

#guard isExactUint32 0.0
#guard isExactUint32 4294967295.0
#guard !isExactUint32 4294967296.0
#guard !isExactUint32 (-1.0)
#guard !isExactUint32 1.5
/- The one the `@[extern]` path would get wrong: `n.toInt64` SATURATES to
`2^63 - 1`, which then passes a naive range check. A round trip through
`Float.Model` refuses it. -/
#guard !isExactUint32 1e30

/-! ## `UpdateExpression` — §13.4.2 – §13.4.5

### THE ToNumeric DISCRIMINATOR

`s = "3"; s++` answers the **Number** `3`, not the string `"3"`. §13.4.3.1
runs `ToNumeric` BEFORE choosing the answer, so an implementation that
saves the old value and converts afterwards returns a string and is wrong
in a way no numeric test would catch. -/

#guard progIs [decl "var" [("s", some (str "3"))], exprS (update "++" false (ident "s"))]
       (.num 3.0)
#guard progIs [decl "var" [("s", some (str "3"))], exprS (update "++" false (ident "s")),
               exprS (ident "s")] (.num 4.0)

/- Postfix answers the OLD value, prefix the NEW. -/
#guard progIs [decl "var" [("x", some (num "5"))], exprS (update "++" false (ident "x"))]
       (.num 5.0)
#guard progIs [decl "var" [("x", some (num "5"))], exprS (update "++" false (ident "x")),
               exprS (ident "x")] (.num 6.0)
#guard progIs [decl "var" [("y", some (num "5"))], exprS (update "++" true (ident "y"))]
       (.num 6.0)
#guard progIs [decl "var" [("z", some (num "5"))], exprS (update "--" false (ident "z")),
               exprS (ident "z")] (.num 4.0)

/- It works through a member reference too — the reference machinery is
shared with assignment. -/
#guard progIs [decl "var" [("a", some (arr [some (num "7")]))],
               exprS (update "++" true (memberC (ident "a") (num "0")))] (.num 8.0)

/-! ## The boundaries this inch does NOT cross -/

/- Spread needs the iterator protocol (§7.4). -/
#guard refuses (arr [some (Node.mk .spreadElement sp [] [("argument", [some (ident "a")])])])
/- A getter in an object literal needs the accessor path (2026-08-23-es-1). -/
#guard refuses (Node.mk .objectExpression sp []
  [("properties", [some (Node.mk .property sp
      [("kind", .str "get"), ("computed", .bool false), ("method", .bool false),
       ("shorthand", .bool false)]
      [("key", [some (ident "g")]), ("value", [some (num "1")])])])])

end Examples.es.literals
