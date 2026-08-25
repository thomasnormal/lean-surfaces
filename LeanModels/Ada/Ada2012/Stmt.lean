import LeanModels.Ada.Ada2012.Value

/-!
# M2 inch 2 — `W`, and the first three statement rules (ARM 5.1-5.3)

`docs/ada-semantics-design.md` §3 rung 2; the census that scoped it is
`docs/backlog/ada.md` §2026-08-24-ada-2. **58 ARM paragraphs, 4.05% of the
corpus's nodes, and a reach of ZERO** — inch 2 grades no ACATS test, because
all 1,374 v0 tests call `Report`, which needs inches 3 and 5. That was said
before the rung was built rather than after it disappointed.

## THE RANGE IS ADA 2012's

**A paragraph range is edition-relative**, so a rung scoped by clause number
is scoped in an edition or it is not scoped at all. Ada 2022 numbers a
**5.2.1 Target Name Symbols** between 5.2 and 5.3; this tier is Ada 2012 and
that subclause is not in it. Settled by measurement rather than assertion:
libadalang 26 parses Ada 2022 and has a `TargetName` node, and the construct
census records **zero of them in 4,821 ACATS sources** (with zero `DeclExpr`,
`ReduceAttributeRef`, `ParallelLoopStmt` and `ParallelBlockStmt` beside it).

## EVERY NODE SHAPE BELOW WAS READ OFF A REAL ENVELOPE, NOT RECALLED

The walker dispatches on `kind` strings because `LeanModels/Ada/Ast.lean` is
kind-agnostic — 280 kinds reached by the corpus made 280 constructors a
transcription — and that file names the consequence as M2's problem: *a
semantics built on this must pattern-match on strings and have a loud
default*. The shapes were extracted from `Examples/ada/report/report.json`
and `Examples/ada/b371001/b371001.json` (3,505 nodes) rather than assumed:

| kind | shape | count in the two fixtures |
| --- | --- | ---: |
| `AssignStmt` | 2 children: target, expression | 49, all arity 2 |
| `IfStmt` | 4 children: condition, `StmtList`, elsif list, else-or-`null` | 31, all arity 4 |
| `ElsifStmtPart` | 2 children: condition, `StmtList` | 2 |
| `ElsePart` | 1 child: `StmtList` | 9 |
| `RelationOp` / `BinOp` | 3 children: left, **operator leaf**, right | 24 / 84 |
| `UnOp` | 2 children: operator leaf, operand | 3 |
| `Identifier` / `IntLiteral` | **leaves** carrying source text | 794 / 110 |

**AND THE TRAP THAT CENSUS-FIRST CAUGHT: AN EMPTY LIST IS A LEAF, NOT AN
EMPTY NODE.** `extractors/ada/extract.py` emits `children` when a node has
children and `text` otherwise — so an `if` with no `elsif` carries
`ElsifStmtPartList` as a **leaf with empty text**. Measured: **30 of 31**
`ElsifStmtPartList` nodes in the fixtures are leaves. A walker matching
`.node "ElsifStmtPartList" _ #[]` would have matched **one** `if` in
thirty-one and refused the rest, and it would have looked like a semantics
bug rather than an encoding one. Cross-checked on the else slot too: 31
`IfStmt` minus 9 `ElsePart` is exactly the 22 `null` children the extractor
emits under `IfStmt`.

## FUEL IS AN INDEX, AND THAT IS WHAT KEEPS THE GATE KERNEL-REDUCIBLE

`Value.lean` records the family rule — fuel indexes the step function and is
never a monad layer — and inch 2 is where it becomes load-bearing for a
second reason: `Ast.lean`'s own walkers are `partial`, and **a `partial`
definition is opaque to the kernel, so a `#guard` stated through one cannot
reduce**. Every function here is structurally recursive on `fuel`, which is
what lets the gate below run the interpreter instead of admiring it.

`execStmts` is ONE function over a statement LIST rather than a mutual pair
over a statement and a list, and `elsif` is handled by **lowering** rather
than by a second entry point: ARM 5.3's `elsif` is a nested `if`, so the rule
rebuilds it as one. That keeps the whole statement tier structurally
recursive on a single argument.

## WHAT INCH 2 REFUSES, AND WHY EACH REFUSAL IS A MEASUREMENT

Refusals cite the clause and travel on `π` (`RefusalCause.unsupported`),
never on `ρ` — `ρ` is the language's own raise and belongs to
`Constraint_Error`. The largest deliberate refusal is the one the census
named:

> **A non-simple-name assignment target is REFUSED, citing ARM 5.2, until the
> target-child-kind census extension runs.** `docs/ada-construct-census.json`
> is a flat kind-frequency map with no parent-child structure, so it knows
> there are 20,529 `AssignStmt` and cannot say how many assign into a simple
> name rather than an indexed or selected component — and `CallExpr`
> (96,592) is libadalang's node for **both** a call and an indexed component,
> so even a parent pass must disambiguate by resolution. **A refusal is how a
> pending measurement is carried in the model rather than in a note**: it is
> honest, it is countable, and the next census reads the number off the model
> instead of re-deriving it from the corpus.

`CallStmt` (56,062, **2.7× the assignments**) and `HandledStmts` (26,386) are
refused as inches 3 and 4. Logical operators (`and`, `or`, `not` beyond the
unary case, `and then`, `or else`) are ARM 4.5.1 and outside the range.
-/

namespace LeanModels.Ada.Ada2012

/-! ## §1 THE ACAA EVENT-TRACE ROW — in `W` from the first statement rule

**The trace is in `W` from the first statement rule, and this is that rule.**
Ada's scoreboard computes no verdict: it emits the ACAA's event-trace rows and
lets `GRADE` decide (`docs/backlog.md` §L69). An emitter is not retrofittable
— if the trace is not in `W` when the first rule is written, every rule is
revisited to add it — so the component lands now even though **nothing emits
a row at inch 2**.

**`kind` IS A STRING, DELIBERATELY, AND THE REASON IS THE SAME ONE THE RE-
ACQUIRE RUNG NAMES.** The row vocabulary is fixed by the ACAA's own grading
tool, which **is not on this machine** — the scratchpad purge took the ACATS
delivery with it. Enumerating ten constructors from a secondary source would
be a vocabulary claim quoted from memory, which is precisely what this tier's
kind-agnostic AST exists to avoid one level down. It becomes an inductive at
inch 5, when the tool is re-acquired and the set can be CHECKED. -/
structure TraceRow where
  /-- The ACAA row tag (`CSTART`, `CEND`, `CERR`, ...), unverified until the
  grading tool is re-acquired. -/
  kind : String
  /-- Where it happened. A `CERR` row carries a line AND a position, and the
  ACATS User's Guide calls the line critical to the grading tool. -/
  span : AdaSpan
  detail : String
  deriving Repr, Inhabited, BEq, DecidableEq

/-! ## §2 `W` — the Ada store, with one component live and three declared

`docs/ada-semantics-design.md` §1.1 fixes four components. Inch 2 writes
exactly one of them and declares the rest, because the cost of declaring them
now is a field and the cost of adding them later is every rule. -/

/-- The Ada world.

* **`objects` — LIVE.** A scoped map of named objects, **not** a
  byte-addressed heap: v0 has no `'Address` pressure (Clause 13 is out of v0
  and the 1,374-test target reaches it nowhere), which is the C tier's
  §2.2(b) decision arriving at the opposite answer for a different language.
  It is an association list at inch 2 because inch 2 has **no scoping
  construct** — blocks are ARM 5.6 and subprograms are inch 3 — so a nesting
  structure would be a shape with nothing to nest. It gains scopes with the
  construct that needs them.
* **`elaborated` — declared, unwritten until inch 9.** Elaboration order is
  data the tier was HANDED, not derived: §L74 measured that **680 of 4,810
  ACATS files, one in seven, have a name that is not among their unit
  names**, so it cannot be re-derived from paths.
* **`output` — declared, unwritten until `Report` lands at inch 5.**
* **`trace` — declared, unwritten, and the reason §1 exists.** -/
structure AdaWorld where
  objects : List (String × Val) := []
  /-- **Inch 3.** The call stack's locals, innermost first. Separate from
  `objects` rather than replacing it: inch 3 models no nested subprogram, so a
  static chain would be a shape with nothing to chain. A lookup searches the
  innermost frame and then the outer store, and every inch-2 guard is
  unaffected because the default is `[]`. -/
  frames : List (List (String × Val)) := []
  elaborated : List String := []
  output : List String := []
  trace : List TraceRow := []
  deriving Repr, Inhabited, BEq, DecidableEq

/-! ## §3 IDENTIFIERS ARE CASE-INSENSITIVE, and this is a STANDARD fact with NO corpus witness

ARM 2.3: identifiers differing only in case are the same identifier. Every
lookup and every store folds case, because a case-SENSITIVE store would model
a language Ada is not.

**Measured, and the measurement is negative:** across both fixtures there are
**131 distinct case-folded identifiers and ZERO spelled in more than one
case**. So this decision comes from the STANDARD and not from the corpus,
which is worth stating rather than blurring — the census doc's own rule is
that a missing corpus witness relocates a discriminator, never removes it.
The witness should exist corpus-wide (ACATS's legacy tests are upper-case and
its modern ones are mixed), and checking it is part of the re-acquire rung. -/
def foldId (s : String) : String := s.toLower

/-- The current value of a named object, case-folded per ARM 2.3. -/
def lookupObj (w : AdaWorld) (name : String) : Option Val :=
  let key := foldId name
  let outer := (w.objects.find? (fun p => p.1 == key)).map Prod.snd
  match w.frames with
  | [] => outer
  | f :: _ => match (f.find? (fun p => p.1 == key)).map Prod.snd with
              | some v => some v
              | none => outer

/-- Replace a named object's value. **Only ever called after `lookupObj`
succeeded** — an assignment to an undeclared name is refused before this,
because inch 2 models no declaration — so this updates in place and never
creates, which is what keeps a refused program from quietly acquiring a
variable. -/
def updateObj (w : AdaWorld) (name : String) (v : Val) : AdaWorld :=
  let key := foldId name
  let hit (l : List (String × Val)) := l.any (fun p => p.1 == key)
  let put (l : List (String × Val)) := l.map (fun p => if p.1 == key then (p.1, v) else p)
  match w.frames with
  | f :: rest => if hit f then { w with frames := put f :: rest }
                 else { w with objects := put w.objects }
  | [] => { w with objects := put w.objects }

/-! ## §4 CITING THE ARM WHEN THE ARM IS NOT ON THE MACHINE -/

/-- A CLAUSE-level citation. `ArmRef.toString` renders it as the bare clause,
so a citation that could not be checked to the paragraph **says so by its
shape**. Inch 1 had the ARM text and cites to the paragraph
(`erroneousExecution` is `1.1.5(9)`); inch 2 does not, and does not guess. -/
def clauseRef (clause : String) : ArmRef := { clause := clause, para := "" }

/-! ## §5 BOUNDED (RUN-TIME) ERRORS ARE MEMBERSHIP SITES — never `⊕`

`docs/backlog.md` §L63 minted the site class and it is now family law. **ARM
5.1 carries a Bounded (Run-Time) Errors category** — measured from
`docs/ada-spec-census.json`, which records the categories present in every
subclause — so inch 2 is the rung where the machinery goes live.

The verdict is `obs (run …) ∈ permitted site`, with equality as the singleton
case, so ordinary sites need no special treatment. **Never `⊕`**: outcome
conjunction carries an `S ≠ ∅` side condition that makes it a REACHABILITY
claim, converting a permission into an obligation — strictly stronger and,
for Ada, false.

**NO ARM 5.1 SITE IS INSTANTIATED HERE, and the absence is gated rather than
hidden.** The permitted set of 5.1's bounded error is a fact about the ARM's
text, and the ARM text is not on this machine. Writing a permitted set from
memory would be the exact failure the citation shape in §4 exists to prevent.
So the machinery is **present and gated**, which is the same discipline the
`RefusalCause` ruling applies to an expected-empty class: a gate needs
something to be about, and a lane that omitted the type would make the
emptiness invisible. The first real site lands with the re-acquire rung.
Scale, for when it does: **57 Bounded (Run-Time) Errors paragraphs in clauses
1-13**, 104 document-wide. -/
structure BoundedSite (α : Type) where
  /-- The ARM paragraph that grants the permission. -/
  site : ArmRef
  /-- Every outcome the standard permits here. A singleton is an ordinary
  determinate site. -/
  permitted : List α
  deriving Repr, Inhabited

/-- The verdict at a bounded-error site: MEMBERSHIP, never equality and never
outcome conjunction. -/
def BoundedSite.admits [BEq α] (s : BoundedSite α) (x : α) : Bool :=
  s.permitted.contains x

/-! ## §6 THE BRIDGE FROM INCH 1's PURE DECISIONS INTO THE MONAD

`constrain` and its family return `Except Abrupt Val` — inch 1 deliberately
kept the one decision that cannot be retrofitted in a pure function. This is
the only place that lifts them, and it lifts them onto **`ρ`**, which is the
adoption's two-channel mapping doing its job at the statement layer: a
`Constraint_Error` is the language's own raise, so the world survives it. -/
def ofAbrupt (r : Except Abrupt Val) : AdaM W Val :=
  match r with
  | .ok v => pure v
  | .error e => raiseIn e

/-- This node's `kind`, for dispatch. Local to the meaning layer rather than
added to `Ast.lean`: the trunk is provably edition-INSENSITIVE and a
dispatcher is not. -/
def kindOf : Node → String
  | .node k _ _ => k
  | .leaf k _ _ => k
  | .absent => "Absent"
  | .unsupported _ _ _ => "Unsupported"

/-! ## §7 SCALAR PROJECTIONS -/

/-- The integer behind a value, universal or typed. -/
def Val.asInt : Val → Option Int
  | .int _ v => some v
  | .univInt v => some v
  | .enum _ _ => none

/-- The Boolean behind a value. `Boolean` IS an enumeration type (ARM 3.5.3),
so this reads a position and does not need a constructor of its own — which
is inch 1's representation decision paying out at its first use. -/
def Val.asBool : Val → Option Bool
  | .enum sub pos => if sub.typeName == "Boolean" then some (pos == 1) else none
  | _ => none

/-- The two operands of a binary arithmetic operation, plus the subtype that
GOVERNS it. `none` for the subtype means both operands were universal, and the
result stays exact and unbounded (ARM 3.5.4).

**Two typed operands of DIFFERENT subtype names refuse**, because inch 2 has
no declarations and therefore no way to tell a different SUBTYPE of one type
from a different TYPE. `typeName` is doing double duty as type identity here,
and resolving that is inch 3's job with `ObjectDecl` in hand. -/
def operands : Val → Val → Option (Option IntSubtype × Int × Int)
  | .univInt x, .univInt y => some (none, x, y)
  | .int s x,   .univInt y => some (some s, x, y)
  | .univInt x, .int s y   => some (some s, x, y)
  | .int s x,   .int t y   => if s.typeName == t.typeName then some (some s, x, y) else none
  | _, _ => none

/-- Ada's binary arithmetic (ARM 4.5.3, 4.5.5), routed through inch 1's
`constrain` so there is exactly ONE site where the constraint decision lives.

The `rfl` examples in the gate below pin that this IS inch 1's `addOp`,
`subOp`, `mulOp` and `divOp` at a known subtype, rather than a second
implementation that happens to agree. -/
def applyArith (sub : Option IntSubtype) (op : String) (x y : Int) :
    Option (Except Abrupt Val) :=
  let wrap : Int → Except Abrupt Val := fun v =>
    match sub with
    | some s => constrain s v
    | none => .ok (.univInt v)
  let divByZero : Except Abrupt Val := .error (.raised constraintError "division by zero")
  match op with
  | "OpPlus"  => some (wrap (x + y))
  | "OpMinus" => some (wrap (x - y))
  | "OpMult"  => some (wrap (x * y))
  | "OpDiv"   => some (if y == 0 then divByZero else wrap (adaDiv x y))
  | "OpRem"   => some (if y == 0 then divByZero else wrap (adaRem x y))
  | _ => none

/-- Ada's relational operators (ARM 4.5.2) on integers. The result is
`Boolean`, which is an enumeration, so it comes back through `Val.ofBool`. -/
def applyRel (op : String) (x y : Int) : Option Val :=
  match op with
  | "OpEq"  => some (Val.ofBool (x == y))
  | "OpNeq" => some (Val.ofBool (x != y))
  | "OpLt"  => some (Val.ofBool (decide (x < y)))
  | "OpLte" => some (Val.ofBool (decide (x ≤ y)))
  | "OpGt"  => some (Val.ofBool (decide (x > y)))
  | "OpGte" => some (Val.ofBool (decide (x ≥ y)))
  | _ => none

/-! ## §8 EXPRESSIONS

The vocabulary is the minimum that makes ARM 5.1-5.3 RUN and nothing more.
Everything else refuses with the clause it would have needed.

**THE EVALUATION ORDER IS UNOBSERVABLE AT THIS VOCABULARY, and that is why
fixing one is sound here.** Ada leaves operand order unspecified, which is
normally an `orderDependence` question — but every expression form below is
side-effect-free, because the one form that could have an effect is a
function call and calls are refused until inch 3. So no program in inch 2's
fragment can observe the order this file happens to evaluate in. **The
question becomes live exactly when calls arrive**, and that is the rung that
owes the `orderDependence` answer rather than this one. -/

/-- An integer literal. Based literals (`16#FF#`, ARM 2.4.2) refuse rather
than being parsed wrong; underscores are separators (ARM 2.4.1) and are
removed. The literal is `universal_integer` — see `Val.univInt`. -/
def intLiteral (t : String) : AdaM W Val :=
  if t.contains '#' then
    refuse (.unsupported (clauseRef "2.4.2")) s!"based literal '{t}' is outside inch 2's vocabulary"
  else
    match (t.replace "_" "").toNat? with
    | some n => pure (Val.univInt (Int.ofNat n))
    | none => refuse (.unsupported (clauseRef "2.4")) s!"integer literal '{t}' did not parse"

/-! ## §8a INCH 3 — the subprogram table, the frame, and what a frame ABSORBS

`docs/backlog/ada.md` §2026-08-24-ada-5 censused this rung: 178 ARM paragraphs
and 16.39% of the corpus, with the weight in the ARGUMENTS rather than in the
call (`AssocList` + `ParamAssoc` = 271,135 nodes against 152,654 call nodes).

**The table is a PARAMETER, not world state**, following the Go tier's
`FuncTable` (`LeanModels/Go/Stmt.lean`): a subprogram body is program text,
and putting text in `W` would make elaboration look like a side effect. -/

/-- A subprogram this tier can call. -/
structure Subp where
  /-- Case-folded, per ARM 2.3. -/
  name : String
  isFunction : Bool
  /-- Formal parameter names, case-folded, in POSITIONAL order. -/
  params : List String
  /-- Every mode is `in` (`ModeDefault`/`ModeIn`). **`out` and `in out` are
  outside inch 3's slice** and the call refuses citing ARM 6.2 — which is also
  the subclause carrying a Bounded (Run-Time) Errors category, so it is the
  right place for the next rung to start. -/
  modesOk : Bool
  body : List Node
  /-- **Inch 4.** The exception handlers, ARM 11.2 — read from
  `HandledStmts`' SECOND slot, which is a generic `AdaNodeList` and **not** an
  `ExceptionHandlerList`: that kind occurs **zero times in 2,976,861 corpus
  nodes** (`docs/backlog/ada.md` §2026-08-24-ada-7). Inch 3 read slot[0] and
  ignored this one. -/
  handlers : List Node
  deriving Repr, Inhabited

abbrev SubpTable := List (String × Subp)

/-- ARM 11.2: does this handler's choice list cover an occurrence of `exc`?

`others` is an `OthersDesignator` LEAF and is the shape both fixture handlers
use. A named choice is matched case-INSENSITIVELY, per ARM 2.3 — an exception
name is an identifier like any other. -/
def handlerCovers (exc : String) : Node → Bool
  | .node "ExceptionHandler" _ ch =>
      if ch.size != 3 then false else
      match ch[1]! with
      | .node "AlternativesList" _ alts =>
          alts.any fun a =>
            match a with
            | .leaf "OthersDesignator" _ _ => true
            | .leaf "Identifier" _ nm => foldId nm == foldId exc
            | _ => false
      | _ => false
  | _ => false

/-- The statements a handler runs. `ExceptionHandler` is 3 children, measured. -/
def handlerBody : Node → List Node
  | .node "ExceptionHandler" _ ch =>
      if ch.size == 3 then
        match ch[2]! with
        | .node "StmtList" _ ss => ss.toList
        | other => [other]
      else []
  | _ => []

/-- Does this subtree contain a call? **Out of fuel answers `true`**, because
the only consumer refuses on `true` and a refusal is the safe direction — a
budget-exhausted "no" would silently license the very order-dependence this
predicate exists to catch. -/
def containsCall : Nat → Node → Bool
  | 0, _ => true
  | fuel + 1, n =>
    match n with
    | .node "CallExpr" _ _ => true
    | .node _ _ ch => ch.any (containsCall fuel)
    | _ => false

/-- The identifier under a `DefiningName` (ARM 6.1). -/
def definingName : Node → Option String
  | .node "DefiningName" _ ch =>
      if ch.size == 1 then
        match ch[0]! with
        | .leaf "Identifier" _ t => some t
        | _ => none
      else none
  | .leaf "Identifier" _ t => some t
  | _ => none

/-- One `ParamSpec`: its names and whether its mode is in the slice.
Arity 6, measured (35 of 35); the mode is child 2. -/
def paramSpec : Node → Option (List String × Bool) 
  | .node "ParamSpec" _ ch =>
      if ch.size != 6 then none else
      let ok := kindOf ch[2]! == "ModeDefault" || kindOf ch[2]! == "ModeIn"
      match ch[0]! with
      | .node "DefiningNameList" _ ns =>
          let named := ns.toList.filterMap definingName
          if named.length == ns.size then some (named.map foldId, ok) else none
      | _ => none
  | _ => none

/-- A `SubpSpec`'s parameter list. An ABSENT list is a parameterless
subprogram, which is ordinary and not a failure. -/
def paramsOf : Node → List String × Bool
  | .node "ParamSpecList" _ ps =>
      ps.foldl (fun acc s =>
        match paramSpec s with
        | some (ns, ok) => (acc.1 ++ ns, acc.2 && ok)
        | none => (acc.1, false)) (([], true) : List String × Bool)
  | .absent => ([], true)
  | _ => ([], false)

/-- A `SubpBody` read into a `Subp`. Arities measured off the fixtures:
`SubpBody` 6 of 6, `SubpSpec` 4 of 4, `HandledStmts` 2 of 2. -/
def subpOf : Node → Option Subp
  | .node "SubpBody" _ ch =>
      if ch.size != 6 then none else
      match ch[1]!, ch[4]! with
      | .node "SubpSpec" _ sp, .node "HandledStmts" _ hs =>
          if sp.size != 4 || hs.size < 1 then none else
          match definingName sp[1]! with
          | none => none
          | some nm =>
            let (ps, ok) := paramsOf sp[2]!
            some { name := foldId nm,
                   isFunction := kindOf sp[0]! == "SubpKindFunction",
                   params := ps, modesOk := ok,
                   body := match hs[0]! with
                           | .node "StmtList" _ ss => ss.toList
                           | other => [other],
                   -- An EMPTY handler list is a LEAF with empty text (41 of
                   -- 65 `AdaNodeList` nodes in the fixtures), so a non-node
                   -- here means "no handlers" and never "malformed".
                   handlers := match hs[1]! with
                               | .node "AdaNodeList" _ hs2 => hs2.toList
                               | _ => [] }
      | _, _ => none
  | _ => none

/-- Every `SubpBody` in a declaration tree, as a table. Explicitly recursive
on a LIST at a decreasing fuel rather than folding, so the recursion stays
structural and the table stays kernel-reducible. -/
def collectSubps : Nat → List Node → SubpTable
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, n :: rest =>
      let here := match subpOf n with
                  | some s => [(s.name, s)]
                  | none => []
      let inner := match n with
                   | .node _ _ ch => collectSubps fuel ch.toList
                   | _ => []
      here ++ inner ++ collectSubps fuel rest

/-! ## §9 ARM 5.2 — THE ASSIGNMENT'S SUBTYPE CHECK

This is where inch 1's one irreversible decision fires through a statement
rule. ARM 5.2's dynamic semantics converts the value to the TARGET's subtype
and checks the constraint; out of range **raises `Constraint_Error`**, which
travels on `ρ` and leaves the world intact for a handler. -/

/-- Convert a value to the target's subtype, per ARM 5.2. -/
def convertTo (target v : Val) : AdaM W Val :=
  match target, v with
  | .int sub _, .univInt n => ofAbrupt (constrain sub n)
  | .int sub _, .int sub' n =>
      if sub.typeName == sub'.typeName then ofAbrupt (constrain sub n)
      else refuse (.unsupported (clauseRef "4.6"))
        s!"assigning a '{sub'.typeName}' into a '{sub.typeName}' needs the type resolution inch 2 does not have"
  | .enum sub _, .enum sub' p =>
      if sub.typeName == sub'.typeName then ofAbrupt (constrainEnum sub p)
      else refuse (.unsupported (clauseRef "4.6"))
        s!"assigning a '{sub'.typeName}' into a '{sub.typeName}' needs the type resolution inch 2 does not have"
  | _, _ =>
      refuse (.unsupported (clauseRef "5.2")) "assignment between these value shapes is outside inch 2's vocabulary"

/-! ## §10 THE STATEMENT TIER — ARM 5.1, 5.2, 5.3 -/

/-! ## §10 THE WALKER — ARM 5.1-5.3 and 6.1/6.3/6.4/6.4.1/6.5

ONE `mutual` block, every function structurally recursive on `fuel` and
carrying the subprogram table as a leading parameter. That is the Go tier's
shape (`LeanModels/Go/Stmt.lean`: `mutual` over `evalExpr`/`evalArgs`/
`evalCallValues`/`execStmt`, fuel-indexed, `FuncTable` as a parameter) and it
is followed rather than reinvented — **with `termination_by` deliberately
absent**, because it would force well-founded recursion and take the gate's
kernel reduction away. The C tier's `Expr.lean` measures on AST size instead;
this tier cannot, for that reason. -/

mutual

/-- Evaluate an expression. -/
def evalExpr (prog : SubpTable) : Nat → Node → AdaM AdaWorld Val
  | 0, _ => exhausted
  | fuel + 1, n =>
    match n with
    | .leaf k _ t =>
      match k with
      | "IntLiteral" => intLiteral t
      | "Identifier" => do
        let w ← get
        match lookupObj w t with
        | some v => pure v
        | none =>
          refuse (.unsupported (clauseRef "3.3"))
            s!"'{t}' is not in the store — inch 2 models no object declaration"
      | _ =>
        refuse (.unsupported (clauseRef "4.4"))
          s!"expression leaf '{k}' is outside this tier's vocabulary"
    | .node k _ ch =>
      match k with
      | "ParenExpr" =>
        if ch.size == 1 then evalExpr prog fuel ch[0]!
        else refuse (.unsupported (clauseRef "4.4")) "ParenExpr: unexpected arity"
      | "UnOp" =>
        if ch.size != 2 then refuse (.unsupported (clauseRef "4.5")) "UnOp: unexpected arity"
        else do
          let v ← evalExpr prog fuel ch[1]!
          match kindOf ch[0]! with
          | "OpNot" =>
            match v.asBool with
            | some b => pure (Val.ofBool (!b))
            | none => refuse (.unsupported (clauseRef "4.5.6")) "'not' applied to a non-Boolean"
          | "OpMinus" =>
            match v with
            | .int s x => ofAbrupt (constrain s (-x))
            | .univInt x => pure (Val.univInt (-x))
            | .enum _ _ => refuse (.unsupported (clauseRef "4.5.4")) "unary '-' on an enumeration"
          | u =>
            refuse (.unsupported (clauseRef "4.5"))
              s!"unary operator '{u}' is outside this tier's vocabulary"
      | "BinOp" =>
        if ch.size != 3 then refuse (.unsupported (clauseRef "4.5")) "BinOp: unexpected arity"
        else do
          let l ← evalExpr prog fuel ch[0]!
          let r ← evalExpr prog fuel ch[2]!
          let op := kindOf ch[1]!
          match operands l r with
          | none =>
            refuse (.unsupported (clauseRef "4.5"))
              s!"operator '{op}' on these operand types is outside this tier's vocabulary"
          | some (sub, x, y) =>
            match applyArith sub op x y with
            | some res => ofAbrupt res
            | none =>
              refuse (.unsupported (clauseRef "4.5"))
                s!"binary operator '{op}' is outside this tier's vocabulary"
      | "RelationOp" =>
        if ch.size != 3 then refuse (.unsupported (clauseRef "4.5.2")) "RelationOp: unexpected arity"
        else do
          let l ← evalExpr prog fuel ch[0]!
          let r ← evalExpr prog fuel ch[2]!
          let op := kindOf ch[1]!
          match l.asInt, r.asInt with
          | some x, some y =>
            match applyRel op x y with
            | some v => pure v
            | none =>
              refuse (.unsupported (clauseRef "4.5.2"))
                s!"relational operator '{op}' is outside this tier's vocabulary"
          | _, _ =>
            refuse (.unsupported (clauseRef "4.5.2"))
              s!"relational operator '{op}' on non-integer operands is outside this tier's vocabulary"
      -- ARM 6.4: a FUNCTION call in expression position.
      | "CallExpr" => do
        let r ← callExpr prog fuel n
        match r with
        | some v => pure v
        | none =>
          refuse (.unsupported (clauseRef "6.5"))
            "a function call completed without returning a value"
      | _ =>
        refuse (.unsupported (clauseRef "4.4"))
          s!"expression node '{k}' is outside this tier's vocabulary"
    | .absent =>
      refuse (.unsupported (clauseRef "4.4")) "an ABSENT node is not an expression"
    | .unsupported cls _ _ =>
      refuse (.unsupported (clauseRef "4.4"))
        s!"frontend node class '{cls}' is outside the pinned vocabulary"

/-- ARM 6.4, *Subprogram Calls*. Measured shapes: `CallExpr` is 2 children
(124 of 124) — a name and a suffix — and `CallStmt` wraps one (32 of 32).

**THE SUFFIX IS NOT ALWAYS AN ARGUMENT LIST.** 20 of 124 are `BinOp`, which is
a range or a slice (`A (1 .. 10)`), and 35 of 160 `AssocList` nodes are LEAVES
carrying empty text — a parameterless call. Both are refused or handled
explicitly rather than falling through a pattern that assumed a node. -/
def callExpr (prog : SubpTable) : Nat → Node → AdaM AdaWorld (Option Val)
  | 0, _ => exhausted
  | fuel + 1, n =>
    match n with
    | .node "CallExpr" _ ch =>
      if ch.size != 2 then refuse (.unsupported (clauseRef "6.4")) "CallExpr: unexpected arity"
      else
        match ch[0]! with
        | .leaf "Identifier" _ nm =>
          match prog.find? (fun e => e.1 == foldId nm) with
          | none =>
            refuse (.unsupported (clauseRef "6.4"))
              s!"'{nm}' is not a subprogram this tier has elaborated"
          | some (_, s) =>
            match ch[1]! with
            -- THE TRAP, HANDLED: an empty argument list is a LEAF, not a node
            -- with no children — 35 of 160, and `P;` is the commonest call.
            | .leaf "AssocList" _ _ => callSubp prog fuel s []
            | .node "AssocList" _ assoc =>
              -- ARM 6.4.1 LEAVES THE ORDER UNSPECIFIED, and a call can have an
              -- effect. This is the first site in the tier where the order is
              -- OBSERVABLE, exactly as inch 2 predicted it would be.
              if assoc.size ≥ 2 && assoc.any (containsCall fuel) then
                refuse (.orderDependence (clauseRef "6.4.1"))
                  s!"'{nm}' is called with {assoc.size} arguments and at least one contains a call: ARM 6.4.1 leaves the evaluation order unspecified, so the observable outcome is not determined by this model"
              else do
                let args ← evalArgs prog fuel assoc.toList
                callSubp prog fuel s args
            | sfx =>
              refuse (.unsupported (clauseRef "4.1.2"))
                s!"a '{kindOf sfx}' suffix is an index or a slice, not an argument list"
        | callee =>
          refuse (.unsupported (clauseRef "6.4"))
            s!"callee '{kindOf callee}' is not a simple name — inch 3 has no name resolution"
    | other =>
      refuse (.unsupported (clauseRef "6.4")) s!"'{kindOf other}' is not a call"

/-- ARM 6.4.1, *Parameter Associations* — 51 paragraphs, the biggest subclause
in the rung. `ParamAssoc` is 2 children (139 of 139) and a **`null` designator
is a POSITIONAL association**, which is the shape the corpus is made of. -/
def evalArgs (prog : SubpTable) : Nat → List Node → AdaM AdaWorld (List Val)
  | 0, _ => exhausted
  | _ + 1, [] => pure []
  | fuel + 1, a :: rest =>
    match a with
    | .node "ParamAssoc" _ pc =>
      if pc.size != 2 then refuse (.unsupported (clauseRef "6.4.1")) "ParamAssoc: unexpected arity"
      else
        match pc[0]! with
        | .absent => do
          let v ← evalExpr prog fuel pc[1]!
          let vs ← evalArgs prog fuel rest
          pure (v :: vs)
        | d =>
          refuse (.unsupported (clauseRef "6.4.1"))
            s!"a NAMED association (designator '{kindOf d}') is outside inch 3's slice"
    | other =>
      refuse (.unsupported (clauseRef "6.4.1"))
        s!"'{kindOf other}' is not a parameter association"

/-- Enter the frame, run the body, and come back with whatever `return`
delivered. ARM 6.3, 6.5. -/
def callSubp (prog : SubpTable) : Nat → Subp → List Val → AdaM AdaWorld (Option Val)
  | 0, _, _ => exhausted
  | fuel + 1, s, args =>
    if !s.modesOk then
      refuse (.unsupported (clauseRef "6.2"))
        s!"'{s.name}' has a parameter mode outside inch 3's slice — only `in` is modelled"
    else if s.params.length != args.length then
      refuse (.unsupported (clauseRef "6.4.1"))
        s!"'{s.name}' takes {s.params.length} parameters and was given {args.length} arguments — inch 3 models no default expression"
    else fun w =>
      -- **WHAT A FRAME ABSORBS**, and the arms are the laws:
      --   `.ret`      CAUGHT -- that is what a frame is for (ARM 6.5).
      --   `.raised`   caught IFF a handler covers it (ARM 11.2); otherwise it
      --               PROPAGATES (ARM 11.4). Either way the frame is popped:
      --               an exception leaving a subprogram still leaves it.
      --   a refusal   does not come back at all -- there is no world on pi,
      --               and an arm that restored one would be inventing it.
      -- The handler runs on `w'`, the world AS OF THE RAISE and with the frame
      -- still pushed, because ARM 11.4 hands the handler the state the raise
      -- happened in -- not the state the call started in.
      let entered := { w with frames := (s.params.zip args) :: w.frames }
      let pop := fun (x : AdaWorld) => { x with frames := w.frames }
      match execStmts prog fuel s.body entered with
      | .error h => .error h
      | .ok (.ok _, w') => .ok (.ok none, pop w')
      | .ok (.error (.ret v), w') => .ok (.ok v, pop w')
      | .ok (.error (.raised n m), w') =>
        match s.handlers.find? (handlerCovers n) with
        | none => .ok (.error (.raised n m), pop w')
        | some hd =>
          match execStmts prog fuel (handlerBody hd) w' with
          | .error h2 => .error h2
          | .ok (.ok _, w2) => .ok (.ok none, pop w2)
          | .ok (.error (.ret v), w2) => .ok (.ok v, pop w2)
          -- A raise INSIDE a handler propagates; it is not re-handled here
          -- (ARM 11.4: a handler is not its own handler).
          | .ok (.error e2, w2) => .ok (.error e2, pop w2)
      | .ok (.error e, w') => .ok (.error e, pop w')

/-- Execute a sequence of statements (ARM 5.1).

ONE function over a LIST, and `elsif` is handled by **lowering** — ARM 5.3's
`elsif` is a nested `if`, so the rule rebuilds it as one. -/
def execStmts (prog : SubpTable) : Nat → List Node → AdaM AdaWorld Unit
  | 0, _ => exhausted
  | _ + 1, [] => pure ()
  | fuel + 1, s :: rest =>
    match s with
    | .leaf k _ _ =>
      match k with
      | "NullStmt" => execStmts prog fuel rest
      -- A childless `raise;` reaches us as a LEAF, per the same encoding rule.
      | "RaiseStmt" =>
        refuse (.unsupported (clauseRef "11.3"))
          "a bare `raise` re-raises the current occurrence, which needs an occurrence in W — outside inch 4's slice"
      | _ =>
        refuse (.unsupported (clauseRef "5.1"))
          s!"statement leaf '{k}' is outside this tier's vocabulary"
    | .node k esp ch =>
      match k with
      | "StmtList" => execStmts prog fuel (ch.toList ++ rest)
      | "NullStmt" => execStmts prog fuel rest
      -- ARM 6.4: a PROCEDURE call statement. `CallStmt` wraps one `CallExpr`,
      -- 32 of 32, and its value (if any) is discarded.
      | "CallStmt" =>
        if ch.size != 1 then refuse (.unsupported (clauseRef "6.4")) "CallStmt: unexpected arity"
        else do
          let _ ← callExpr prog fuel ch[0]!
          execStmts prog fuel rest
      -- ARM 6.5: `return`. A RAISE on rho, which the call frame absorbs -- so
      -- the frame is what makes a return local, and no new machinery is
      -- needed because inch 1 put `.ret` in `Abrupt` already.
      | "ReturnStmt" =>
        if ch.size != 1 then refuse (.unsupported (clauseRef "6.5")) "ReturnStmt: unexpected arity"
        else
          match ch[0]! with
          | .absent => raiseIn (.ret none)
          | e => do
            let v ← evalExpr prog fuel e
            raiseIn (.ret (some v))
      -- ARM 11.3, *Raise Statements*. **NO CORPUS WITNESS**: `RaiseStmt` is
      -- 1,440 nodes corpus-wide and **0 in both fixtures**, so its ARITY is
      -- unverified here. The rule is deliberately written not to depend on
      -- it — child 0 is the exception name whatever else follows — because a
      -- guessed arity is exactly what the three list-encoding traps punished.
      | "RaiseStmt" =>
        if ch.size == 0 then
          refuse (.unsupported (clauseRef "11.3"))
            "a bare `raise` re-raises the current occurrence, which needs an occurrence in W — outside inch 4's slice"
        else
          match ch[0]! with
          | .leaf "Identifier" _ nm => raiseIn (.raised nm "")
          | .absent =>
            refuse (.unsupported (clauseRef "11.3"))
              "a bare `raise` re-raises the current occurrence, which needs an occurrence in W — outside inch 4's slice"
          | other =>
            refuse (.unsupported (clauseRef "11.3"))
              s!"raising a '{kindOf other}' is outside inch 4's slice"
      | "AssignStmt" =>
        if ch.size != 2 then refuse (.unsupported (clauseRef "5.2")) "AssignStmt: unexpected arity"
        else
          match ch[0]! with
          | .leaf "Identifier" _ name => do
            let v ← evalExpr prog fuel ch[1]!
            let w ← get
            match lookupObj w name with
            | none =>
              refuse (.unsupported (clauseRef "3.3"))
                s!"'{name}' is not in the store — inch 2 models no object declaration"
            | some cur => do
              let v' ← convertTo cur v
              modify (fun w' => updateObj w' name v')
              execStmts prog fuel rest
          | target =>
            refuse (.unsupported (clauseRef "5.2"))
              s!"assignment target '{kindOf target}' is not a simple name — the target-shape census says 83.7% are, and the rest need composite VALUES"
      | "IfStmt" =>
        if ch.size != 4 then refuse (.unsupported (clauseRef "5.3")) "IfStmt: unexpected arity"
        else do
          let c ← evalExpr prog fuel ch[0]!
          match c.asBool with
          | none =>
            refuse (.unsupported (clauseRef "5.3"))
              "an if condition that is not Boolean is outside this tier's vocabulary"
          | some true => execStmts prog fuel (ch[1]! :: rest)
          | some false =>
            let elsifs :=
              match ch[2]! with
              | .node "ElsifStmtPartList" _ es => es.toList
              | _ => ([] : List Node)
            match elsifs with
            | [] =>
              match ch[3]! with
              | .node "ElsePart" _ ep => execStmts prog fuel (ep.toList ++ rest)
              | _ => execStmts prog fuel rest
            | e :: es =>
              match e with
              | .node "ElsifStmtPart" _ ec =>
                if ec.size != 2 then refuse (.unsupported (clauseRef "5.3")) "ElsifStmtPart: unexpected arity"
                else
                  execStmts prog fuel
                    (Node.node "IfStmt" esp
                      #[ec[0]!, ec[1]!, Node.node "ElsifStmtPartList" esp es.toArray, ch[3]!] :: rest)
              | bad =>
                refuse (.unsupported (clauseRef "5.3"))
                  s!"elsif part '{kindOf bad}' is outside this tier's vocabulary"
      | _ =>
        refuse (.unsupported (clauseRef "5.1"))
          s!"statement node '{k}' is outside this tier's vocabulary"
    | other =>
      refuse (.unsupported (clauseRef "5.1"))
        s!"statement node '{kindOf other}' is outside this tier's vocabulary"

end

/-! ## §11 THE GATE

Non-vacuous by the C lane's test: flip a claim and Lean reports the failing
expression. Every fixture below is built to the shapes MEASURED off
`report.json` and `b371001.json` — including the empty-elsif-list-as-a-leaf
encoding, which is the one a walker gets wrong by reading the grammar instead
of the corpus. -/

private def sp0 : AdaSpan := { line := 1, col := 1, endLine := 1, endCol := 1 }
private def ident (n : String) : Node := .leaf "Identifier" sp0 n
private def lit (n : String) : Node := .leaf "IntLiteral" sp0 n
private def opLeaf (k : String) : Node := .leaf k sp0 k
private def bin (op : String) (l r : Node) : Node := .node "BinOp" sp0 #[l, opLeaf op, r]
private def rel (op : String) (l r : Node) : Node := .node "RelationOp" sp0 #[l, opLeaf op, r]
private def assign (t e : Node) : Node := .node "AssignStmt" sp0 #[t, e]
private def seq (ss : List Node) : Node := .node "StmtList" sp0 ss.toArray
private def elsifPart (c t : Node) : Node := .node "ElsifStmtPart" sp0 #[c, t]
private def elsePart (t : Node) : Node := .node "ElsePart" sp0 #[t]

/-- An `if` built the way the extractor builds one: an EMPTY elsif list is a
LEAF with empty text, which is 30 of the 31 in the fixtures. -/
private def ifStmt (c t : Node) (elsifs : List Node := []) (els : Node := .absent) : Node :=
  .node "IfStmt" sp0
    #[c, t,
      (if elsifs.isEmpty then .leaf "ElsifStmtPartList" sp0 "" else .node "ElsifStmtPartList" sp0 elsifs.toArray),
      els]

private def int8 : IntSubtype := { typeName := "Int8", lo := -128, hi := 127 }
private def row0 : TraceRow := { kind := "CSTART", span := sp0, detail := "fixture" }

/-- The store's keys are folded; the fixtures below refer to `X` and `Y` in
upper case, so every guard also exercises ARM 2.3's case insensitivity. -/
private def w0 : AdaWorld :=
  { objects := [("x", .int int8 0), ("y", .int int8 10), ("b", Val.ofBool false)],
    trace := [row0] }

private def endsWith (name : String) (v : Val) (ss : List Node)
    (prog : SubpTable := []) : Bool :=
  match execStmts prog 64 ss w0 with
  | .ok (.ok _, w') => match lookupObj w' name with
                       | some u => u == v
                       | none => false
  | _ => false

private def raisesKeeping (exc : String) (name : String) (v : Val) (ss : List Node)
    (prog : SubpTable := []) : Bool :=
  match execStmts prog 64 ss w0 with
  | .ok (.error (.raised n _), w') =>
      n == exc && (match lookupObj w' name with
                   | some u => u == v
                   | none => false) && w'.trace == [row0]
  | _ => false

private def refusedAtClause (clause : String) (ss : List Node)
    (prog : SubpTable := []) : Bool :=
  match execStmts prog 64 ss w0 with
  | .error (.unsupported c _ _) => c.className == "unsupported" && c.detail.clause == clause
  | _ => false

private def timedOut (fuel : Nat) (ss : List Node) (prog : SubpTable := []) : Bool :=
  match execStmts prog fuel ss w0 with
  | .error .timeout => true
  | _ => false

-- ARM 5.2. `X := 5` stores 5 -- and the target is written `X` while the store
-- holds `x`, so ARM 2.3's case folding is under every guard here.
#guard endsWith "x" (.int int8 5) [assign (ident "X") (lit "5")]

-- ...and the value takes the TARGET's subtype, not the literal's: what goes
-- in is a universal_integer and what comes out is an Int8.
#guard endsWith "x" (.int int8 5) [assign (ident "x") (lit "5")]

-- ARM 5.1: a sequence runs in order, and the second statement reads what the
-- first wrote.
#guard endsWith "x" (.int int8 3) [assign (ident "X") (lit "1"), assign (ident "X") (bin "OpPlus" (ident "X") (lit "2"))]

-- A StmtList is spliced, so nesting one changes nothing.
#guard endsWith "x" (.int int8 3) [seq [assign (ident "X") (lit "1")], assign (ident "X") (bin "OpPlus" (ident "X") (lit "2"))]

-- ARM 5.1: a null_statement is a LEAF and is skipped.
#guard endsWith "x" (.int int8 5) [.leaf "NullStmt" sp0 "null;", assign (ident "X") (lit "5")]

-- THE INCH-1 DECISION, NOW FIRING THROUGH A STATEMENT RULE. 200 is outside
-- Int8, so ARM 5.2's check RAISES Constraint_Error -- it does not wrap and it
-- does not refuse. And because a raise travels on rho, THE WORLD SURVIVES:
-- `x` still holds its old value and the trace still holds its row.
#guard raisesKeeping constraintError "x" (.int int8 0) [assign (ident "X") (lit "200")]

-- The same through arithmetic (ARM 4.5.3): 100 + 28 overflows Int8.
#guard raisesKeeping constraintError "x" (.int int8 0)
         [assign (ident "X") (bin "OpPlus" (lit "100") (lit "28"))]

-- ARM 5.3: the THEN branch.
#guard endsWith "x" (.int int8 1)
         [ifStmt (rel "OpLt" (ident "X") (ident "Y")) (seq [assign (ident "X") (lit "1")])
            [] (elsePart (seq [assign (ident "X") (lit "2")]))]

-- ...and the ELSE branch.
#guard endsWith "x" (.int int8 2)
         [ifStmt (rel "OpLt" (ident "Y") (ident "X")) (seq [assign (ident "X") (lit "1")])
            [] (elsePart (seq [assign (ident "X") (lit "2")]))]

-- ...and an ABSENT else is a no-op rather than an error. Measured: 22 of the
-- 31 IfStmt nodes in the fixtures carry `null` in that slot.
#guard endsWith "x" (.int int8 0) [ifStmt (rel "OpLt" (ident "Y") (ident "X")) (seq [assign (ident "X") (lit "1")])]

-- ...and the ELSIF chain, which is LOWERED into a nested if. The first
-- condition is false, the elsif's is true, so the else must not run.
#guard endsWith "x" (.int int8 7)
         [ifStmt (rel "OpLt" (ident "Y") (ident "X")) (seq [assign (ident "X") (lit "1")])
            [elsifPart (rel "OpLt" (ident "X") (ident "Y")) (seq [assign (ident "X") (lit "7")])]
            (elsePart (seq [assign (ident "X") (lit "2")]))]

-- ...and when NO elsif matches, the else still runs -- the lowering must not
-- lose the else part as it rebuilds.
#guard endsWith "x" (.int int8 2)
         [ifStmt (rel "OpLt" (ident "Y") (ident "X")) (seq [assign (ident "X") (lit "1")])
            [elsifPart (rel "OpGt" (ident "X") (ident "Y")) (seq [assign (ident "X") (lit "7")])]
            (elsePart (seq [assign (ident "X") (lit "2")]))]

-- A Boolean object is a condition on its own -- no relational operator. This
-- is the shape `report.json`'s own most common if-condition takes.
#guard endsWith "x" (.int int8 4)
         [ifStmt (.node "UnOp" sp0 #[opLeaf "OpNot", ident "B"]) (seq [assign (ident "X") (lit "4")])]

-- THE REFUSALS, each citing the clause it would have needed.
-- ARM 5.2: a non-simple-name target. This is the pending measurement carried
-- in the model: the target-shape census has not run.
#guard refusedAtClause "5.2" [assign (.node "DottedName" sp0 #[ident "R", ident "F"]) (lit "1")]

-- ARM 5.1: a statement kind outside the tier's vocabulary. This guard USED to
-- name `CallStmt` -- "56,062 nodes, 2.7x the assignments, and it is inch 3's"
-- -- and inch 3 made it FAIL, which is the gate earning its keep: a guard that
-- pins a REFUSAL must go red the moment the frontier moves past it, or the
-- tier would keep claiming not to model something it models. The witness moves
-- to a kind that is still genuinely out of tier: `CaseStmt` is ARM 5.4 and
-- inch 7's, at 715 nodes.
#guard refusedAtClause "5.1" [.node "CaseStmt" sp0 #[ident "P"]]

-- ...and `CallStmt` now refuses ONE step further in, at ARM 6.4, when its
-- child is not a call at all. The arm stays non-vacuous; only its clause moved.
#guard refusedAtClause "6.4" [.node "CallStmt" sp0 #[ident "P"]]

-- ARM 2.4.2: a based literal is refused rather than parsed wrong.
#guard refusedAtClause "2.4.2" [assign (ident "X") (lit "16#FF#")]

-- ARM 3.3: inch 2 models no declaration, so an unknown name is out of tier
-- rather than a raise -- it is the MODEL that is missing something.
#guard refusedAtClause "3.3" [assign (ident "Zork") (lit "1")]

-- ARM 4.5: an operator outside the rung. Concatenation is the corpus's most
-- frequent operator at 22,180 and it is not an integer operation.
#guard refusedAtClause "4.5" [assign (ident "X") (bin "OpConcat" (ident "X") (ident "Y"))]

-- FUEL IS AN INDEX, and exhaustion is TIMEOUT -- loud, and never a claim
-- about the program.
#guard timedOut 0 [assign (ident "X") (lit "5")]

-- ...and it is not vacuous: the same statements complete with enough fuel.
#guard !timedOut 64 [assign (ident "X") (lit "5")]

-- Underscores are separators (ARM 2.4.1), not part of the value. 100 fits
-- Int8; 1_00 must be the same number and not a parse artefact.
#guard endsWith "x" (.int int8 100) [assign (ident "X") (lit "1_00")]

-- THE ARITHMETIC IS INCH 1's, not a second implementation that agrees. These
-- are `rfl`, so the kernel checks the identity rather than a sample of it.
example : applyArith (some int8) "OpPlus" 100 27 = some (addOp int8 100 27) := rfl
example : applyArith (some int8) "OpMinus" (-100) 28 = some (subOp int8 (-100) 28) := rfl
example : applyArith (some int8) "OpMult" 100 2 = some (mulOp int8 100 2) := rfl
example : applyArith (some int8) "OpDiv" 1 0 = some (divOp int8 1 0) := rfl
example : applyArith (some int8) "OpDiv" (-7) 2 = some (divOp int8 (-7) 2) := rfl

-- THE BOUNDED-SITE MACHINERY: membership, with the singleton case being
-- ordinary equality. No ARM 5.1 site is instantiated -- the permitted set is
-- a fact about a text this machine does not have -- so this is the type being
-- present and gated, exactly as the expected-empty refusal class is.
private def determinate : BoundedSite Int := { site := clauseRef "5.1", permitted := [7] }
private def twoWay : BoundedSite Int := { site := clauseRef "5.1", permitted := [7, 9] }
#guard determinate.admits 7
#guard !determinate.admits 9
#guard twoWay.admits 7
#guard twoWay.admits 9
#guard !twoWay.admits 8

-- A clause-level citation renders as the bare clause, so a reader can see
-- which citations were checked to the paragraph and which were not.
#guard (clauseRef "5.2").toString == "5.2"
#guard (clauseRef "5.2") == ({ clause := "5.2", para := "" } : ArmRef)

/-! ### INCH 3 — calls, the frame, and `return`

`Subp` is written directly rather than through a `SubpBody` fixture, so the
call rules are tested apart from the table BUILDER — which gets its own
fixture below. That separation is the reason a red here would say which of the
two is wrong. -/

private def callOf (nm : String) (args : List Node) : Node :=
  .node "CallExpr" sp0
    #[ident nm,
      (if args.isEmpty then .leaf "AssocList" sp0 ""
       else .node "AssocList" sp0 (args.map (fun a => Node.node "ParamAssoc" sp0 #[.absent, a])).toArray)]
private def callStmt (nm : String) (args : List Node) : Node := .node "CallStmt" sp0 #[callOf nm args]
private def retStmt (e : Node) : Node := .node "ReturnStmt" sp0 #[e]

/-- `procedure Bump is begin X := X + 1; end;` — no parameters, so its
argument list is a LEAF. -/
private def bump : Subp :=
  { name := "bump", isFunction := false, params := [], modesOk := true,
    body := [assign (ident "X") (bin "OpPlus" (ident "X") (lit "1"))], handlers := [] }

/-- `procedure SetX (N : Integer) is begin X := N; end;` -/
private def setX : Subp :=
  { name := "setx", isFunction := false, params := ["n"], modesOk := true,
    body := [assign (ident "X") (ident "N")], handlers := [] }

/-- `function Twice (N : Integer) return Integer is begin return N + N; end;` -/
private def twice : Subp :=
  { name := "twice", isFunction := true, params := ["n"], modesOk := true,
    body := [retStmt (bin "OpPlus" (ident "N") (ident "N"))], handlers := [] }

/-- The same, but its parameter has a mode outside the slice. -/
private def outMode : Subp := { setX with name := "outmode", modesOk := false }

/-- A procedure that raises rather than returning — ARM 11.4's case. -/
private def blowUp : Subp :=
  { name := "blowup", isFunction := false, params := ["n"], modesOk := true,
    body := [assign (ident "X") (lit "200")], handlers := [] }

private def prog0 : SubpTable :=
  [("bump", bump), ("setx", setX), ("twice", twice), ("outmode", outMode), ("blowup", blowUp)]

private def refusedAs (cls clause : String) (ss : List Node) (prog : SubpTable := []) : Bool :=
  match execStmts prog 64 ss w0 with
  | .error (.unsupported c _ _) => c.className == cls && c.detail.clause == clause
  | _ => false

/-- Did a frame LEAK? After the call the store must be exactly what it was
apart from the intended write, and `frames` must be back to empty. -/
private def framesEmptyAfter (ss : List Node) (prog : SubpTable) : Bool :=
  match execStmts prog 64 ss w0 with
  | .ok (.ok _, w') => w'.frames == []
  | .ok (.error _, w') => w'.frames == []
  | _ => false

-- ARM 6.4: a parameterless procedure call runs its body. The argument list is
-- a LEAF here -- the encoding that would make a naive walker refuse `P;`.
#guard endsWith "x" (.int int8 1) [callStmt "Bump" []] prog0

-- ...and it is called by a name in the OTHER case, per ARM 2.3.
#guard endsWith "x" (.int int8 2) [callStmt "BUMP" [], callStmt "bump" []] prog0

-- ARM 6.4.1: a positional argument binds to the formal, and the body reads it
-- through the FRAME rather than through the outer store.
#guard endsWith "x" (.int int8 9) [callStmt "SetX" [lit "9"]] prog0

-- ARM 6.5: a FUNCTION call returns a value, and `return` is a raise the frame
-- absorbed -- it did not escape to the caller.
#guard endsWith "x" (.int int8 14) [assign (ident "X") (callOf "Twice" [lit "7"])] prog0

-- THE FRAME IS POPPED. `N` is the callee's formal; after the call it must not
-- be visible, and the frame stack must be empty again.
#guard framesEmptyAfter [callStmt "SetX" [lit "9"]] prog0
#guard refusedAtClause "3.3" [callStmt "SetX" [lit "9"], assign (ident "X") (ident "N")] prog0

-- ...AND IT IS POPPED WHEN AN EXCEPTION LEAVES THE CALL, not only on success.
-- ARM 11.4: an exception leaving a subprogram still leaves it.
#guard raisesKeeping constraintError "x" (.int int8 0) [callStmt "BlowUp" [lit "1"]] prog0
#guard framesEmptyAfter [callStmt "BlowUp" [lit "1"]] prog0

-- THE ORDER-DEPENDENCE GATE FIRES, and this is its FIRST real content in this
-- tier. Two arguments and one contains a call: ARM 6.4.1 leaves the order
-- unspecified and a call can have an effect, so the model refuses rather than
-- picking an order and calling it the language. Inch 2 predicted this rung.
#guard refusedAs "order-dependence" "6.4.1"
         [assign (ident "X") (callOf "Twice" [callOf "Twice" [lit "1"], lit "2"])] prog0

-- ...and it does NOT fire when the order cannot be observed: one argument, or
-- several with no call among them. A gate that refused these would be
-- refusing the language rather than the model's limit.
#guard endsWith "x" (.int int8 14) [assign (ident "X") (callOf "Twice" [lit "7"])] prog0

-- THE CITABLE EXCLUSIONS, each refusing at the clause it would have needed.
#guard refusedAtClause "6.2" [callStmt "OutMode" [lit "1"]] prog0
#guard refusedAtClause "6.4.1" [callStmt "SetX" []] prog0
#guard refusedAtClause "6.4" [callStmt "Nope" []] prog0
#guard refusedAtClause "6.4"
         [.node "CallStmt" sp0 #[.node "CallExpr" sp0 #[.node "DottedName" sp0 #[ident "P", ident "Q"], .leaf "AssocList" sp0 ""]]] prog0
#guard refusedAtClause "4.1.2"
         [.node "CallStmt" sp0 #[.node "CallExpr" sp0 #[ident "Bump", bin "OpDoubleDot" (lit "1") (lit "9")]]] prog0
#guard refusedAtClause "6.4.1"
         [.node "CallStmt" sp0 #[.node "CallExpr" sp0 #[ident "SetX",
            .node "AssocList" sp0 #[.node "ParamAssoc" sp0 #[ident "N", lit "1"]]]]] prog0

-- THE TABLE BUILDER, tested apart from the call rules. One `SubpBody` at the
-- arities measured off the fixtures: SubpBody 6, SubpSpec 4, HandledStmts 2.
private def defName (n : String) : Node := .node "DefiningName" sp0 #[ident n]
private def bodyOfBump : Node :=
  .node "SubpBody" sp0
    #[.leaf "OverridingUnspecified" sp0 "",
      .node "SubpSpec" sp0
        #[.leaf "SubpKindProcedure" sp0 "procedure", defName "Bump", .absent, .absent],
      .absent,
      .node "DeclarativePart" sp0 #[.leaf "AdaNodeList" sp0 ""],
      .node "HandledStmts" sp0
        #[.node "StmtList" sp0 #[assign (ident "X") (bin "OpPlus" (ident "X") (lit "1"))],
          .leaf "AdaNodeList" sp0 ""],
      .leaf "EndName" sp0 "Bump"]

#guard (subpOf bodyOfBump).isSome
#guard (collectSubps 32 [bodyOfBump]).length == 1
-- the name is FOLDED, and an absent ParamSpecList is a parameterless
-- subprogram rather than a failure
#guard match subpOf bodyOfBump with
       | some s => s.name == "bump" && s.params == [] && s.modesOk && !s.isFunction
       | none => false
-- ...and a table built by the BUILDER drives the walker, closing the loop
#guard endsWith "x" (.int int8 1) [callStmt "Bump" []] (collectSubps 32 [bodyOfBump])

-- `containsCall` answers TRUE out of fuel, because its only consumer refuses
-- on true and a refusal is the safe direction.
#guard containsCall 0 (lit "1")
#guard !containsCall 8 (bin "OpPlus" (lit "1") (lit "2"))
#guard containsCall 8 (bin "OpPlus" (callOf "Twice" [lit "1"]) (lit "2"))

-- AND THE INCH-1 GATE FINALLY HAS A CAUSE TO BE ABOUT: `orderDependenceGate`
-- was written expecting an empty bucket. It is no longer vacuous.
#guard !orderDependenceGate [.orderDependence (clauseRef "6.4.1")]
#guard orderDependenceGate [.unsupported (clauseRef "6.4"), .undefined erroneousExecution]

/-! ### INCH 4 — handlers, propagation, and `raise`

**THE `RaiseStmt` FIXTURES BELOW ARE SYNTHETIC AND SAID TO BE.** `RaiseStmt`
is 1,440 nodes corpus-wide and **0 in both envelopes**, so unlike every shape
inch 3 used, this one has no witness in the tree. The rule it drives was
written not to depend on the arity for that reason, and these fixtures pin the
rule's behaviour rather than the frontend's encoding. When the corpus returns
(the re-acquire rung) the encoding gets checked and this label comes off. -/

private def othersChoice : Node := .leaf "OthersDesignator" sp0 "others"
private def namedChoice (n : String) : Node := ident n
private def handler (choices : List Node) (ss : List Node) : Node :=
  .node "ExceptionHandler" sp0
    #[.absent, .node "AlternativesList" sp0 choices.toArray, seq ss]
/-- SYNTHETIC — see the note above. -/
private def raiseOf (n : String) : Node := .node "RaiseStmt" sp0 #[ident n]

private def boom : String := "Boom"

/-- `begin X := 5; raise Boom; exception when others => X := X + 1; end;` -/
private def caught : Subp :=
  { name := "caught", isFunction := false, params := [], modesOk := true,
    body := [assign (ident "X") (lit "5"), raiseOf boom],
    handlers := [handler [othersChoice] [assign (ident "X") (bin "OpPlus" (ident "X") (lit "1"))]] }

/-- The same, handled by NAME rather than by `others`.

**Spelled out rather than `{ caught with … }`**, and the reason is measured
rather than stylistic: a multi-line structure UPDATE does not parse here,
while a multi-line plain instance does (`caught`, just above, is three lines
and elaborates). One-line updates are fine — `TrueOnly` and `outMode` are
both one-liners and both compiled green. -/
private def caughtByName : Subp :=
  { name := "caughtbyname", isFunction := false, params := [], modesOk := true,
    body := [assign (ident "X") (lit "5"), raiseOf boom],
    handlers := [handler [namedChoice "BOOM"] [assign (ident "X") (lit "7")]] }

/-- A handler that does not cover what was raised. -/
private def notCovered : Subp :=
  { name := "notcovered", isFunction := false, params := [], modesOk := true,
    body := [assign (ident "X") (lit "5"), raiseOf boom],
    handlers := [handler [namedChoice "Other_Error"] [assign (ident "X") (lit "7")]] }

/-- A handler that raises again — ARM 11.4: a handler is not its own handler. -/
private def reraises : Subp :=
  { name := "reraises", isFunction := false, params := [], modesOk := true,
    body := [assign (ident "X") (lit "5"), raiseOf boom],
    handlers := [handler [othersChoice] [raiseOf "Second"]] }

private def prog4 : SubpTable :=
  [("caught", caught), ("caughtbyname", caughtByName),
   ("notcovered", notCovered), ("reraises", reraises)]

-- ARM 11.2: an `others` handler CATCHES, and the subprogram then completes
-- normally. X is 6, not 5 -- so THE HANDLER SAW THE WORLD AS OF THE RAISE
-- (X had already become 5), which is ARM 11.4's state rule and not merely
-- "a handler ran".
#guard endsWith "x" (.int int8 6) [callStmt "Caught" []] prog4

-- ...and the frame is popped on the HANDLED path too.
#guard framesEmptyAfter [callStmt "Caught" []] prog4

-- ARM 11.2 + 2.3: a NAMED choice matches case-insensitively -- an exception
-- name is an identifier like any other.
#guard endsWith "x" (.int int8 7) [callStmt "CaughtByName" []] prog4

-- ...and a handler that does NOT cover it lets the exception PROPAGATE
-- (ARM 11.4), with the world the raise left behind: X is 5, the write that
-- preceded the raise, and the trace still holds its row.
#guard raisesKeeping boom "x" (.int int8 5) [callStmt "NotCovered" []] prog4
#guard framesEmptyAfter [callStmt "NotCovered" []] prog4

-- ARM 11.4: a raise INSIDE a handler propagates and is NOT re-handled by the
-- same handler. The caller sees `Second`, never `Boom`.
#guard raisesKeeping "Second" "x" (.int int8 5) [callStmt "Reraises" []] prog4
#guard !raisesKeeping boom "x" (.int int8 5) [callStmt "Reraises" []] prog4

-- ARM 11.3: `raise Foo;` raises Foo. (Synthetic fixture -- see the note.)
#guard raisesKeeping boom "x" (.int int8 0) [raiseOf boom]

-- ...and a BARE `raise` refuses: re-raising needs the current occurrence in W.
#guard refusedAtClause "11.3" [.leaf "RaiseStmt" sp0 "raise;"]
#guard refusedAtClause "11.3" [.node "RaiseStmt" sp0 #[.absent]]

-- `handlerCovers`: `others` covers anything, a name covers itself
-- case-blind, and a different name covers nothing.
#guard handlerCovers boom (handler [othersChoice] [])
#guard handlerCovers boom (handler [namedChoice "boom"] [])
#guard !handlerCovers boom (handler [namedChoice "Other_Error"] [])

-- THE ENCODING, THIRD TIME: the handlers come out of `HandledStmts` slot[1]
-- as a generic `AdaNodeList`, and an EMPTY one is a LEAF. `bodyOfBump` has
-- exactly that, so its handler list must read as empty rather than as
-- malformed.
#guard match subpOf bodyOfBump with
       | some s => s.handlers.isEmpty
       | none => false

/-- The same body, now WITH a handler in slot[1] — an `AdaNodeList`, which is
what the corpus emits, and never an `ExceptionHandlerList` (0 occurrences in
2,976,861 nodes). -/
private def bodyOfCaught : Node :=
  .node "SubpBody" sp0
    #[.leaf "OverridingUnspecified" sp0 "",
      .node "SubpSpec" sp0
        #[.leaf "SubpKindProcedure" sp0 "procedure", defName "Caught2", .absent, .absent],
      .absent,
      .node "DeclarativePart" sp0 #[.leaf "AdaNodeList" sp0 ""],
      .node "HandledStmts" sp0
        #[.node "StmtList" sp0 #[assign (ident "X") (lit "5"), raiseOf boom],
          .node "AdaNodeList" sp0
            #[handler [othersChoice] [assign (ident "X") (bin "OpPlus" (ident "X") (lit "1"))]]],
      .leaf "EndName" sp0 "Caught2"]

#guard match subpOf bodyOfCaught with
       | some s => s.handlers.length == 1
       | none => false
-- ...and a table built by the BUILDER drives the handled path end to end.
#guard endsWith "x" (.int int8 6) [callStmt "Caught2" []] (collectSubps 32 [bodyOfCaught])

end LeanModels.Ada.Ada2012
