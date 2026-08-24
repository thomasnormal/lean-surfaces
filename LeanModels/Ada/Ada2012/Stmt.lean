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
  (w.objects.find? (fun p => p.1 == foldId name)).map Prod.snd

/-- Replace a named object's value. **Only ever called after `lookupObj`
succeeded** — an assignment to an undeclared name is refused before this,
because inch 2 models no declaration — so this updates in place and never
creates, which is what keeps a refused program from quietly acquiring a
variable. -/
def updateObj (w : AdaWorld) (name : String) (v : Val) : AdaWorld :=
  { w with objects := w.objects.map (fun p => if p.1 == foldId name then (p.1, v) else p) }

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

/-- Evaluate an expression. Structurally recursive on `fuel`, so the gate can
run it in the kernel. Shaped like `LeanModels/Es/Eval.lean`'s walker: match
the node's SHAPE, then dispatch on its `kind`, then a loud default. -/
def evalExpr : Nat → Node → AdaM AdaWorld Val
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
          s!"expression leaf '{k}' is outside inch 2's vocabulary"
    | .node k _ ch =>
      match k with
      | "ParenExpr" =>
        if ch.size == 1 then evalExpr fuel ch[0]!
        else refuse (.unsupported (clauseRef "4.4")) "ParenExpr: unexpected arity"
      | "UnOp" =>
        if ch.size != 2 then refuse (.unsupported (clauseRef "4.5")) "UnOp: unexpected arity"
        else do
          let v ← evalExpr fuel ch[1]!
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
              s!"unary operator '{u}' is outside inch 2's vocabulary"
      | "BinOp" =>
        if ch.size != 3 then refuse (.unsupported (clauseRef "4.5")) "BinOp: unexpected arity"
        else do
          let l ← evalExpr fuel ch[0]!
          let r ← evalExpr fuel ch[2]!
          let op := kindOf ch[1]!
          match operands l r with
          | none =>
            refuse (.unsupported (clauseRef "4.5"))
              s!"operator '{op}' on these operand types is outside inch 2's vocabulary"
          | some (sub, x, y) =>
            match applyArith sub op x y with
            | some res => ofAbrupt res
            | none =>
              refuse (.unsupported (clauseRef "4.5"))
                s!"binary operator '{op}' is outside inch 2's vocabulary"
      | "RelationOp" =>
        if ch.size != 3 then refuse (.unsupported (clauseRef "4.5.2")) "RelationOp: unexpected arity"
        else do
          let l ← evalExpr fuel ch[0]!
          let r ← evalExpr fuel ch[2]!
          let op := kindOf ch[1]!
          match l.asInt, r.asInt with
          | some x, some y =>
            match applyRel op x y with
            | some v => pure v
            | none =>
              refuse (.unsupported (clauseRef "4.5.2"))
                s!"relational operator '{op}' is outside inch 2's vocabulary"
          | _, _ =>
            refuse (.unsupported (clauseRef "4.5.2"))
              s!"relational operator '{op}' on non-integer operands is outside inch 2's vocabulary"
      | _ =>
        refuse (.unsupported (clauseRef "4.4"))
          s!"expression node '{k}' is outside inch 2's vocabulary"
    | .absent =>
      refuse (.unsupported (clauseRef "4.4")) "an ABSENT node is not an expression"
    | .unsupported cls _ _ =>
      refuse (.unsupported (clauseRef "4.4"))
        s!"frontend node class '{cls}' is outside the pinned vocabulary"

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

/-- Execute a sequence of statements (ARM 5.1).

ONE function over a LIST, so the whole tier is structurally recursive on
`fuel` with no mutual block. `elsif` is handled by **lowering** — ARM 5.3's
`elsif` is a nested `if`, and the rule rebuilds it as one. -/
def execStmts : Nat → List Node → AdaM AdaWorld Unit
  | 0, _ => exhausted
  | _ + 1, [] => pure ()
  | fuel + 1, s :: rest =>
    match s with
    | .leaf k _ _ =>
      match k with
      -- ARM 5.1: null_statement. A LEAF, because the extractor emits a
      -- childless node as a leaf carrying its source text.
      | "NullStmt" => execStmts fuel rest
      | _ =>
        refuse (.unsupported (clauseRef "5.1"))
          s!"statement leaf '{k}' is outside inch 2's vocabulary"
    | .node k esp ch =>
      match k with
      -- ARM 5.1: a sequence_of_statements, SPLICED rather than recursed
      -- into, which is what keeps this one function.
      | "StmtList" => execStmts fuel (ch.toList ++ rest)
      | "NullStmt" => execStmts fuel rest
      -- ARM 5.2: assignment_statement.
      | "AssignStmt" =>
        if ch.size != 2 then refuse (.unsupported (clauseRef "5.2")) "AssignStmt: unexpected arity"
        else
          match ch[0]! with
          | .leaf "Identifier" _ name => do
            let v ← evalExpr fuel ch[1]!
            let w ← get
            match lookupObj w name with
            | none =>
              refuse (.unsupported (clauseRef "3.3"))
                s!"'{name}' is not in the store — inch 2 models no object declaration"
            | some cur => do
              let v' ← convertTo cur v
              modify (fun w' => updateObj w' name v')
              execStmts fuel rest
          | target =>
            refuse (.unsupported (clauseRef "5.2"))
              s!"assignment target '{kindOf target}' is not a simple name — the target-shape census has not run"
      -- ARM 5.3: if_statement.
      | "IfStmt" =>
        if ch.size != 4 then refuse (.unsupported (clauseRef "5.3")) "IfStmt: unexpected arity"
        else do
          let c ← evalExpr fuel ch[0]!
          match c.asBool with
          | none =>
            refuse (.unsupported (clauseRef "5.3"))
              "an if condition that is not Boolean is outside inch 2's vocabulary"
          | some true => execStmts fuel (ch[1]! :: rest)
          | some false =>
            -- An EMPTY elsif list is a LEAF, not a node with no children, so
            -- a non-node here means "no elsif parts" and not "malformed".
            let elsifs :=
              match ch[2]! with
              | .node "ElsifStmtPartList" _ es => es.toList
              | _ => ([] : List Node)
            match elsifs with
            | [] =>
              match ch[3]! with
              | .node "ElsePart" _ ep => execStmts fuel (ep.toList ++ rest)
              | _ => execStmts fuel rest
            | e :: es =>
              match e with
              | .node "ElsifStmtPart" _ ec =>
                if ec.size != 2 then refuse (.unsupported (clauseRef "5.3")) "ElsifStmtPart: unexpected arity"
                else
                  execStmts fuel
                    (Node.node "IfStmt" esp
                      #[ec[0]!, ec[1]!, Node.node "ElsifStmtPartList" esp es.toArray, ch[3]!] :: rest)
              | bad =>
                refuse (.unsupported (clauseRef "5.3"))
                  s!"elsif part '{kindOf bad}' is outside inch 2's vocabulary"
      | _ =>
        refuse (.unsupported (clauseRef "5.1"))
          s!"statement node '{k}' is outside inch 2's vocabulary"
    | other =>
      refuse (.unsupported (clauseRef "5.1"))
        s!"statement node '{kindOf other}' is outside inch 2's vocabulary"

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

private def endsWith (name : String) (v : Val) (ss : List Node) : Bool :=
  match execStmts 64 ss w0 with
  | .ok (.ok _, w') => match lookupObj w' name with
                       | some u => u == v
                       | none => false
  | _ => false

private def raisesKeeping (exc : String) (name : String) (v : Val) (ss : List Node) : Bool :=
  match execStmts 64 ss w0 with
  | .ok (.error (.raised n _), w') =>
      n == exc && (match lookupObj w' name with
                   | some u => u == v
                   | none => false) && w'.trace == [row0]
  | _ => false

private def refusedAtClause (clause : String) (ss : List Node) : Bool :=
  match execStmts 64 ss w0 with
  | .error (.unsupported c _ _) => c.className == "unsupported" && c.detail.clause == clause
  | _ => false

private def timedOut (fuel : Nat) (ss : List Node) : Bool :=
  match execStmts fuel ss w0 with
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

-- ARM 5.1: a statement kind outside the rung. CallStmt is 56,062 nodes, 2.7x
-- the assignments, and it is inch 3's.
#guard refusedAtClause "5.1" [.node "CallStmt" sp0 #[ident "P"]]

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

end LeanModels.Ada.Ada2012
