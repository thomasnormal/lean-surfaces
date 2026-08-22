/-!
# The Ada tier's deep-embedded AST (`LeanModels.Ada`)

The Lean image of the `ada-0.1` envelope (`docs/ada-envelope-schema.md`).

**This file is a TYPE, not a semantics.** Nothing here evaluates anything;
the semantics is M2 and does not exist. A term of type `Envelope` is what
`load_ada_program` produces at elaboration time, and what the `#guard`s of
`Examples/ada/` are stated about.

## The one decision worth reading first: the node is KIND-AGNOSTIC

The C lane's `Ast.lean` has one constructor per node kind, because its
census measured **45**. Ada's census measured **280** reached by the ACATS
corpus, out of 316 the grammar declares (`docs/backlog.md` §L74). Two
hundred and eighty hand-written constructors would be a transcription, and
`docs/ada-envelope-schema.md` §3 already ruled against exactly that
transcription in its own text: the vocabulary lives in
`docs/ada-construct-census.json` and is CHECKED at ingestion, never restated.

So `Node` carries `kind : String` and the ingester validates it against the
census. That is not a shortcut, it is the same rule one level down:

> **If the TYPE enumerated the kinds, the type would BE the vocabulary
> claim — and it would drift from the census the moment the corpus moved,
> with a rebuild rather than a gate as the only way to notice.**

It also makes the type provably edition-INSENSITIVE, which is what puts this
file in the version-neutral trunk (see `LeanModels/Ada.lean`): Ada 2022's
`ParallelLoopStmt` would add a *string*, not a constructor.

The cost is named rather than hidden: a `kind` is not checked by the Lean
type system, so a semantics built on this must pattern-match on strings and
have a loud default. That is M2's problem, and M2 will have the census to
enumerate against.

## Two smaller shapes, each forced by a measurement

* **`Node.absent` is a constructor.** The envelope preserves a null child as
  `null` because in Ada an ABSENT optional field is meaningful — a missing
  default expression is not the same program as a present one. Making it a
  constructor rather than `Option Node` keeps the nested inductive simple
  and makes the absence impossible to drop silently.
* **A leaf keeps its SOURCE SPELLING.** An `IntLiteral`'s text is
  `"16#FF#"`, not a `Nat`, for the C lane's reason (`LeanModels/C/Ast.lean`):
  a literal decided during ingestion would have been decided before the
  semantics ever saw it.
-/

namespace LeanModels.Ada

/-- A source span. All four components are required: the scoreboard emits
the ACAA's `CERR` records, which carry a line AND a position, and the ACATS
User's Guide calls the line *"critical to the correct operation of the
grading tool"* (`docs/ada-envelope-schema.md` §0.5). A span the ingester
dropped is a verdict the tier cannot produce.

Defined here rather than reused from `LeanModels.Core.Basic`: that `Span` is
the Python lane's, with Python's own field names (`lineno`, `colOffset`), and
`LeanModels/Ada/` is a SIBLING of `LeanModels/Python/`, never a client
(`docs/c-tier-charter.md` §2.1, inherited). -/
structure AdaSpan where
  line : Nat
  col : Nat
  endLine : Nat
  endCol : Nat
deriving Repr, Inhabited, BEq, DecidableEq

/-- One libadalang node.

`kind` is the frontend's own `kind_name`, preserved exactly — see the module
docstring for why it is a `String` and not a constructor. -/
inductive Node where
  /-- An interior node: its `kind`, its span, and its children in source
  order. -/
  | node (kind : String) (span : AdaSpan) (children : Array Node)
  /-- A leaf: its `kind`, its span, and its source text. -/
  | leaf (kind : String) (span : AdaSpan) (text : String)
  /-- An ABSENT optional child. Ada distinguishes a missing default
  expression from a present one, so this is a value and not an omission. -/
  | absent
  /-- Outside the pinned vocabulary. Carries libadalang's own node class so
  a refusal can name a frontend concept a human can act on, plus at most 200
  characters of source. -/
  | unsupported (nodeClass : String) (span : AdaSpan) (text : String)
deriving Repr, Inhabited

/-- One source file the envelope was extracted from.

`lineEndings` is `"lf"` or `"crlf"` and is NOT decoration: the ACATS ZIP
delivery ships CRLF and the ACAA's own tools die on it, so an envelope that
could not say which it saw could not explain a byte-count discrepancy
against the same nominal source (`docs/ada-envelope-schema.md` §1). -/
structure SourceFile where
  path : String
  sha256 : String
  lineEndings : String
deriving Repr, Inhabited, BEq, DecidableEq

/-- One Ada compilation unit.

`name` and `kind` are `Option` because libadalang resolves them through a
property that can fail on a unit whose context is absent, and a fabricated
name would be worse than an honest `none`.

`order` is the compilation ORDER, and it is first-class for a measured
reason: **680 of 4,810 ACATS files — one in seven — have a name that is not
among their unit names**, and 723 declare more than one unit
(`docs/backlog.md` §L74). Deriving a top unit from a path is `docs/backlog.md`
§L67's mistake, and in Ada it is the common case. -/
structure CompilationUnit where
  name : Option String
  kind : Option String
  file : Nat
  order : Nat
  position : Nat
  span : AdaSpan
  decl : Node
deriving Repr, Inhabited

/-- One ACATS marking, carried out of a COMMENT the AST discards.

These are the expected result of 1,484 class-B and 71 class-L tests — 37.1%
of the official suite — and they live in a separate array rather than on
nodes, because the payload is what the FRONTEND produced and a marking is
what the SUITE said (`docs/ada-envelope-schema.md` §0.5). -/
structure Marking where
  kind : String
  file : Nat
  line : Nat
  col : Nat
  endLine : Nat
  endCol : Nat
  text : String
deriving Repr, Inhabited, BEq, DecidableEq

/-- A parse diagnostic, retained rather than discarded: a class B or L test
is EXPECTED to be illegal, so a diagnostic is data about the corpus and not
necessarily a fault. -/
structure Diagnostic where
  file : Nat
  message : String
deriving Repr, Inhabited, BEq, DecidableEq

/-- The whole `ada-0.1` envelope.

The envelope is loaded whole, not just its units, for the C lane's reason:
`markings` and `sourceFiles` are claims the ingester must be checkable
against too. -/
structure Envelope where
  schemaVersion : String
  language : String
  /-- The registry's edition token (`Ada2012`, `Ada2022`). First-class
  because Ada's version pair is FORCED — the ARM is Ada 2022 and the
  official suite is Ada 2012 — so both are live from the first envelope
  (`docs/ada-charter.md` §1.3). -/
  languageVersion : String
  profileId : String
  sourceFiles : Array SourceFile
  compilationUnits : Array CompilationUnit
  markings : Array Marking
  diagnostics : Array Diagnostic
  unsupportedCount : Nat
deriving Repr, Inhabited

/-! ## Walkers

Kept deliberately few. This file is a type; anything that needs to know what
a `kind` MEANS belongs to `LeanModels/Ada/Ada2012/`, which is where meaning
lives. -/

/-- Every node in the subtree, root first, in source order. -/
partial def Node.flatten : Node → Array Node
  | n@(.node _ _ children) =>
      children.foldl (fun acc c => acc ++ c.flatten) #[n]
  | n => #[n]

/-- How many nodes carry this kind, anywhere in the subtree. -/
def Node.countKind (n : Node) (kind : String) : Nat :=
  (n.flatten.filter fun
    | .node k _ _ => k == kind
    | .leaf k _ _ => k == kind
    | _ => false).size

/-- Every distinct `kind` in the subtree, plus `"Unsupported"` for each
unsupported leaf — the shape `harness/ada_round_trip.py`'s vocabulary check
compares against the census. -/
def Node.kinds (n : Node) : Array String :=
  n.flatten.map fun
    | .node k _ _ => k
    | .leaf k _ _ => k
    | .absent => "Absent"
    | .unsupported _ _ _ => "Unsupported"

/-- The compilation units, in the order the envelope recorded — never
re-derived. -/
def Envelope.unitNames (e : Envelope) : Array (Option String) :=
  e.compilationUnits.map (·.name)

/-- Markings of one kind, across every source file. -/
def Envelope.markingsOf (e : Envelope) (kind : String) : Array Marking :=
  e.markings.filter (·.kind == kind)

end LeanModels.Ada
