/-!
# The ECMAScript tier's deep-embedded AST (`LeanModels.Es`)

The Lean image of the `es-0.2` envelope (`docs/es-envelope-schema.md`).

**This file is a TYPE, not a semantics.** Nothing here evaluates anything;
the evaluator, the completion records and the refusal taxonomy are M2 and
later (`docs/es-charter.md`). A term of type `Envelope` is what
`load_es_program` produces at elaboration time, and what the `#guard`s of
`Examples/es/` are stated about.

`LeanModels/Es/` is a SIBLING of `LeanModels/Python/` and of
`LeanModels/C/`, never a client of either (`docs/c-tier-charter.md` §2.1).

Four shapes are worth reading first, because each is a decision the census
or the schema forced rather than a convenience.

* **The node tree is UNIFORM, not sorted into Stmt/Expr/Pattern.** The C
  lane splits its AST by sort because clang's AST is genuinely sorted.
  ESTree's is not: `ArrayPattern` and `ArrayExpression` are the same
  surface syntax classified by CONTEXT, and the spec's own grammar
  reinterprets a parenthesized expression as a pattern after the fact. A
  Lean sort discipline imposed at M1 would be inventing a classification
  the frontend does not make — so a `Node` carries its `NodeKind` and its
  properties, and any sorting is a job for the tier that gives it meaning.

* **`NodeKind` is a 66-constructor enumeration, not a `String`.** The
  vocabulary is closed and MEASURED (`docs/es262-census.json`), and
  `harness/es_census.py --check-schema` holds this list, the schema
  document's table and `extractors/es/extract.py`'s `VOCABULARY` to the
  same set. Anything outside it arrives as `Node.unsupported` and is
  refused at evaluation, never at ingestion.

* **A numeric literal keeps its SOURCE SPELLING.** `Lit.number` carries
  `"0.1"`, not a `Float`. The tier's Number type is binary64 and the
  decimal→binary conversion is correctly-rounded work the family has
  scheduled (`docs/family-architecture.md` §3.5.5 step 3); a literal
  converted during ingestion would have been silently decided before the
  semantics ever saw it. This is the C lane's integer-literal reasoning,
  reached independently.

* **A REJECTED PARSE IS A VALUE, not an absent one.** `ParseResult` has
  two constructors because 4,248 of the language-core slice's 18,114
  tests assert that their source must NOT parse
  (`docs/es-envelope-schema.md` §0(2)). An ingester that could only
  represent successful parses would make a quarter of the corpus
  unrepresentable.
-/

namespace LeanModels.Es

/-- A source span. `start`/`end` are UTF-16 code-unit offsets, which is
what ESTree producers emit and what the spec's own source-text indexing
uses; `line`/`col` are derived, and exist so a refusal can name a place a
human can find. -/
structure EsSpan where
  start : Nat
  stop : Nat
  line : Nat
  col : Nat
  endLine : Nat
  endCol : Nat
  deriving Repr, DecidableEq, Inhabited

/-- The pinned node vocabulary: exactly the kinds measured over the whole
language-core slice. See the module docstring — this list is gate-checked
against the census and the extractor. -/
inductive NodeKind where
  -- program and statements (23)
  | program
  | variableDeclaration
  | variableDeclarator
  | expressionStatement
  | blockStatement
  | throwStatement
  | ifStatement
  | returnStatement
  | emptyStatement
  | tryStatement
  | catchClause
  | forOfStatement
  | forStatement
  | withStatement
  | breakStatement
  | labeledStatement
  | forInStatement
  | doWhileStatement
  | switchCase
  | continueStatement
  | whileStatement
  | switchStatement
  | debuggerStatement
  -- declarations and classes (9)
  | propertyDefinition
  | methodDefinition
  | classBody
  | classDeclaration
  | functionDeclaration
  | staticBlock
  | importDeclaration
  | importDefaultSpecifier
  | exportDefaultDeclaration
  -- patterns (4)
  | assignmentPattern
  | arrayPattern
  | objectPattern
  | restElement
  -- expressions and the rest (30)
  | identifier
  | literal
  | privateIdentifier
  | memberExpression
  | callExpression
  | binaryExpression
  | functionExpression
  | newExpression
  | property
  | assignmentExpression
  | unaryExpression
  | objectExpression
  | thisExpression
  | arrayExpression
  | classExpression
  | updateExpression
  | yieldExpression
  | arrowFunctionExpression
  | logicalExpression
  | sequenceExpression
  | templateElement
  | spreadElement
  | super
  | conditionalExpression
  | templateLiteral
  | importExpression
  | chainExpression
  | taggedTemplateExpression
  | awaitExpression
  | metaProperty
  deriving Repr, DecidableEq, Inhabited

/-- A `Literal`'s payload. One ESTree kind covers six spec-level types, so
the envelope splits it and this mirrors the split rather than making the
tier re-derive the lexer from raw text. -/
inductive Lit where
  /-- Carried as the SOURCE SPELLING, never as a `Float`. -/
  | number (raw : String)
  | string (value : String)
  | boolean (value : Bool)
  | null
  /-- Digits only, without the trailing `n`. -/
  | bigint (digits : String)
  /-- Recorded, NOT parsed: the RegExp grammar is its own clause. -/
  | regexp (pattern flags : String)
  deriving Repr, DecidableEq, Inhabited

/-- A property value that is NOT a node: the scalar attributes ESTree
hangs off its nodes — an operator's spelling, `computed`, `static`,
`prefix`, a declaration's `var`/`let`/`const`. -/
inductive Scalar where
  | str (s : String)
  | bool (b : Bool)
  | num (n : Int)
  | null
  deriving Repr, DecidableEq, Inhabited

/-- One ESTree node.

**Deliberately NOT a mutual inductive.** `Node` recurses only through
`List`/`Option`/product, exactly as the C lane's `Expr` recurses through
`List Expr` — which keeps `deriving` and the equation compiler on the
well-trodden path. The price is that a node's properties are split in
two, and the split turns out to be the right shape anyway: SCALARS are
the attributes a semantics reads as flags, CHILDREN are the subtrees it
recurses into.

A child list encodes arity uniformly: a single required child is
`[some n]`, an absent optional child is `[]`, and an array with an elided
element (`[1, , 3]`) keeps its hole as `none` rather than being quietly
closed up. -/
inductive Node where
  /-- A node of the pinned vocabulary. Both property lists are sorted by
  name, so the term is canonical and a `#guard` about a node's shape does
  not depend on the extractor's serialization order. -/
  | mk (kind : NodeKind) (span : EsSpan)
      (scalars : List (String × Scalar))
      (children : List (String × List (Option Node)))
  /-- A `Literal`, whose payload is typed rather than left in `scalars`. -/
  | lit (value : Lit) (raw : String) (span : EsSpan)
  /-- Outside the vocabulary. Structured, so it INGESTS and refuses at
  EVALUATION — the family's `Unsupported` discipline. -/
  | unsupported (nodeType : String) (text : String) (span : EsSpan)
  deriving Repr, Inhabited

/-- The outcome of parsing. Two constructors, because a rejection is data.
See the module docstring. -/
inductive ParseResult where
  | ok (program : Node)
  /-- `errorKind` is always `"SyntaxError"` — the only class ECMA-262 lets a
  parse-phase failure be. `message` is the FRONTEND's own text and is
  explicitly NOT normative: it is telemetry so a human can act on a
  refusal, and nothing may branch on it. -/
  | error (errorKind message : String) (line col : Nat)
  deriving Repr, Inhabited

/-- Script or Module — a parse INPUT, not a property of the text. -/
inductive SourceType where
  | script
  | module
  deriving Repr, DecidableEq, Inhabited

/-- The whole `es-0.2` envelope. `languageVersion` is retained because the
edition is an INPUT to the AST, so a mismatch has to be refusable
downstream — the C lane's `profile_id` reasoning. `frontend` is accepted
and not retained. -/
structure Envelope where
  schemaVersion : String
  languageVersion : String
  specRevision : String
  sourceFile : String
  sourceSha256 : String
  sourceType : SourceType
  parse : ParseResult
  deriving Repr, Inhabited

/-! ## The kind table

The one place a name becomes a constructor. Used by the ingester, and by
`kindName` for messages; keeping both directions here is what stops them
from drifting. -/

/-- Every kind with its ESTree spelling, sorted. -/
def kindTable : List (String × NodeKind) :=
  [
   ("ArrayExpression", .arrayExpression),
   ("ArrayPattern", .arrayPattern),
   ("ArrowFunctionExpression", .arrowFunctionExpression),
   ("AssignmentExpression", .assignmentExpression),
   ("AssignmentPattern", .assignmentPattern),
   ("AwaitExpression", .awaitExpression),
   ("BinaryExpression", .binaryExpression),
   ("BlockStatement", .blockStatement),
   ("BreakStatement", .breakStatement),
   ("CallExpression", .callExpression),
   ("CatchClause", .catchClause),
   ("ChainExpression", .chainExpression),
   ("ClassBody", .classBody),
   ("ClassDeclaration", .classDeclaration),
   ("ClassExpression", .classExpression),
   ("ConditionalExpression", .conditionalExpression),
   ("ContinueStatement", .continueStatement),
   ("DebuggerStatement", .debuggerStatement),
   ("DoWhileStatement", .doWhileStatement),
   ("EmptyStatement", .emptyStatement),
   ("ExportDefaultDeclaration", .exportDefaultDeclaration),
   ("ExpressionStatement", .expressionStatement),
   ("ForInStatement", .forInStatement),
   ("ForOfStatement", .forOfStatement),
   ("ForStatement", .forStatement),
   ("FunctionDeclaration", .functionDeclaration),
   ("FunctionExpression", .functionExpression),
   ("Identifier", .identifier),
   ("IfStatement", .ifStatement),
   ("ImportDeclaration", .importDeclaration),
   ("ImportDefaultSpecifier", .importDefaultSpecifier),
   ("ImportExpression", .importExpression),
   ("LabeledStatement", .labeledStatement),
   ("Literal", .literal),
   ("LogicalExpression", .logicalExpression),
   ("MemberExpression", .memberExpression),
   ("MetaProperty", .metaProperty),
   ("MethodDefinition", .methodDefinition),
   ("NewExpression", .newExpression),
   ("ObjectExpression", .objectExpression),
   ("ObjectPattern", .objectPattern),
   ("PrivateIdentifier", .privateIdentifier),
   ("Program", .program),
   ("Property", .property),
   ("PropertyDefinition", .propertyDefinition),
   ("RestElement", .restElement),
   ("ReturnStatement", .returnStatement),
   ("SequenceExpression", .sequenceExpression),
   ("SpreadElement", .spreadElement),
   ("StaticBlock", .staticBlock),
   ("Super", .super),
   ("SwitchCase", .switchCase),
   ("SwitchStatement", .switchStatement),
   ("TaggedTemplateExpression", .taggedTemplateExpression),
   ("TemplateElement", .templateElement),
   ("TemplateLiteral", .templateLiteral),
   ("ThisExpression", .thisExpression),
   ("ThrowStatement", .throwStatement),
   ("TryStatement", .tryStatement),
   ("UnaryExpression", .unaryExpression),
   ("UpdateExpression", .updateExpression),
   ("VariableDeclaration", .variableDeclaration),
   ("VariableDeclarator", .variableDeclarator),
   ("WhileStatement", .whileStatement),
   ("WithStatement", .withStatement),
   ("YieldExpression", .yieldExpression)
  ]

/-- The ESTree spelling of a kind. -/
def kindName (k : NodeKind) : String :=
  match kindTable.find? (fun p => p.2 == k) with
  | some (n, _) => n
  | none => "?"

/-- The kind of an ESTree spelling, when it is in the vocabulary. -/
def kindOf? (s : String) : Option NodeKind :=
  (kindTable.find? (fun p => p.1 == s)).map (·.2)

/-- The vocabulary's size, as a checkable fact. -/
def vocabularySize : Nat := kindTable.length

end LeanModels.Es
