# The ECMAScript envelope — schema `es-0.2`

Normative for `extractors/es/extract.py` and for `LeanModels/Es/Json.lean`.
Mirrors `docs/envelope-schema.md`, `docs/sv-envelope-schema.md` and
`docs/c-envelope-schema.md`; `docs/es-charter.md` is the tier's charter and
`docs/es262-census.json` is the measurement every table below is DERIVED
from rather than chosen.

---

## 0 What is different about the ES envelope, in one place

Four things this schema has that its three siblings do not. Each is forced
by a measurement in `docs/es262-census.json`, and none is a preference.

1. **`language_version` is a first-class field, and the edition is an INPUT
   to the AST — not a stamp on the side of it.** This is the family's §1.5
   ruling, and for ECMAScript it is load-bearing rather than hygienic: the
   grammar a parser accepts is a function of the edition. Measured on the
   core slice, **106 of 18,114 tests parse under the living draft's grammar
   and not under a ratified edition's** — decorators, `import.defer`,
   source-phase imports. Same source, different edition, different program.
   The ingester REFUSES a mismatch, exactly as `load_c_program` refuses a
   `profile_id` mismatch, and `docs/es-edition.json` is the pin it checks
   against.

2. **A REJECTED parse is a valid envelope, not a missing one.** This is the
   big one and it has no analogue in the other three lanes. **4,248 of the
   core slice's 18,114 tests declare `negative: {phase: parse}`** — 23% of
   the corpus asserts that the source must NOT parse. A schema that could
   only represent successful parses would make a quarter of its own corpus
   unrepresentable, and the extractor would have to signal those tests by
   failing, which the never-fail contract forbids. So `parse.status` is a
   first-class field with two values and a rejection carries its reason
   (§4).

3. **`source_type` is a parse INPUT, not a property of the text.** The same
   bytes can be a Script or a Module and mean different things — `await`
   is an identifier in one and an operator in the other. test262 says which
   via `flags: [module]`, which is METADATA the frontend never sees.
   Measured: probing script-then-module, **5 core-slice files parse only as
   `module`**. The envelope records which sourceType produced it, and the
   cache key includes it, because otherwise two different programs share a
   cache entry.

4. **`parse.status: "ok"` is a claim about the FRONTEND, never about
   validity.** Early errors are static semantics the parser does not carry:
   measured, **acorn accepts 285 core-slice tests that test262 says must be
   rejected at parse phase**. The envelope therefore never claims the source
   is a valid ECMAScript Program, and §8 states that limit rather than
   letting a reader infer the stronger claim.

---

## 1 Envelope

```json
{
  "schema_version": "es-0.2",
  "language": "ecmascript",
  "language_version": "ES2026",
  "spec_revision": "es2026-errata",
  "frontend": {"name": "acorn-estree", "version": "acorn-8"},
  "source_file": "test/language/statements/if/cptn-normal.js",
  "source_sha256": "<hex sha256 of source bytes>",
  "source_type": "script",
  "parse": {"status": "ok"},
  "program": {"kind": "Program", "body": [ <node>... ]},
  "lean_blocks": []
}
```

`frontend.version` is the parser's **FAMILY** (`acorn-8`), never the point
release. That correction is recorded twice in `docs/backlog.md` and cost 53
files of re-extraction the second time; reproducing it in a new lane, having
read the entry, would be inexcusable.

`language_version` is the registry's edition token and is the same string
that names `LeanModels/Es/ES2026/`, so path, envelope and citation cannot
drift. `spec_revision` names the bytes that token was pinned to
(`docs/es-edition.json`); the two are deliberately different strings,
because the revision is not a valid Lean identifier.

`lean_blocks` is `[]` and exists so the envelope stays language-neutral;
the inline-spec convention has no ECMAScript form yet.

**Cache key**:
`<stem>-<sha256(source)[:16]>-<sha256(extract.py)[:8]>-<language_version>-<source_type>`
— the existing `extractor_digest()` discipline plus the two inputs §0
identifies. An ES envelope is a function of (source, extractor, EDITION,
SOURCETYPE).

---

## 2 Spans

Every node carries

```json
"span": {"start": 412, "end": 431, "line": 24, "col": 8, "end_line": 24, "end_col": 27}
```

`start`/`end` are UTF-16 code-unit offsets, which is what ESTree producers
emit and what the spec's own source-text indexing uses; `line`/`col` are
derived and are for humans and refusal messages. Both are kept because a
refusal that cannot name a line is one a human cannot act on, and an
offset that disagrees with a line number is a bug the schema should make
visible rather than hide.

There is no macro layer — ECMAScript has no preprocessor, which is the one
place this envelope is SIMPLER than C's.

---

## 3 The node vocabulary — 66 kinds, and where they come from

**The ingester REFUSES any `kind` outside this table**, emitting an
`Unsupported` leaf (§5). The list is exactly the census's measured
vocabulary over the whole 18,114-test language-core slice
(`docs/es262-census.json` → `frontend.node_types`), not a reading of the
ESTree specification. Counts are today's corpus and are informative, not
normative.

### 3.1 Program and statements (23)

`Program` 14045, `VariableDeclarator` 130710, `VariableDeclaration` 130062,
`ExpressionStatement` 74441, `BlockStatement` 49100, `ThrowStatement` 17863,
`IfStatement` 15629, `ReturnStatement` 13117, `EmptyStatement` 2623,
`TryStatement` 1152, `CatchClause` 1092, `ForOfStatement` 718,
`ForStatement` 598, `WithStatement` 318, `BreakStatement` 194,
`LabeledStatement` 141, `ForInStatement` 139, `DoWhileStatement` 90,
`SwitchCase` 84, `ContinueStatement` 74, `WhileStatement` 69,
`SwitchStatement` 40, `DebuggerStatement` 1

**Two of these are worth naming.** `SwitchStatement` is 40 sites and
`SwitchCase` 84 — where the C lane's flagship corpus had **zero** `switch`
and had to make it rung R1, this corpus has it from the start, so it is v0
vocabulary here and not a rung. And `WithStatement` (318) exists only in
sloppy mode; it is in the vocabulary because the corpus writes it, and it
is a semantics problem for later, not an ingestion one.

### 3.2 Declarations and classes (9)

`PropertyDefinition` 109312, `MethodDefinition` 12379, `ClassBody` 6284,
`ClassDeclaration` 3257, `FunctionDeclaration` 2581, `StaticBlock` 43,
`ImportDeclaration` 1, `ImportDefaultSpecifier` 1,
`ExportDefaultDeclaration` 1

**The three module nodes appear once each**, which is the measured
confirmation that excluding the module system from the core slice
(`docs/es-charter.md` §1.5) removes essentially all of it rather than
leaving a residue: the slice already excludes `language/{module-code,
import,export}` and every `module`-flagged test, and what survives is three
nodes in the whole 18,114-test corpus.

### 3.3 Patterns (4)

`AssignmentPattern` 6460, `ArrayPattern` 4481, `ObjectPattern` 2973,
`RestElement` 1305

Destructuring is not a corner of this corpus — `destructuring-binding` is
the largest single feature tag in the core slice at 5,495 tests — so the
pattern nodes are v0.

### 3.4 Expressions and the rest (30)

`Identifier` 442415, `Literal` 185577, `PrivateIdentifier` 119243,
`MemberExpression` 94127, `CallExpression` 74148, `BinaryExpression` 54479,
`FunctionExpression` 26127, `NewExpression` 23350, `Property` 22931,
`AssignmentExpression` 18818, `UnaryExpression` 17695,
`ObjectExpression` 11336, `ThisExpression` 9285, `ArrayExpression` 4702,
`ClassExpression` 3027, `UpdateExpression` 1370, `YieldExpression` 1171,
`ArrowFunctionExpression` 970, `LogicalExpression` 940,
`SequenceExpression` 555, `TemplateElement` 360, `SpreadElement` 308,
`Super` 273, `ConditionalExpression` 233, `TemplateLiteral` 194,
`ImportExpression` 175, `ChainExpression` 118,
`TaggedTemplateExpression` 93, `AwaitExpression` 26, `MetaProperty` 22

**`PrivateIdentifier` at 119,243 is the corpus telling the tier what it is
about.** Private class fields are the third-largest node kind in the whole
slice, ahead of `MemberExpression` and `CallExpression`, because the
class-fields feature tags together (`class-fields-private`,
`class-methods-private`, `class-static-fields-private`,
`class-static-methods-private`) account for 3,455 tests. A tier that
treated private names as an advanced corner would be wrong about its own
corpus — the same lesson `docs/c-tier-charter.md` §1.3 recorded when its
census found 71 file-scope mutable objects.

### 3.5 `Literal` carries a typed payload, and one of its types is deferred

`Literal` is one ESTree kind covering six spec-level types. The envelope
splits it, because a tier that had to re-derive the type from the raw text
would be re-implementing the lexer:

```json
{"kind": "Literal", "value_type": "number", "raw": "0.1", "value": "0.1"}
{"kind": "Literal", "value_type": "string", "raw": "'a\\n'", "value": "a\n"}
{"kind": "Literal", "value_type": "boolean", "value": true}
{"kind": "Literal", "value_type": "null"}
{"kind": "Literal", "value_type": "bigint", "raw": "10n", "value": "10"}
{"kind": "Literal", "value_type": "regexp", "raw": "/a/g", "pattern": "a", "flags": "g"}
```

**`number` is carried as its RAW TEXT and never as a host double**, and
this is the one place the schema is opinionated. The extractor runs under
CPython, whose float is also binary64, so round-tripping would *probably*
be exact — but "probably exact" is how a silent wrong answer enters, and
the correctly-rounded decimal→binary conversion is a real algorithm the
family has already scheduled (`docs/family-architecture.md` §3.5.5 step 3).
The envelope hands Lean the digits the programmer wrote and lets the tier
do the conversion under its own rules.

`regexp` is carried as `pattern` + `flags` and is **not** parsed further.
The RegExp grammar is its own clause (§22.2) and its own sub-language; the
envelope records it faithfully and the tier refuses it until a rung buys
it.

---

## 4 The parse VERDICT

```json
"parse": {"status": "ok"}
```

```json
"parse": {
  "status": "error",
  "error_kind": "SyntaxError",
  "message": "Unexpected token",
  "span": {"start": 412, "line": 24, "col": 8}
},
"program": null
```

Exactly two `status` values. `"error"` is a **successful extraction of a
source that does not parse** — the extractor exits 0, the envelope is
well-formed, and `program` is `null`. This is what makes the 4,248
parse-negative tests representable, and it is the difference between a
frontend that can be SCORED and one that can only be run.

`error_kind` is `"SyntaxError"` for everything a parser rejects, because
that is the only class ECMA-262 lets a parse-phase failure be, and test262
agrees to the digit: of 4,732 negative tests suite-wide, **4,696 name
`SyntaxError`**.

**`message` is the frontend's own text and is explicitly NOT normative.**
It is recorded so a human can act on a refusal and so a drift in the
frontend is visible; nothing in the tier may branch on it. This is the same
discipline `harness/leanpy_survey.py` applies to exception messages, where
the message is telemetry (SAME/DRIFT/ABSENT) and never a verdict.

---

## 5 `Unsupported`

Anything outside §3's vocabulary becomes a leaf, and the extractor NEVER
fails on valid ECMAScript:

```json
{"kind": "Unsupported", "node_type": "Decorator", "text": "@dec", "span": {...}}
```

`node_type` is the ESTree type the frontend produced; `text` is at most 200
characters of source. The node is STRUCTURED, so it ingests and refuses at
EVALUATION rather than at ingestion — the family's `Unsupported` discipline,
and the one `docs/backlog.md` §L14 warns a node count cannot see.

---

## 6 Determinism

* Sorted keys; a double run is byte-identical.
* Hard errors — unreadable file, edition mismatch, a frontend that crashes
  rather than rejecting — exit non-zero and say why. **A source that does
  not PARSE is not a hard error** (§4); conflating the two is precisely the
  bug that would make a quarter of the corpus unrepresentable.
* Exactly one envelope per source. In batch mode, one row per input in
  input order, and a `{"status":"runner-error"}` row rather than a missing
  row.

---

## 7 What the ingester will check, and why the census is its oracle

The `#guard`s the M1 fixture will carry, every one a fact
`docs/es262-census.json` independently knows — which is why the census
landed as an instrument, and landed first:

1. `schema_version = "es-0.1"`, `language = "ecmascript"`.
2. `language_version = "ES2026"` and it MATCHES `docs/es-edition.json`.
3. The envelope's `source_sha256` matches the bytes on disk.
4. Every `kind` in the tree is one of the 66.
5. For the positive fixture: `parse.status = "ok"` and `program` is
   non-null.
6. For the **negative** fixture: `parse.status = "error"`,
   `error_kind = "SyntaxError"`, `program = null` — so the tier's first
   statement about ECMAScript includes something it must REJECT.
7. A count the census fixes in advance (node kinds present in the fixture),
   checked non-vacuously: flipping it makes Lean report the failing
   expression.

---

## 8 Honest limits

* **The envelope does not claim its source is valid ECMAScript.**
  `parse.status: "ok"` means the pinned frontend accepted it. Early errors
  are a separate obligation, measured at **285 core-slice tests** the
  frontend under-rejects, and until an early-error tier exists the correct
  reading of an `ok` envelope is "syntactically accepted", not "well-formed
  Program". §0(4).
* **`source_type` is supplied, not inferred.** For test262 it comes from
  `flags: [module]`. For an arbitrary file there is no rule in the language
  that decides it, which is a fact about ECMAScript and not a gap here.
* **RegExp bodies and template cooking are recorded, not analysed** (§3.5).
* **The 66 kinds are this corpus's vocabulary, not the language's.** The C
  lane could say its 45 kinds were stable across an 11.3% corpus growth
  because it had two data points; this lane has one, and the honest
  statement is that a second corpus is what would turn 66 from a corpus
  fact into a language fact. `docs/c-tier-charter.md` §3.3 makes exactly
  this move for C, and it is owed here too.
