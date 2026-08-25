import LeanModels.Es

/-!
# M1's round-trip: two test262 sources, ingested, with the census as oracle

`docs/es-charter.md` §5.3 inch 6. Source → envelope → Lean AST literal →
`#guard`, with **no evaluator in the repository**.

Two fixtures, and the pair is the point:

* `ifCptn` — `test/language/statements/if/cptn-else-true-nrml.js`, an
  ordinary positive test that PARSES;
* `classDup` —
  `test/language/statements/class/syntax/early-errors/class-definition-evaluation-block-duplicate-binding.js`,
  which test262 declares `negative: {phase: parse}` and which therefore
  must NOT parse.

**The tier's first statement about ECMAScript includes something it must
REJECT**, which is the reasoning that chose `pyfloordiv` for the C lane —
and here it is not a nicety: 4,248 of the language-core slice's 18,114
tests are parse-negative, so a tier that could not represent a rejection
could not be scored on 23% of its own corpus.

Every count below is one `harness/es_census.py` independently knows, which
is why the census landed as an instrument and landed first.
-/

namespace Examples.es.test262

open LeanModels.Es

load_es_program ifCptn from "Examples/es/test262/if_cptn.json"
load_es_program classDup from "Examples/es/test262/class_dup_binding.json"
/-- A fixture that CONTAINS DECLARATIONS. Its absence is why `es-0.1`'s
node-type collision survived: ESTree gives `VariableDeclaration` a property
called `kind`, the extractor wrote the node TYPE to `kind` as well, and the
property won — so every `var` serialized with its type gone. Neither existing
fixture had a declaration in it, and the vocabulary census reads acorn
directly, so nothing looked. The scoreboard's first real run hit it on
`assert.js`, which meant no test262 test had ever been ingestible. -/
load_es_program varDecl from "Examples/es/test262/var_decl.json"

/-! ## The envelope's own claims -/

#guard ifCptn.schemaVersion == "es-0.2"
#guard ifCptn.languageVersion == "ES2026"
#guard ifCptn.specRevision == "es2026-errata"
#guard ifCptn.sourceType == SourceType.script
#guard ifCptn.sourceFile == "test/language/statements/if/cptn-else-true-nrml.js"

/-! ## The vocabulary is closed, and its size is the measured one -/

/-! ### The node type survives an ESTree `kind` property — `es-0.2`'s reason -/

#guard varDecl.schemaVersion == "es-0.2"
/- The declaration ingests AT ALL, which is what `es-0.1` could not do. -/
#guard match varDecl.parse with | .ok _ => true | .error .. => false
/- Its type is `VariableDeclaration` and its own `kind` scalar is `"var"` —
both present, neither having overwritten the other. -/
#guard match varDecl.parse with
  | .ok p =>
    (p.kids "body").any (fun n =>
      n.kindOf == some NodeKind.variableDeclaration && n.str? "kind" == some "var")
  | .error .. => false

#guard vocabularySize == 66
#guard (kindOf? "IfStatement").isSome
#guard (kindOf? "Decorator").isNone
#guard kindName NodeKind.program == "Program"

/-! ## The POSITIVE fixture parsed, and its shape is the census's -/

#guard ifCptn.accepted
#guard ifCptn.program?.isSome

/- The root of a parsed program is a `Program` node. -/
#guard match ifCptn.program? with
  | some (.mk .program _ _ _) => true
  | _ => false

/- Six distinct kinds, 37 nodes: `Program` 1, `ExpressionStatement` 4,
`CallExpression` 8, `MemberExpression` 4, `Identifier` 14, `Literal` 6.
`Literal` is not in `kinds` (it is `Node.lit`), so the walk counts 31. -/
#guard match ifCptn.program? with
  | some p => p.kinds.length == 31
  | none => false

/- No `Unsupported` leaf: this source is entirely inside the vocabulary. -/
#guard match ifCptn.program? with
  | some p => p.unsupportedTypes == []
  | none => false

/- `Identifier` is the most frequent kind here, as it is corpus-wide. -/
#guard match ifCptn.program? with
  | some p => (p.kinds.filter (· == NodeKind.identifier)).length == 14
  | none => false

/-! ## The NEGATIVE fixture did not parse — and that is a value, not a gap -/

#guard !classDup.accepted
#guard classDup.program?.isNone
#guard classDup.schemaVersion == "es-0.1"
#guard classDup.languageVersion == "ES2026"

/- The error class is the only one a parse-phase failure can be, and
test262 agrees to the digit: 4,696 of its 4,732 negative tests name
`SyntaxError`. -/
#guard match classDup.parse with
  | .error kind _ _ _ => kind == "SyntaxError"
  | .ok _ => false

/- The frontend's message is RECORDED so a human can act on a refusal,
and is explicitly NOT normative — nothing in the tier may branch on it.
This `#guard` pins that it is non-empty, never what it says. -/
#guard match classDup.parse with
  | .error _ msg _ _ => msg != ""
  | .ok _ => false

end Examples.es.test262
