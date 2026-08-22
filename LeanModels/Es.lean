import LeanModels.Es.Ast
import LeanModels.Es.Json
import LeanModels.Es.Load
import LeanModels.Es.Value
import LeanModels.Es.Completion
import LeanModels.Es.Object
import LeanModels.Es.Ordinary
import LeanModels.Es.Env
import LeanModels.Es.Function
import LeanModels.Es.Convert
import LeanModels.Es.Eval
import LeanModels.Es.SpecAttr
import LeanModels.Es.Spec

/-!
# The ECMAScript lane (`LeanModels.Es`)

ECMAScript as the project's fourth modeled language, after Python,
SystemVerilog and C. The charter is `docs/es-charter.md`; the family row
it ratifies is `docs/family-architecture.md` §1.2.

**M1 (ingestion) is complete; M2 has begun.** The lane contains the
deep-embedded AST of the `es-0.1` envelope
(`docs/es-envelope-schema.md`), the ingester that builds it, and — as M2's
first inch — the VALUE model (`Value.lean`: the eight language types and
the conversions that cannot throw), COMPLETION RECORDS on the family's
substrate shape (`Completion.lean`: `Abrupt` in `ρ`, all four types), and
the `@[es_spec]` registry with arm-level lemmas (`Spec.lean`).

There is still no evaluator, no realm and no world. The plan for those is
`docs/es-semantics-design.md`; the goal they will be scored against is
test262, whose tests pass by NOT throwing — which is why that document's
§5.2 makes liveness a load-bearing field of the scoreboard.

The tier's authority is dual and the distinction is load-bearing:
SPEC-MIRROR against ECMA-262 (edition `ES2026`, pinned at the
`es2026-errata` revision by `docs/es-edition.json`) and OFFICIAL-SUITE
against test262. There is no reference implementation of ECMAScript, so
an engine is a cross-check and never the authority — `docs/es-charter.md`
§4.3.
-/
