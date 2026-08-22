import LeanModels.Es.Ast
import LeanModels.Es.Json
import LeanModels.Es.Load

/-!
# The ECMAScript lane (`LeanModels.Es`)

ECMAScript as the project's fourth modeled language, after Python,
SystemVerilog and C. The charter is `docs/es-charter.md`; the family row
it ratifies is `docs/family-architecture.md` §1.2.

**M1 (ingestion) only.** The lane contains the deep-embedded AST of the
`es-0.1` envelope (`docs/es-envelope-schema.md`) and the ingester that
builds it. There is no evaluator, no completion record, no realm and no
world — those are M2, and the goal they will be scored against is
test262, whose tests pass by NOT throwing.

The tier's authority is dual and the distinction is load-bearing:
SPEC-MIRROR against ECMA-262 (edition `ES2026`, pinned at the
`es2026-errata` revision by `docs/es-edition.json`) and OFFICIAL-SUITE
against test262. There is no reference implementation of ECMAScript, so
an engine is a cross-check and never the authority — `docs/es-charter.md`
§4.3.
-/
