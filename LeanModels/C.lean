import LeanModels.C.Ast
import LeanModels.C.Json
import LeanModels.C.Load

/-!
# The C lane (`LeanModels.C`)

C as the project's third modeled language, after Python and SystemVerilog.
The charter is `docs/c-tier-charter.md`; the architecture it continues is
`docs/c-tier-architecture.md`.

**Milestone M1 is INGESTION ONLY.** This lane currently contains a type
and a parser: the deep-embedded AST of the `c-0.1` envelope
(`docs/c-envelope-schema.md`), and the ingester that builds it. There is
no interpreter, no memory model and no semantics — those are M2 and
later, and which of the charter's three endgames they serve is the
owner's open choice (`docs/c-tier-charter.md` §3, §5).

Importing this from `LeanModels.lean` is what puts the lane in
`lake build`, and therefore in CI.
-/
