import LeanModels.Ada.Ast
import LeanModels.Ada.Json
import LeanModels.Ada.Load
import LeanModels.Ada.Ada2012.Value

/-!
# The Ada lane (`LeanModels.Ada`)

Ada as the project's fourth modeled language. The charter is
`docs/ada-charter.md`; the envelope it ingests is
`docs/ada-envelope-schema.md`.

**M1 (ingestion) is complete. M2 has begun** — `docs/ada-semantics-design.md`
is the plan and `LeanModels/Ada/Ada2012/Value.lean` is its inch 1. There is
still no interpreter.

`Ada2012/` is imported from here for one reason worth stating, because it was
learned the expensive way: a module no module imports is **never elaborated**,
so a build that is green says nothing about it. Inch 1's first tenure was
green while its own file had never been compiled.

## Placement: `Ast`/`Json`/`Load` are TRUNK, and the reason is structural

`docs/family-architecture.md` §1.1 splits a lane into a version-NEUTRAL
trunk and version-SCOPED editions, and §1.3 requires the boundary to be a
claim with an instrument behind it. Ada declares **two** edition tokens at
founding — `Ada2022` (the ARM) and `Ada2012` (ACATS 4.2) — because the
version pair is FORCED, not chosen (`docs/ada-charter.md` §1.3). So the
directory level exists from commit one and the only question is what sits
above it.

These three files sit in the trunk, on the C lane's precedent
(`Ast`/`Json`/`Load` stayed at `LeanModels/C/`; only `Value` moved to
`C23/`) and on evidence of two kinds:

1. **Structural, and it is the decisive one.** `Node` carries
   `kind : String`, not one constructor per node kind
   (`LeanModels/Ada/Ast.lean`, module docstring). The type therefore
   **cannot** be edition-sensitive: Ada 2022's `ParallelLoopStmt` adds a
   string to a census file, not a constructor to an inductive. Where the C
   lane had to measure that none of its 45 kinds was post-C99, this lane
   has nothing to measure — the sensitivity is absent by construction.
2. **Corroborating, and it corrected a guess.** The census
   (`docs/ada-construct-census.json`, 280 kinds over 2,976,861 nodes)
   contains no Ada-2022-only construct, which follows from the corpus being
   ACATS 4.2 — an Ada 2012 suite by its own `ACATS_Version` constant. Three
   kinds were flagged as suspects and **all three were cleared by
   measurement rather than by argument**: `IterTypeOf` is Ada 2012's
   `for ... of`, and `ConcatOp`/`ConcatOperand` are libadalang's
   representation of `&` chains, which is Ada 83. Parsing a file containing
   both produced exactly those kinds with zero diagnostics.

**What will be version-scoped is MEANING**, which is where the C lane's
boundary fell too: Legality Rules, Dynamic Semantics, and the bounded-error
and erroneous-execution classes (`docs/ada-charter.md` §1.5). The ARM
measures 953 Legality-Rule paragraphs against 572 Syntax paragraphs, and it
is the first number that differs between editions, not the second.

## What the lane is scored against

`docs/ada-charter.md` §6: Thomas ruled BOTH the spec ladder — ARM-paragraph
coverage, denominator 14,262 — and differential grounding against GNAT. The
scoreboard is a **trace emitter**: verdicts come from the ACAA's own `GRADE`
tool, not from us (§4.4).

Importing this from `LeanModels.lean` is what would put the lane in
`lake build`. It is deliberately NOT imported there: `Examples/ada/**`
imports `LeanModels.Ada` directly and the `Examples.+` glob pulls the lane
into the build and into CI anyway, so the import would only couple the Ada
lane into every other lane's import graph — the measurement the C lane made
and acted on (`docs/c-tier-charter.md` §4.8).
-/
