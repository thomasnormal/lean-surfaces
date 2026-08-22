import LeanModels.C.Ast
import LeanModels.C.Json
import LeanModels.C.Load
import LeanModels.C.C23

/-!
# The C lane (`LeanModels.C`)

C as the project's third modeled language, after Python and SystemVerilog.
The charter is `docs/c-tier-charter.md`; the architecture it continues is
`docs/c-tier-architecture.md`.

**M1 (ingestion) is complete; M2 has begun.**

The lane is split by LANGUAGE VERSION, because `lean-surfaces` is a
family of versioned surfaces and a user proving about C chooses which C:

* **`LeanModels.C`** — the version-neutral substrate. The deep-embedded
  AST of the `c-0.1` envelope (`docs/c-envelope-schema.md`), the JSON
  reader, and `load_c_program`. An ingested translation unit is the same
  term whichever version you go on to reason about.
* **`LeanModels.C.C23`** — the ISO/IEC 9899:2024 surface, mirroring
  N3220 clause by clause. Everything that assigns MEANING lives here;
  `LeanModels/C/C23.lean` records the measured C17↔C23 differences that
  make the boundary a directory rather than a flag.

The plan for the rest is `docs/c-semantics-design.md`; the goal it is
scored against is `docs/c23-goal.md` (Thomas ruled option (c) — the C23
completeness ladder, measured against real test suites).

Importing this from `LeanModels.lean` is what puts the lane in
`lake build`, and therefore in CI.
-/
