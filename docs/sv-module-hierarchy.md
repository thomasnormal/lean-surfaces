# Static module hierarchy

IEEE 1800-2023 clauses 23 and 27 elaborate module instances before execution.
The legacy `sv-0.1` surface now traverses concrete portless module instances,
including parameter overrides, nested generate scopes and static instance
arrays. This is the first module-hierarchy rung; connected ports, interface
instances and program instances remain explicit boundaries.
The connected-port census and repricing decision are recorded separately in
[Connected child ports](sv-hierarchy-ports.md).
Program and interface instances have their own [hierarchy-kind boundary](sv-hierarchy-kinds.md).

The extractor walks each actual `InstanceSymbol.body`, rather than its shared
`canonicalBody`. Siblings with identical parameter configurations can share a
frontend template while retaining different variables and procedural locals.
Before converting any expression, the extractor registers all declarations in
the supported top tree by bound symbol identity. Parent, child, sibling and
upward statically resolved references therefore name their original slot,
regardless of source declaration order. Per-instance integral parameters and
genvars retain the frontend's exact width, signedness and four-state value.

Instance storage uses length-prefixed structural scope routes and declaration
locations under `$hierarchy:`. Routes include member ordinals and array-element
positions; they are not parsed from hierarchical name strings. Generate scopes
within an instance retain that instance's route. Dynamic local captures use
the same current scope, and collision checks cover module declarations and
procedural locals. Fixed unpacked cells and packed selections/members reuse
the existing read, capture and store rules. Pure packed-member reads also
compose with the selected-store admission check; this corrects an existing
purity over-refusal without changing their evaluation.

Flattened declarations and processes carry `instance_scope`; the enclosing
module carries `hierarchy_lowered`. Package imports continue referring to the
one original package slot; instantiating a module does not instantiate another
copy of package storage. The emitter preserves traversal order, and ordinary
execution, delays, retained continuations, edge waits and NBA work use the
existing shared executor and region oracles. No scheduler is introduced.

Every active unsupported child member remains visible. Child modules with any
declared ports refuse as `Hierarchy:ports`, even when unconnected: input/output
conversion, net aliasing and continuous propagation require the connected-port
rung. Program/interface instances refuse as `Hierarchy:module-kind`; their
process-region or interface behavior is not guessed. A child whose timescale
differs from its top refuses as `Hierarchy:timescale`; raw local delay units
are never silently identified. Instance expansion is bounded at 1,024 child
instances per top and 64 instance/array nesting levels. An over-budget
expansion retains a refusal rather than admitting its partial prefix. Empty/invalid arrays, frontend errors and
redefinitions also remain loud.

Closed static initializers are admitted. New reads whose initialization order
would depend on flattened storage retain the existing
`Generate:initializer-order` boundary. The current loader still requires one
top module. Symbolic extraction keeps its instance boundary: an instance there
is one `Instance` node plus the child's definition, flattened by the Lean side
(`docs/sv-envelope-schema.md`, "Module instances", 2026-10-28).

The independently referenced authored fixtures exercise sibling isolation,
live cross-instance reads/stores, NBA capture across later source changes,
upward references, nested generate scopes, negative/descending instance-array
bounds, per-instance widths and type queries, delayed procedural locals,
shared package storage, fixed arrays and packed members. Separate sources
retain port, program-kind, initializer-order and timescale refusals. Their
reference success is not model agreement. The reference compiler rejected an
initial multidimensional instance-array experiment; that exact source and
failed receipt are retained as evidence, and no execution agreement is claimed
for that experiment. The structural array walker handles nested frontend
arrays, tested for distinct declaration binding without a runtime value claim.

Five kernel theorems bind the actual parsed declarations and blocking/NBA
statements in `isolation.sv`: live reads, blocking storage preserving prior
work/output, sibling preservation, NBA capture and capture stability after a
later source change. They prove properties of the selected parsed program,
not a general correctness theorem for frontend elaboration. See the
[fixtures and receipts](../Examples/system-verilog/module_hierarchy/README.md).

The paired 22,035-path census gains 198 clean extractions with no losses:
4,296 clean, 17,673 partial, 66 include skips and zero extraction errors.
All 4,098 previously clean designs remain identical. Extraction is distinct
from runtime conformance. Of the gains, 175 match complete reference
transcripts under both region oracles, nine match one tested order, eleven
retain runtime refusals, two hit reference-compiler limitations and one has
multiple tops without a usable single-top oracle. All 207 successful
independent invocations and both compiler refusals were authenticated against
final source bytes, top, arguments, status, transcript and available
provenance. The eight runnable authored/prior fixtures match both orders;
the four explicit boundaries refuse. No successful reference transcript is
outside both tested model traces.

The nine order-sensitive corpus rows are:

| Corpus source | Difference between tested orders |
|---|---|
| `chapter-22/22.10--v3-celldefine-anywhere-in-description.sv` | Top finishes before child output |
| `chapter-22/22.2--v3-directive-scope-across-compilation-unit.sv` | Top finishes before child output |
| `chapter-22/22.5.1--v3-define-used-across-modules.sv` | Top finishes before child outputs |
| `chapter-23/23.6--hier-name-array-of-instances-v3.sv` | Parent and child initial blocks race on element writes |
| `chapter-26/26.3--explicit-import-same-pkg-from-two-locations-allowed.sv` | Independent same-tick child outputs reverse |
| `chapter-26/26.3--import-not-copy-visible-only-in-importing-scope.sv` | Top finishes before child output |
| `chapter-26/26.7--compilation-unit-import.sv` | Top finishes before child output |
| `chapter-5/5.12--attribute-on-module-instantiation-v2.sv` | Top finishes before child output |
| `chapter-5/5.12--attribute-on-module-instantiation.sv` | Top finishes before child output |

The two reference limitations are
`chapter-23/23.4--nested-module-implicit-instantiation.sv` and
`chapter-23/23.4--nested-module-outer-namespace-visible.sv` (nested module
compilation is unimplemented). The no-oracle source is
`chapter-23/23.8--upward-ref-module-c-writes-module-b-variable.sv`, whose two
tops also retain the loader's single-module refusal. These rows do not count
as execution agreements.
