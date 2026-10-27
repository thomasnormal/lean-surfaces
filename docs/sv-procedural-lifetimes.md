# Procedural variable lifetimes

IEEE 1800-2023 §6.21 and §9.3 distinguish a declaration's lifetime from entry
into its block. The concrete frontend's actual bound lifetime determines the
lowering. Static scalar, packed integral and admitted fixed-array declarations
have one store initialized before any process starts, including declarations in
unentered blocks. Their declaration statements become empty; re-entry retains
the current value. Named-block hierarchical reads and writes use the original
bound storage identity. Same-spelled declarations remain distinct.

Closed pure initializers and default values use the existing pre-process
`Var` initialization. A static declaration may read an earlier closed pure
static declaration in the same procedural scope; source order is retained in
the hoisted declarations so the dependency is evaluated after its source.
Runtime reads, environment queries and effects refuse as
`StaticLocal:initializer`; a pre-process initializer outside that scope that
reads procedural storage refuses as `StaticLocal:initializer-order`.
Unsupported types and invalid/redefined source remain loud. The shared
declaration census includes unsupported bodies, so their hidden initializers
cannot silently disappear. Fixed arrays now use this same census rather than
a separate statement-marker hoist.

Actual automatic scalar declarations retain `LocalDecl` entry behavior. Each
fresh sequential block/loop entry evaluates its initializer, while an existing
saved continuation retains its locals across a dependency wait. The existing
loop and scheduler implement that distinction. Automatic hierarchical access,
reentrant subroutine activations, fork lifetimes and symbolic extraction remain
outside this admission. No runtime node, evaluator or scheduler is added.

A qualification probe found a disagreement for an implicit procedural local
inside `module automatic`: the frontend binds it Automatic, but the independent
reference retains its value across repeated entries. The original source is
preserved as `default_lifetime.sv`, with the reference's complete transcript.
`AutomaticLocal:default-lifetime` refuses this semantic context unless the
source states its lifetime explicitly. This is an unresolved disagreement,
not a reference agreement or a claim that either tool has established the rule.
Explicit `automatic` and `static` declarations have separate successful receipts.

The paired **22,035** paths gain **20 clean extractions** and withdraw **35**
prior admissions: **4,341 → 4,326 clean**, **17,628 → 17,643 partial**,
**66 include skips**, zero errors. Twenty-eight withdrawals have nonclosed static
initializers and seven contain invalid source. All nineteen gained
simulation files match complete independent stdout under both tested region
oracles. The other gained compile-warning file has no `$finish`: its reference
quiesces after three zeroes, while the bounded model reaches its horizon.
It is recorded as **HORIZON**, not an agreement or a semantic refusal.

Of the prior 4,341 clean designs, 3,165 are unchanged, 1,141 change and remain
clean, and 35 now refuse. Paired model runs on the 1,141 changed clean designs
have no status or transcript differences: 1,116 finish, 17
refuse and eight require explicit command-line inputs at loading. This is regression
telemetry, not independent conformance evidence for those 1,141 files.

Eight authored programs match complete independent transcripts under both
orders, including before-entry visibility, re-entry, shadowing, hierarchy,
fixed arrays, packed fields, X/Z and two-state defaults, automatic capture across
a wait and NBA capture before a later write. Four authored programs explicitly
refuse default-lifetime provenance, effects, initializer reads and order. All
32 successful final-source reference invocations are bound to exact bytes,
invocation, status, full stdout and provenance. No transcript filtering is used.

Four kernel theorems are checked against the parsed `certificate.sv`: static
pre-process initialization, entry retaining all stores/work, increment reading
the retained value, and modular addition for every four-bit operand. They prove
properties of this actual fixture, not general frontend correctness. See
[the fixtures and receipts](../Examples/system-verilog/static_locals/README.md).
