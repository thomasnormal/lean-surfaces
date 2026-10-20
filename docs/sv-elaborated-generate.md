# Elaborated generate scopes

IEEE 1800-2023 clauses 6, 23 and 27 distinguish elaboration from runtime
execution. The legacy `sv-0.1` frontend already elaborates its module types
and widths. It now traverses live unconditional, conditional and case-generate
blocks and every elaborated loop entry. Inactive branches and zero-count loops
contribute no runtime declarations or processes. Every active unsupported
member remains visible as a refusal, including elaboration-severity tasks.
This does not execute a generate loop at simulation time.

Live generated variables, nets and procedural locals use injective storage
names based on the top module, structural scope route and original declaration.
The route records member ordinals, labels and loop-entry indices; identifiers
are length-prefixed, rather than parsed as hierarchical paths. Bound symbol
identity selects the original slot for ordinary and statically bound
hierarchical reads and stores. Same-named siblings, nested scopes and repeated
source declarations remain distinct. Fixed arrays reuse existing cell storage
with those distinct base names. Temporary intra-assignment captures and foreach
cursors/iterators also carry their generated scope. All generated names are
audited against user bindings before execution.

Integral module/local parameters and implicit per-entry genvar localparams
become exact typed vector literals, preserving width, signedness and X/Z bits.
Source genvar declarations allocate no runtime storage. Nonintegral and type
parameters stay loud. The legacy model consumes the concrete elaborated
configuration; the separate symbolic extractor continues retaining symbolic
parameters and generate forms, without this flattening.

Declarations and processes retain their traversal order and use the existing
vector store, expression evaluator, continuations, NBA capture/commit and
region oracles. No scheduler is added. Runtime reads in generated static
initializers, or new module initializer reads of generated storage, require an
initialization-order oracle and remain `Generate:initializer-order`. Closed
parameter/genvar initialization is admitted. Existing expression, array,
lifetime, timing and process boundaries still apply. Cross-instance hierarchy,
ports/connections and unresolved names are not flattened into guessed aliases.
The current runner still requires exactly one top module.

Frontend errors and redefinition conflicts in a lowered design prevent
execution. Expansion over 1,024 entries in an individual generate loop refuses
without emitting a partial prefix. Unsupported active members, types and
initializers stay loud. Each declaration/process emitted from a generate scope
retains `generated_scope` provenance; the module and folded parameter or
hierarchical-reference nodes carry `elaboration_lowered`.

Seven authored runnable sources match complete independent four-state
transcripts under both region oracles. They exercise if/else/case/unconditional
and nested scopes, zero-count and ascending/descending loops, exact parameters,
four-state choices, qualified reads/stores, packed/fixed-array storage, scoped
imports, repeated locals and delayed captures/NBAs. Three further sources
preserve unsupported-member, cross-instance and static-initialization boundaries.
The source-bound kernel proofs certify current reads, separation of nested
same-named storage, and the selected branch's real blocking assignment.

The paired 22,035-path census gains 345 clean extractions without losses:
4,011 clean, 17,958 partial and 66 include skips, with zero extraction errors.
Of those gains, 187 match complete independent transcripts under both oracles;
three show legal time-zero process races, with one matching oracle each.
Another 146 retain existing runtime boundaries: 112 continuous assignments,
33 procedural edge-publication cases and one time-zero-only clock. Four
multiple-top designs retain loader refusals. Five independent compiler
refusals cover four constant system-function contexts and one reset-protection
pragma; they establish no execution agreement. No remaining row differs from
both oracle traces. The chapter table measures extraction coverage, including
negative and compile-only sources, rather than whole-corpus execution.
