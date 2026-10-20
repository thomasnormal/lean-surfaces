# Integral assignment patterns

IEEE 1800-2023 §10.9 assignment patterns use their destination or explicit
pattern type to determine element correspondence and conversion. The legacy
`sv-0.1` extractor now lowers positional, keyed/member/type/default and
constant-replicated patterns for its existing integral storage inventory:
predefined integers, packed scalar vectors and untagged packed structs.
Nested struct patterns use the same recursive conversion. A typed pattern
keeps its elaborated type inside conditionals, casts and other expressions.

The bound frontend inventory is checked against the target geometry before
packing. Struct fields use declaration order, most significant first.
Positional arrays retain declared left-to-right order. Structured array and
integer inventories enumerate increasing numeric indices in this frontend;
these are reversed for descending declarations before packing. This mapping
also corrects the existing fixed-unpacked-cell declaration, whole-assignment,
slice and pattern-target paths, including the symbolic cell initializer path.
Symbolic packed-pattern admission is unchanged.

Every element retains its bound width and conversion. Ordinary concatenation
packs the bits, including X/Z; existing sign propagation, resizing and
two-state conversion apply. The expression reads live storage, without a
constant snapshot. A whole packed assignment evaluates the complete RHS
before its one store, so a packed struct can swap its own fields. Captured
NBA values and delayed continuations use the existing execution rules. No
storage primitive, evaluator or scheduler is added.

Only pure source operands are admitted. Effectful calls, assignments and
increments remain loud even if a frontend constant could otherwise erase
them. Unsupported elements never disappear into a guessed constant. A lowered
pattern design with frontend errors or declaration-redefinition conflicts is
refused. Invalid correspondence and expansions over 1,024 elements per pattern
are loud. Unpacked value results, union/tagged patterns, existing unsupported
multidimensional packed storage and all existing expression/storage boundaries
remain loud. Split-cell unpacked assignments retain their self-read refusal:
they need a separate complete-RHS capture contract before writes may alias
later reads. Ordinary replication expressions are a separate construct.

The paired 22,035-path census gains 26 clean extractions without losses:
4,037 clean, 17,932 partial, 66 include skips and zero extraction errors.
Twenty-four gains match complete independent transcripts under both region
oracles. Two retain continuous-assignment runtime refusals. All 26 independent
runs succeed; no remaining transcript difference, oracle failure or multi-top
absence occurs. All 69 previously clean corpus sources containing pattern
syntax retain identical extracted designs under a paired before/after check.
The census includes negative and compile-only sources and measures extraction.

Five authored sources match complete independent transcripts under both
oracles; four also match the time-zero runner. They cover integer bit keys,
both array directions, member/type/default priority, nested and signed
structs, two-state conversion, live self-swaps, replicated groups, fixed
arrays of packed structs, and NBA value capture. Three further sources
preserve effect, multidimensional-storage and unpacked self-alias boundaries.
Four source-bound kernel proofs certify the real keyed RHS's current-value
read, blocking store, NBA capture, and visibility after the source changes.
