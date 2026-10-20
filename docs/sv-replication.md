# Integral replication

IEEE 1800-2023 §11.4.12.1 replication repeats a self-determined concatenation
group in source order. The legacy `sv-0.1` extractor lowers a nonnegative
constant count and pure integral group to the existing `Concat` expression.
Each operand retains its width and four-state bits. The result is unsigned;
assignment resizing applies to the complete result afterward. Nested groups,
byte-string literals and elaborated parameter counts use the same rule.
Existing symbolic `sv-0.2` replication stays symbolic.

A legal zero-count member lowers to an empty width-zero concatenation inside
a positive-width enclosing concatenation. Its source operands are checked
even though they contribute no bits. Effects remain loud at every count:
the source evaluates an effectful group once, including at count zero, while
copying or dropping its expression would change that behavior. Unsupported
pure operands also remain visible. Dynamic strings, nonintegral groups,
unknown/negative/nonconstant counts, malformed geometry, standalone zeros,
frontend errors and declaration-redefinition conflicts remain loud.
Expansion is bounded to 1,024 copies and 16,384 copied expression nodes per
replication; exceeding either limit refuses without truncation.

The result uses the ordinary vector evaluator, live storage, whole-RHS
assignment, captured NBA and delayed-continuation rules. Replication composes
with admitted patterns, cases and fixed-array cells. No value primitive or
scheduler is added.

The first independent comparison exposed an existing IEEE §5.7.1 issue:
the frontend zero-extends a wide conversion of an unsized based literal
whose leading digit is X/Z. The extractor now fills the wider context from
that digit before enclosing constant folding, including explicit size casts.
Sized literals and ordinary unsigned variables retain zero-fill, and the
existing two-state conversion still clears X/Z. Parameters, enum values and
generate expressions already evaluated with this frontend error refuse as
`UnsizedBasedLiteral:constant-context`; their elaboration cannot be repaired
by runtime conversion. Constant selectors also refuse the affected bound
constant. Symbolic extraction is unchanged.

The paired 22,035-path census gains 20 clean extractions without losses:
4,057 clean, 17,912 partial, 66 include skips and zero extraction errors.
All 20 new clean files execute to completion and match complete independent
transcripts under both region oracles. The initial widening mismatch now
prints `PASS`. All 4,037 previously clean extracted designs remain identical.
The census includes negative and compile-only sources and measures extraction.

Seven authored sources match complete independent transcripts under both
oracles; six also match the time-zero runner. Three further sources preserve
effect, dynamic-string and elaboration-constant refusals. Five source-bound
kernel proofs certify current replicated reads, blocking stores, NBA capture,
visibility after source changes and zero-member identity. The fixture receipt
checks the actual parsed statements and complete observations.
