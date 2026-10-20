# Command-line plusargs

The self-check loader admits IEEE 1800-2023 §21.6 queries with an explicit
immutable input environment:

```lean
loadEnvelopeDesignWithPlusargs ["COUNT=7", "COUNT=9", "MASK=10xz"] envelope
```

Each list element is a plusarg's content after removing its command-line
`+`. Order and duplicates are preserved. An explicit `[]` represents no
plusargs. `loadEnvelopeDesign` refuses input-dependent envelopes because it
has no supplied environment. Extraction never reads the host's arguments.
The existing conformance runner uses that ordinary loader; callers testing
plusargs must use the explicit API and supply the source's invocation metadata.

`$test$plusargs` accepts a literal ASCII query. Matching compares the whole
query against a case-sensitive prefix of each input. `$value$plusargs`
accepts a literal prefix followed by one final `%b`, `%o`, `%d`, `%h` or `%x`;
uppercase and leading-zero forms are admitted. The first matching input wins.
An absent match returns zero and leaves its destination untouched.

The admitted numeric suffix is consumed completely. Decimal conversion
supports a leading sign and digit separators. Based conversion supports
separators, known digits, and binary x/z digits following a known leading
digit. Results truncate or pad to the packed destination width. Existing
packed assignments handle selected writes and two-state conversion, retaining
neighboring bits. There is no scanner-prefix shortcut.

Stateful calls are admitted in blocking-assignment values and `if` conditions
through integral unary operators and binary expressions. Logical operands
preserve short circuiting: save the left value, execute the right prelude only
when needed, then combine their saved values. An unknown left value requires
the right operand. Copyback precedes subsequent reads in that operand.
Nonlogical operands with conflicting reads and writes stay loud because
their source evaluation order is unspecified. Generated temporary names have
a module-wide collision audit.

The loader specializes immutable input queries to existing expressions and
statements. Calls keep their source control placement, and repeated calls
still perform their destination writes at each visit. The timed stepper
retains the same statement continuation across a wait. No evaluator,
assignment primitive or scheduler is added.

Dynamic query/format strings, string and real destinations, other format
syntax, effectful selectors, ternary effect contexts, loop-header effects,
nonblocking effect contexts and symbolic-mode queries remain loud. Numeric
whitespace, empty suffixes, decimal unknowns, leading binary unknowns,
question marks, octal/hex unknown digits and malformed values also remain
loud. Independent runs produced diagnostics for several of those numeric
corners; an invented all-x result would lose those observations. Unsupported
inputs can refuse at loading even when their source call would not be visited.

The examples in `Examples/system-verilog/plusargs` record complete independent
transcripts, explicit invocation inputs and fixture-bound kernel theorems.
The diagnostic example records a refusal, not runtime agreement. A separate
corpus timing example remains blocked by the existing time-zero-only `$time`
contract; this family does not extend the clock-query surface.
