# Runtime integral `$clog2`

IEEE 1800-2023 §20.8.1 treats the argument as an unsigned value, including
when its source type is signed. Zero and one return zero; other fully known
values return the ceiling of their base-two logarithm. The result is a signed
32-bit integer. The argument keeps its own bound width; the assignment context
converts the complete result afterward.

The legacy `sv-0.1` extractor retains correct frontend-bound constant literals
and emits `Clog2` for a pure integral call that requires evaluation. The
self-check expression evaluator evaluates its operand once and calls the
existing `LeanModels.Sv.clog2` numeric helper from `Param.lean`. Both constant
parameter mathematics and runtime value mathematics share that definition.
No scheduler or storage primitive is added. Symbolic extraction is unchanged.

Live variables, signed finite-width bit patterns, wide vectors, nested calls,
loops, cases, patterns, replication and fixed cells compose through the
existing expression rules. The source purity audit precedes folding. Effects,
nonintegral or unsupported operands, malformed signatures, invalid compilation
and declaration-redefinition conflicts remain loud. Unevaluated `$bits`
arguments remain type queries and do not invoke the numeric function.

Unknown numeric operands remain an explicit runtime refusal. Independent
observations found that the reference maps an eight-bit all-X operand to 8
and all-Z to 0, while the frontend folds both to zero. A mixed `1x000000`
argument also disagrees between those tools. This tier claims no numeric
answer for X/Z inputs. Enclosing folds cannot erase the runtime call, and
zero-count replication cannot discard an unresolved call. A parameter, enum
or generate expression whose numeric argument is unresolved refuses at
admission as `$clog2:constant-context`; an affected constant selector also
refuses, preventing use of an approximate bound elaboration result.

The paired 22,035-path census gains 13 clean extractions without losses:
4,070 clean, 17,899 partial, 66 include skips and zero extraction errors.
All 13 gains execute to completion and match complete independent transcripts
under both region oracles. All 4,057 previously clean extracted designs remain
identical. These counts measure extraction, including negative/compile-only
sources, rather than whole-corpus execution conformance.

Four authored sources match complete independent transcripts under both
oracles; three also match the time-zero runner. Four further sources preserve
runtime unknown, constant unknown, elaboration unknown and effect refusals.
Five kernel proofs certify the real parsed runtime RHS and assignments:
current unsigned reads, blocking storage, NBA capture, visibility after source
changes, and refusal before inventing a numeric result for unknown input.
