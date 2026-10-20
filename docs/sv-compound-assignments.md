# Selected compound assignments

IEEE 1800-2023 §10.4.1 and §11.4.1 define an operator assignment as a
blocking read/modify/write with its left-hand address evaluated once. The
legacy self-check surface admits integral `+=`, `-=`, `*=`, `/=`, `%=`,
`&=`, `|=`, `^=`, `<<=`, `>>=`, `<<<=` and `>>>=` over whole variables,
fixed unpacked cells, packed selections and admitted packed members.

The extractor converts the frontend's complete bound RMW expression,
substituting only its one typed `LValueReferenceExpression`. Propagated
operand widths, signed division/remainder, shift signedness, final narrowing
and two-state conversion remain in that tree. For example, a four-bit
destination with a 32-bit RHS computes the 32-bit operation before narrowing.
Previously correct simple scalar envelopes are retained when their complete
expression trees agree, ignoring source spans only.

Dynamic packed addresses are captured in scoped local vectors. Dynamic
unpacked arrays capture both the index and the complete computed result
before the conditional cell stores. Only array labels representable by the
index's width and signedness become branches; truncated labels cannot alias
another cell. An invalid read uses the element type's default, zero for a
two-state element and X for a four-state element. Unknown or wholly invalid
targets perform no store, but still evaluate the RHS. The unknown `$clog2`
RHS fixture checks that evaluation cannot disappear behind an invalid target.

A dynamic selection through a packed member first captures the bounded member
vector, updates that vector, then copies the member back. Adjacent fields
cannot become part of the selected storage merely by adding a parent offset.
The new `CompoundRead` expression uses the existing `selectedRead` helper
after the admission check below; stores still use ordinary `selectedWrite`.
Local storage, blocking execution, delayed continuations, pending NBA work
and output use the existing shared executor and scheduler.

Source effects, concatenated destinations, unsupported types/geometries,
nonblocking or internally timed operator forms, malformed bound RMW trees,
invalid compilations and generated-storage collisions remain loud. A delay
around an otherwise admitted operator statement composes normally. Symbolic
compound extraction is unchanged and remains loud.

Partially out-of-range packed compound selections are an explicit runtime
boundary: `AssignmentExpression:compound-partial-range`. It applies when
the selected interval overlaps storage but is not wholly contained. Reference
observations on two sources left the entire vector unchanged, whereas applying
the ordinary clipped read/write helpers changed the overlapping bits. The
exact sources are retained as `partial_windows.sv` and `partial_members.sv`.
Their reference observations are **not** model agreements. No standard
copyback result is claimed for this disputed case, and ordinary selected
assignment clipping is unchanged. Unknown and wholly disjoint selectors
continue to use the existing no-store behavior.

The paired 22,035-path census gains 13 clean extractions without losses:
4,083 clean, 17,886 partial, 66 include skips and zero extraction errors.
All 13 gains execute completely and match full independent transcripts
under both region oracles. All 4,070 previously clean extracted designs are
identical. These are extraction and selected-execution measurements, including
negative and compile-only inputs, rather than whole-corpus conformance.

Seven authored complete transcripts match both oracles; six also match the
time-zero runner. Four further sources retain effect, unresolved-RHS and
partial-range refusals. Five kernel theorems bind the actual parsed delayed
assignment's capture, RMW read and store: address capture, current selected
value, blocking storage preserving NBA/output, unknown no-store, and partial
range refusal. See the [fixtures and receipts](../Examples/system-verilog/compound_assignments/README.md).
