# Dynamic integral casts

IEEE 1800-2023 §6.24.2 and §20.5 `$cast` is a stateful operation. The legacy
surface admits pure supported integral sources and packed integral or enum
variable destinations. It samples the source once, performs destination-width
assignment conversion using the source's signedness, and applies destination
two-state conversion. An enum then checks exact four-state membership in its
bound declaration table. Named X/Z values can succeed; conversion precedes
membership, including truncation and two-state squashing. A non-enum integral
destination accepts every admitted converted value.

Function form returns a signed 32-bit known zero or one. Success stores the
converted value; failure leaves the destination unchanged. Existing stores
handle whole variables, packed members/windows and fixed unpacked cells.
Dynamic fixed-cell selection dispatches only to positions representable by
the selector's width and signedness; an out-of-range selector writes no cell.
The successful conversion still returns one for such a destination.

The existing plusargs expression sequencer is shared with casts. It emits
ordinary local captures, comparisons, conditional statements and stores.
Calls remain at their source control boundary. Logical operands retain IEEE
short circuiting, including evaluating the right operand when the left is
unknown. Unordered operands with conflicting reads/writes refuse. The
ordinary timed continuation retains these statements and their captures;
no evaluator or scheduler is added. Generated `$cast:` storage is audited
against source and other local bindings. Old plusargs lowering is preserved.

Task form uses the same success rule. An invalid task-form conversion reaches
`DynamicCast:task-diagnostic`: the required runtime diagnostic has no shared
observation contract yet. It is not silently dropped or replaced by a return
code. A source with that branch can execute successfully without visiting it,
while still being partial in the extraction census.

Real/string/class conversions, effectful sources or selectors, unsupported
storage, ternary and other unhandled expression effect contexts, static
initializer effects, and symbolic mode remain loud. Frontend-invalid sources
containing a lowered cast retain a whole-design barrier. Existing timing and
procedural-publication boundaries still apply. This is the integral cast
rung; it does not supply class-handle casting or a diagnostic subsystem.


The paired **22,035** paths gain **13 clean extractions**, no losses:
**4,296 → 4,309 clean**, **17,673 → 17,660 partial**, **66 include skips**,
zero errors. All 4,296 previously clean extracted designs remain identical.
Twelve gains match complete independent transcripts under both region oracles;
one retains the existing timed `$time` refusal. Six authored sources match
both orders, and four retain explicit boundaries. The invalid task reference
produces a runtime diagnostic and status one; it is not an agreement. Final
source/status/transcript/provenance authentication covers 22 successful
independent invocations plus that one diagnostic invocation. Six kernel
theorems bind the actual parsed source capture, membership guard and success
body. Extraction is distinct from whole-corpus runtime conformance.
