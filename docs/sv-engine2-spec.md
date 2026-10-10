# Engine 2 kernel specification: contract census and schema

**Status: partial pure schema, 2026-10-09; regions, normalized time, process
identity/lifecycle, wait registrations and scheduled events landed, no
transition semantics or implementation proof.**
This document starts from lane `ls-spec`'s contract census and tracks the schema
as it lands one piece at a time. It identifies the existing SystemVerilog
scheduler surface and the additional Engine 2 contract. It is not yet a complete
normative executable kernel specification.
The eventual Lean relation, not a description of C++ queue mechanics, will be
the normative core and the source of kernelbench's mandated-order checker.

## 1. Authorities and scope

The language reference is IEEE 1800-2023, principally clauses 4, 6.3.1, 9.3,
9.4, 9.6, 9.7, 10.4.2 and 15.5. This document paraphrases obligations and names
clauses; it does not reproduce standard text. Language requirements, image
admission restrictions and implementation policies are different categories.
An ABI restriction must never become a claimed SystemVerilog law.

The read-only implementation references are in `/var/tmp/thomas-ahle/mox`:

- `lib/Runtime/Engine2/README.md`: the consumed runtime contract.
- `include/mox/Runtime/Engine2ABI.h`: the C declarations and layout authority.
- `lib/Runtime/Engine2/Kernel.h` and `Run.cpp`: implementation evidence, not
  substitutes for a language rule.
- `/var/tmp/thomas-ahle/fleet2/journals/engine2-decisions.md`: decisions and
  measurements, including proposals whose implementation must be checked.

The census inspected lean-surfaces revision
`e56576960a2bf04cd12ba51692173e500877e520` and Mox revision
`033defd2db471dec0ee166fe5d6619238aaf64c9`. At that Mox revision the generated
contract records image ABI 19 and kernel snapshot format 18. These identify
the inspected artifact; they are not constants to duplicate in Lean. Later
decision-log entries discuss removing unused ABI entries and moving condition
waits into the consumer. Those entries do not establish that the inspected
README/header already implement the proposed surface.

The scope is the kernel's pure state, transition relation and traces, with
consumer process-body semantics supplied explicitly. LLVM, fibers, native
pointers, intrusive lists, allocators and calendar data structures are not
semantic state. Source lowering, image admission and ABI refinement remain
separate obligations. Neither a hand-emitted image test nor a kernel theorem
proves that a source construct is admitted by `engine2-compiled`.

## 2. What the existing scheduler actually states

The design reference is [the R1 scheduler census](sv-r1-scheduler.md). Its landed
surface is smaller than its planned full scheduler:

| Existing file | Landed statement or mechanism | Boundary |
| --- | --- | --- |
| `LeanModels/Sv/Regions.lean` | `Region`, `RegionOracle`, `Slot`, `RegionTrace`, `CycleView`, `cycleOf` | Fifteen region constructors; oracle permutes one ready-process snapshot |
| `LeanModels/Sv/World.lean` | `SvWorld`, `ProcState`, `ProcStatus`, `SvM` | Residual-list processes; time, region queues, NBA/Re-NBA buffers and a future-process list |
| `LeanModels/Sv/Step.lean` | `Trigger`, `StepOutcome`, `stepSStmt`, `stepSStmts` | One body runs until completion or syntactic suspension |
| `LeanModels/Sv/Slot.lean` | `runProcOnce`, `stepRegion`, `wakeEdges`, `slotStep` | Active/Inactive/NBA only; queue drained before its selected snapshot runs |
| `LeanModels/Sv/Prim.lean` | Signal, output and NBA primitives | NBA writes append and commit by ordered fold |
| `LeanModels/Sv/Drive.lean` | `runSlots` and slot snapshots | One slot per supplied stimulus entry, not a calendar-driven run |
| `LeanModels/Sv/Adequacy.lean` | `CycleAdequacy` and concrete checks | An adequacy predicate, not a general proved transfer of the old estate |

The reusable commitments are important:

1. Four-state values are values (`Logic`/`LVec`), not exceptions or refusals.
2. Scheduling choice is an external parameter with a legality proof. Region
   ordering and sequential statement ordering are not oracle choices.
3. Suspension stores continuation data. The existing AST residual is one
   possible consumer representation, not a requirement that a kernel interpret
   SystemVerilog statements.
4. `stepSStmt_done_agrees` and `stepSStmts_done_agrees` prove that a completed
   stepped body agrees with its existing non-suspending executor.
5. Region iteration is real: Active work is exhausted before Inactive/NBA;
   newly produced Active work causes re-entry, not a single forward pass.
6. `Slot` records sampled and final signal states; `cycleOf` preserves the
   existing coarse observation surface.

### 2.1 Gaps found by reading the definitions

**Region census correction.** The existing type and document say fifteen
regions, nine core and six PLI. The inspected Engine 2 enum has seventeen,
including `PreObserved` and `PrePostponed`, neither present in `Region`.
The inherited claim of a complete region set must not be carried into this
specification. The next region-schema item must resolve the clause-4 mapping
and add the missing points with checked ordering, not merely copy ABI ordinals.

Other gaps are observable, not cosmetic:

- `slotStep` does not execute or reject nonempty queues in the other regions.
  Its three-queue exhaustion is not whole-kernel completion.
- A time trigger records a relative amount, but `runProcOnce` does not register
  a calendar wakeup or route zero delay into Inactive/Re-Inactive.
- `waitCond` always suspends in the stepper. It does not implement immediate
  success of an already-true condition or dependency-driven reevaluation.
- The driver calls `wakeEdges` for external stimulus. Internal blocking writes
  and NBA commits do not themselves publish those wakeups.
- `ProcStatus` has ready/suspended/finished only. There is no explicit running,
  killed, deferred-child or process-control suspension state, durable
  registration identity, fork group or named-event occurrence state.
- `NbaQueue` stores only signal name and value. It has no origin process,
  statement sequence, event identity, target time or cancellation provenance.
- `Out.halted` and the state-preserving `Finish` layer are not one Engine 2
  completion authority, and neither models embedded-run exhaustion/reopening.

These are not claims that the current tier answers all such programs wrongly:
admission and loud refusals still matter. They are missing obligations before
this surface can specify the Engine 2 kernel.

## 3. What the inspected Engine 2 contract adds

### 3.1 Resume bodies and process identity

Image bodies have the common `void(Engine2Ctx *)` form. Callback versus fiber
kind is certified in a descriptor, not guessed from source names. The pure
specification will replace a native thunk with a consumer-supplied resumable
body transition over explicit frame data.

The settled resume-thunk contract re-enters the body at its entry on every
resume. When a wait blocks, its hook marks the process waiting and returns;
no native stack survives suspension. The consumer must save its resume
position and live values, return to the scheduler after actual suspension,
and restore them on re-entry. Already-satisfied waits may continue inline.
`stackClass` is a retained layout field without kernel meaning, not a promise
of a stackful pool. This clarifies stale fiber-pool wording in the header.

Image fibers start in Active. Returning while still running without
suspension, halt or explicit finish is refused; those exits are distinct. A
dynamic fork child may return naturally, completing that child and releasing
its deferred descendants. Fixed-sensitivity callbacks are armed before startup,
do not execute their body at time zero, and rearm after an activation. These
restrictions describe the inspected image contract, not all SV process kinds.

A scheduler slot is not durable identity. Registration incarnations distinguish
historical finished/killed processes from a new occupant of a recycled slot.
Fork lineage, wait ownership and process-class handles must refer to the
registration identity. Opaque attachments are not automatic-variable storage.

### 3.2 Completion and time

The contract assigns completion solely to `Kernel::finished()`: an explicit
finish request, or initialized region/calendar exhaustion outside a drain.
Sensitized processes need not terminate for exhaustion to hold. An external
publication may reopen a naturally exhausted embedded run; a sticky explicit
finish is different and cannot be cleared by registration.

`engine2_halt` terminates only the current process. `engine2_terminate` latches
global finish and the first supplied status. Natural exhaustion reports zero
without latching a request. Queued delayed updates survive the last process's
halt. An existing finish request prevents scheduler entry; the inspected
in-body request contract drains the current slot and stops before the next
calendar slot. This drain rule is recorded as an ABI contract pending its
precise source-language correspondence, not labelled a new clause-4 mandate.

`runUntil(maxFs)` must not consume a later calendar event beyond the bound or
advance time when no event exists. Reaching a run bound, exhausting proof
fuel, naturally exhausting the kernel and requesting finish are four distinct
outcomes. No unconditional termination theorem is planned for arbitrary
zero-delay loops.

### 3.3 Publication, ordinary signals and named events

Scalar ABI values carry two 64-bit planes. For an unknown bit, value zero is X
and value one is Z. The language model remains `Logic`/`LVec`; an ABI bridge
must preserve both planes and refuse unsupported widths rather than truncate.

Ordinary publication owns value change and the shared change token. A
same-value write keeps its token. Publication drives edge/value-change wakes
at the transition where the new value becomes visible, including queued NBA
updates. Array views project to these same signal identities, not another
value store or notification counter.

Named-event occurrence is separate from ordinary value publication. It does
not alter signal planes or ordinary change tokens. Blocking trigger wakes
already armed occurrence waits; nonblocking trigger queues an occurrence in
NBA/Re-NBA. Persistent `triggered` state lasts for the current simulation time,
including region re-entry, and expires on time advance. A null named-event
target neither triggers nor acquires an occurrence waiter. Alias resolution
and event typing belong to the consumer's certified metadata.

### 3.4 Waits, forks and control

Delay waits accept exact known femtoseconds. Event waits copy and validate a
nonempty dependency set; ordinary edges and named-event occurrence masks are
different semantic categories, without asserting an ABI mask equivalence.
The initially inspected README described a registration-owned condition
predicate service. Later owner decisions retired that service in favor of
consumer evaluation, operand-change subscriptions and re-entry. IEEE 9.4.3
still requires an initial condition test, immediate continuation when true,
and otherwise waiting for truth; a known-Boolean runtime predicate profile
must not be mistaken for a restriction of source truth semantics.

The owner's October 9, 2026, 20:14 UTC correction records a remaining gap:
IEEE 9.7 fixes condition truth at the resume call, while later body re-entry
may observe a same-step reversal and block again. Consumer re-entry does not
establish resume-time truth latching. The new wait vocabulary does not select
a predicate ABI, encode a re-entry marker as a source edge, or close this gap.

Fork groups own immediate-child membership and parent incarnations.
`join_none` children defer until the parent blocks or terminates. A blocking
join releases previously deferred groups. `join` waits for the selected group;
`join_any` resumes on its first completion; `wait fork` covers live immediate
children, not all descendants. Child execution order is not implied by the
spawn-list order. Descendant cancellation cannot mistake a recycled slot for
an old child, or lose ancestry through a finished intermediate child.

Process-control suspension is distinct from waiting on a dependency. Kill,
await, suspend and resume use the durable process registry. Named-block
disable selects typed declaration activations and resumes the saved
post-block continuation, cancelling abandoned waits while preserving the
registration and explicit suspension state. Captured automatic activations
are shared and retained by descendants, not copied into process attachments.

## 4. Planned pure schema

The region, time, process and wait vocabulary below is exported; the remaining
pieces are design names.
The intended home is an additive `LeanModels/Sv/Engine2/` surface. Existing
cycle/AST definitions and theorem statements remain intact; bridges are proved
when both sides exist rather than assumed during the schema work.

| Piece | Proposed contents | Invariant or boundary |
| --- | --- | --- |
| `Engine2.SimTime` (landed) | Natural femtoseconds and exact relative-delay arithmetic | Checked 64-bit ABI conversion; occupied-slot advancement remains a future rule |
| `Engine2.Region` (landed) | Complete clause-4 region inventory and region-set classification | Presentation position is not execution priority; iteration edges remain future rules |
| `Engine2.ProcessKey` (landed) | Natural registration identity, independent of scheduler storage | Fresh allocation and historical retention remain future registry invariants |
| `Engine2.ProcessState Frame` (landed) | Live continuation phase/explicit suspension, or distinct normal/forced termination | Source status is not scheduler readiness; wait/control transitions remain future rules |
| `Engine2.ProcessRecord Frame` (landed) | Key, body kind, independent control eligibility, lifecycle | Data replacement preserves registration metadata, not a proof of a legal transition |
| `SignalState` (landed) | Typed signal identity, `LVec` value, publication generation | One ordinary value/publication authority; named events use occurrence state |
| `Engine2.WaitRegistration` (landed) | Independent wait/continuation identity, captured reason/dependencies and resume region | Identity recognition only; single-wake consumption, cancellation and region legality remain future rules |
| `Engine2.ScheduledEvent` (landed) | Event identity, time, region, action, origin and sequencing provenance | Process resume, value update and event occurrence are distinct actions; queue policy remains future |
| `PendingUpdates` (landed) | Captured target/value or captured named-event target, due time/region | RHS/target capture separated from later publication; origin retained for ordering |
| `ForkState` (landed) | Group identity, parent key, child keys, deferred release and join barrier | Immediate-child waiting distinct from transitive descendant cancellation |
| `NamedEventState` (landed) | Resolved identity or null; last occurrence time/validity | Persistent occurrence never masquerades as ordinary value change |
| `ControlState` (landed) | Awaiters and named-block activation continuations; derived suspension view | `ProcessState` alone owns explicit suspension; registration survives continuation replacement |
| `CompletionState` (landed) | Initialized/draining facts and optional explicit status | Natural completion derived from queues; first explicit request retained |
| `KernelState Frame` (landed) | Current time/phase, processes, signals, current/future events, forks, controls, output | No native addresses, cache, allocator, packed-token shortcut or duplicated authority |

### Landed region vocabulary

`LeanModels/Sv/Engine2/Regions.lean` exports the complete seventeen-constructor
`LeanModels.Sv.Engine2.Region`, independently of the legacy R1 interpreter.
Its checked lists contain nine simulation regions and eight additional
PLI-only regions (clauses 4.4.2 and 4.4.3). PLI-only does not mean every region
that permits a PLI callback: Preponed and Postponed remain simulation regions.
Observed does not permit PLI callbacks.

The active and reactive region sets each contain five regions, as defined by
4.4.1; the iterative set contains fourteen, including Pre-Observed and
Pre-Postponed. The active set is not the broader Active-through-Post-Observed
scheduling phase in 4.5. No next-region function or scheduling oracle is
introduced by this vocabulary-only piece.

`Region.position` records the inventory's presentation order in `Fin 17`.
There is deliberately no region-order instance, execution-rank monotonicity
claim, or implicit ABI conversion. Exhaustiveness, no duplicates, partition,
position injectivity, and agreement of all positions with `List.range 17`
are Lean-checked. Region order along execution still depends on the future
queue/phase transition rules, including legal re-entry into Active.

`Region.ofR1` embeds the old fifteen-constructor vocabulary injectively and
preserves its simulation/PLI-only classification. The exact missing names
are Pre-Observed and Pre-Postponed. This is a vocabulary bridge, not a claim
that the old snapshot oracle or AST scheduler implements Engine 2 semantics.

The real source fixtures in `Examples/system-verilog/engine2_regions/` agree
byte-for-byte between Icarus and Mox's compiled Engine 2 consumer. They measure
zero-delay/NBA separation and NBA-triggered Active re-entry, not PLI callbacks
or a refinement of the new Lean type to native code. The existing Lean
self-check source driver refuses these delay/event-control shapes; that
boundary is recorded rather than counted as differential agreement. See the
fixture README for commands and the measured artifact revision.

The reference calendar is a finite semantic collection of events indexed by
time/region, not a commitment to a heap, wheel or FIFO. Derived eligibility
and queue-emptiness predicates have one definition. An incarnation in an
event makes stale cancellation checkable without modelling recycled storage.

### Landed normalized simulation time

`LeanModels/Sv/Engine2/Time.lean` defines `Engine2.SimTime` as a natural
femtosecond count, with chronological comparison, `zero` and `after time
delayFs`. The delay argument is already known, nonnegative and normalized to
femtoseconds. Relative-delay arithmetic is deterministic and needs no oracle.
Kernel-checked facts establish zero-delay identity, associative delay addition,
nondecrease, strict increase exactly for positive delays, and monotonicity in
both the starting time and the delay. These are time facts, not permission to
advance the scheduler without completing the current slot.

IEEE clauses 3.14 and 3.14.3 permit physical units down to femtoseconds and
define each design's global precision. This representation does **not** set
global precision to 1 fs. Source-local precision rounding, defaults, computing
global precision, unknown/negative delay expressions and `$time`/`$realtime`
scaling remain lowering obligations. In particular, the source-language
64-bit four-state `time` type is not this natural-valued internal clock.

`SimTime.ofABI` decodes a runtime `UInt64` exactly. `SimTime.toABI` returns
`some` only below the exclusive bound `2^64`, and `none` otherwise. Its
roundtrip and success/failure equivalences prove that conversion never silently
wraps. `SimTime.checkedAfter` checks the **mathematical sum**, not just two
individually representable operands; success preserves the exact target and
failure is equivalent to the target reaching or exceeding the bound.

This is a specification-side admission adapter, **not** an assertion that Mox
currently refuses overflowing sums. The inspected delay and delayed-update
paths in `Kernel.h` add unsigned timestamps without a guard; the runtime
contract does not endorse an overflow meaning. The delay-range question in
section 6 remains open. No overflow policy or C++ refinement is inferred.

The fixtures in `Examples/system-verilog/engine2_time/` use explicit local
units and precision. Compiled Engine 2 and Icarus agree exactly on successive
positive delays and a zero-delay continuation at the same time. They measure
source behavior separately from these Lean arithmetic proofs. The Lean source
self-check harness still refuses their `$time`/delay-control shapes; the
refusals are retained, not counted as agreement. Region placement for `#0`,
occupied-slot advancement and bounded-run control remain future rules.

### Landed process identity and lifecycle

`LeanModels/Sv/Engine2/Process.lean` defines a natural-valued `ProcessKey`,
the five IEEE clause-9.7 `ProcessStatus` values, and a `ProcessState Frame`
whose live constructor owns the continuation frame, underlying phase and one
explicit-suspension flag. Normal completion and forced termination have
separate constructors, with neither a live frame nor a suspension flag.
State classification does not cancel external registrations automatically;
the wait-ownership and cancellation invariants still need their own rules.

Underlying phases distinguish registered, ready, executing, waiting and
deferred continuations. Registered and deferred are pre-dispatch phases, not
new source-language status values or evidence that execution has begun.
Explicit suspension parks the underlying phase, which is not an effective
wait registration or permission to execute. A deferred child is not thereby
process-class SUSPENDED; waiting is not explicit suspension. The opaque frame
must retain original wait information when needed, but this does not implement
desensitization, resensitization, deadline preservation or condition testing.

`ProcessState.status` gives suspension precedence over a live parked phase,
and distinguishes WAITING from unblocked RUNNING. Semantic `ready` means
**unblocked**, not a raw embedding of native `PS_Ready`, especially after
`#0`. A native-to-source status bridge remains unproved; these constructors
must not be used to declare the existing C++ status service conformant.
`ProcessState.isReady` is only a necessary local dispatch condition; region
eligibility, queue membership and global control are still required. The
checked theorems are one-way readiness/status facts, exact terminal/suspension
classifications and live-frame presence, not scheduling or termination proofs.

`ProcessRecord Frame` separates registration identity and immutable consumer
metadata from the current state. Callback/resume-thunk body kind is admission
metadata, not the IEEE initial/always classification. `controlAllowed` is
independent certified provenance, not derived from body kind. `withState` is
plain data replacement preserving key, body kind and control eligibility; it
is not a process-control or resurrection transition. No scheduler-slot cast,
handle packing or allocation policy is introduced. Key uniqueness and durable
historical retention require future registry invariants, not just this type.
Original registration attachments are also distinct from continuation frames
and automatic-variable storage, and remain a consumer boundary.

The source fixtures in `Examples/system-verilog/engine2_process/` agree exactly
between compiled Engine 2 and Icarus on natural exhaustion with a blocked
process, and on edge-wait resumption followed by independent body completion.
They do not query process-class status or measure kill/suspend/resume policy.
Lean source-driver refusals are retained separately, not counted as agreement.
The owner's recorded resume-time condition-truth-latching gap is not closed by
this opaque-frame schema; no implementation refinement is claimed. This data
piece requires no scheduling oracle.

### Landed normalized wait registrations

`LeanModels/Sv/Engine2/Wait.lean` separates ordinary `SignalKey` endpoints
from `NamedEventKey` synchronization objects. The ordinary edge vocabulary
distinguishes posedge, negedge, their `edge` union and whole-result value
change: X/Z exchanges belong only to the last category. Directional edges
inspect the result's LSB. These are directly monitored values, not a promise
that arbitrary `@(expression)` can be decomposed into operand-change waits;
an operand change that leaves the expression result unchanged is not an event.

`WaitDependency` separates ordinary value/edge subscriptions from instantaneous
named occurrences. It does not represent persistent `.triggered` state.
`EventDependencies` uses a structural head/tail representation for the admitted
nonempty subset, retaining order and duplicates. Entries are OR alternatives,
not wake priorities or a claim of multiple activations/source evaluation order.
Kernel-checked nonemptiness and list injectivity do not prove single-wake
consumption. Empty/inferred-empty lists must not silently become forever waits.

`ContinuationKey` couples a durable owner with a mathematical incarnation;
`WaitKey` independently identifies a registration. `WaitIdentity` contains
both, and `WaitRegistration.owner` is derived rather than stored twice. The
incarnation is not a wrapping native generation word, scheduler slot, or
automatic-variable activation token. Equality recognition and owner/key/epoch
mismatch lemmas do not establish fresh allocation, active registry membership,
stale-wake rejection or cancellation. `ProcessState` remains the sole explicit
suspension authority; the descriptor has no competing suspension flag.

`WaitReason` records an absolute deadline, event alternatives, or independently
justified forever parking. Absolute deadlines can retain the original due time
across suspension; no such transition is implemented here. Unsupported
normalization, failed dependency census and null events are never forever
fallbacks. Named-event waiting on null is undefined in the standard and excluded
from admission. Zero is just a mathematical key, not an ABI null encoding;
registry membership and non-null resolution remain admission obligations.
`resumeRegion` is explicit data, not a default policy or proof of legality.

Conditional `iff` gates, level-wait predicates and resume-time truth handoff,
arbitrary event-expression normalization, clocking/sequence events, fork waits
and process-await descriptors remain outside this partial vocabulary. No native
mask conversion is asserted: the older EVENT-only README wording and the
owner's later ANY-on-named-event correction must not be encoded as a source
semantic theorem. This schema piece introduces no scheduling oracle.

Two ordinary source fixtures in `Examples/system-verilog/engine2_wait/` agree
exactly between compiled Engine 2 and Icarus on OR alternatives resuming once
and a later fresh edge wait. A named-event source attempt was explicitly refused
by compiled Engine 2 during emission; its source, IR and oracle/refusal outputs
are retained, not counted as agreement. Lean source-driver refusals also remain
separate from the pure vocabulary proofs. No wake-rule or C++ refinement proof
is claimed by these observations.

### Landed scheduled-event vocabulary

`LeanModels/Sv/Engine2/Event.lean` defines `ScheduledEvent` as a semantic
calendar entry with an `EventKey`, normalized `SimTime`, explicit `Region`, an
`EventAction`, an `EventOrigin`, and a sequence number. `EventAction` has three
non-interchangeable cases: a process resume carrying a `WaitIdentity`, an
ordinary `SignalKey` update carrying an `LVec` four-state value, and a named
occurrence carrying a `NamedEventKey`. `EventOrigin` records a process, a wait
registration, or an external source without treating provenance as a native
pointer or scheduler queue position. `EventKind` is derived from the action;
checked theorems are exhaustive kind classification only.

The sequence field is provenance supplied by a future scheduler or policy
oracle. It does not assert that independent events have a mandated total order.
Likewise, an event key is semantic identity, not a slot address, packed token,
allocator result, or proof that cancellation has removed another event. No
queue admission, stale-event filtering, publication, named-event persistence,
region legality, or scheduler transition is defined here. Pending-update
capture and NBA ordering will consume this vocabulary in a later piece.

The fixtures in `Examples/system-verilog/engine2_event/` agree byte-for-byte
between compiled Engine 2 and Icarus on a delayed signal update and a separate
process resuming after that update. They do not expose the internal action,
origin or sequence fields and therefore are source evidence only; existing Lean
source-driver refusals for timing/event controls remain separate from the pure
schema proof.

### Landed pending-update captures

`LeanModels/Sv/Engine2/Update.lean` defines `PendingUpdateTarget` with two
well-typed cases: a signal target paired with its captured `LVec` value, or a
named-event target with no value payload. `PendingUpdate` preserves an
`EventKey`, absolute due `SimTime`, explicit `Region`, and `EventOrigin`; its
derived action agrees with the corresponding scheduled signal-update or
named-occurrence action. `PendingUpdates` is only a list alias for captured
records. The structural projections and exhaustive kind facts do not define
queue admission, NBA ordering, publication, cancellation, stale filtering,
overflow, or scheduler policy. No source fixture can expose these internal
captures, so this piece adds no differential claim.

### Landed ordinary signal state

`LeanModels/Sv/Engine2/Signal.lean` defines `SignalState` as one semantic
ordinary-signal record: a `SignalKey`, its current `LVec`, and a
`PublicationGeneration`. The generation has an explicit initial state whose
token is zero and an issued state whose token is nonzero; this captures the
kernel's read-side distinction without choosing token allocation or rollover.
Named-event occurrence state is intentionally not folded into this record.
Only construction, token classification and field-preservation facts are
proved here. Value-change detection, same-value retention, fanout, publication
timing, queue admission, and wakeups remain later rules.

### Landed named-event occurrence state

`LeanModels/Sv/Engine2/NamedEvent.lean` defines `NamedEventState` with an
unresolved case and a resolved case carrying a `NamedEventKey` plus an
optional last-occurrence `SimTime`. The optional time is the occurrence
validity bit: `triggeredAt` is true exactly when the recorded occurrence time
equals the queried simulation time, and therefore naturally expires after time
advance without a reset transition. Structural facts prove null/resolved
classification and current-slot observation only. Trigger admission, alias
resolution, wake consumption, NBA/Re-NBA scheduling and time advancement stay
outside this schema piece.

### Landed fork-group state

`LeanModels/Sv/Engine2/Fork.lean` defines `ForkState` with a semantic
`ForkKey`, parent `ContinuationKey`, direct child `ProcessKey` membership,
`ForkJoinKind` (`join`, `joinAny`, or `joinNone`), and explicit deferred or
released state. The child list is membership data only and carries no execution
priority. Initial constructors capture the kernel's immediate-release versus
`join_none` deferral distinction; structural facts classify modes, release
states, parent ownership and child membership. Spawn, release, join wakeups,
descendant cancellation, process-slot reuse and scheduler ordering remain
future rules.

### Landed completion state

`LeanModels/Sv/Engine2/Completion.lean` defines `CompletionState` with explicit
initialization and current-slot draining facts plus an optional explicit finish
status. `requestFinish` retains the first supplied status and never clears it;
`finishStatus` reports zero when no explicit request exists. Natural completion
is a derived observation over a scheduler-provided queue-exhaustion fact, gated
by initialization, and is false during a drain. It does not inspect process
termination, so sensitized registrations may remain after natural exhaustion.
The state helpers do not implement queue draining, time advancement, external
reopening, or the scheduler's completion transition.

### Landed process-control state

`LeanModels/Sv/Engine2/Control.lean` defines await registrations and typed
named-block activations. Awaiters carry an independent registration key, their
continuation, target process and resume region. Named-block activations carry a
declaration/activation identity, entry continuation and saved post-block
continuation. The `ControlState` lists are membership data only; their derived
awaiting view does not replace `ProcessState`'s explicit suspension authority.
Continuation replacement therefore preserves registration identity, while
cancellation, wakeups, declaration lookup and disable/resume transitions stay
outside this schema piece.

### Landed aggregate kernel state

`LeanModels/Sv/Engine2/Kernel.lean` defines `KernelState Frame`, combining the
landed time/region, process, signal, named-event, event/update, fork, control
and completion records with an explicit output-chunk list. Initial state and
membership/count observations are proved structurally. The collection fields
are policy-neutral lists: no scheduler order, publication, queue admission,
time advance, body execution or output rendering is selected here.

### 4.1 Consumer body interface

The body parameter supplies a deterministic transition on an explicit frame
and visible kernel inputs, yielding a next frame and a typed kernel command:
publication, enqueue update, wait, fork/control operation, output, completion
or refusal. It must preserve the consumer's sequential statement order and
capture update arguments when evaluated. A kernel cannot invent arbitrary
body results by consulting a scheduling oracle.

The residual-list representation can support a later adapter, but today's
big-step `stepSStmts` returns only final signals/NBA/output. It can hide
intermediate publications, so instantiation requires a finer-grained adapter
and a refinement proof, not the existing function unchanged. The semantics of
a real admitted compiled artifact is another intended consumer. Relating
emitted resume thunks to that body semantics is future work. Environment inputs,
including any nondeterministic RNG/host input used by bodies, are explicit
parameters of the consumer semantics rather than hidden kernel state choices.

### 4.2 Oracle boundary

`SchedulingOracle` selects an eligible event at each choice point, with a
proof that its selection belongs to the eligible set. Eligibility incorporates
mandated region/phase rules and sequencing constraints. A next-event interface
can see work published during a region, unlike the old batch permutation.
Embedding `RegionOracle` requires a proved snapshot-policy bridge, not an
assertion that the interfaces already express identical schedules.

The inspected kernel's C5 policy applies all due queued Active updates before
same-slot process evaluations, including timed/cohort work. This is the
chosen Mox refinement policy, not an IEEE-mandated update/evaluation priority.
Its conformance examples must identify that policy while the language oracle
continues to admit other legal Active orders. The old-ready/new-ready and
rescheduling-boundary questions remain separate.

Only freedoms licensed by the language enter that oracle: same-region ready
selection, interleavings at allowed process boundaries and ordering of
independent evaluations. The scheduler cannot choose the time advance,
reorder sequential statements, change sampled values, drop required events or
violate mandated NBA ordering. A concrete FIFO/reference choice is a policy
instance, never a language guarantee.

Where a particular disabled task's pending NBA disposition is unspecified,
any supported retain/discard choice needs its own explicitly scoped
`DisabledTaskUpdatePolicy` and legality condition. It is not permission for a
general cancellation oracle to delete arbitrary updates. The exact cases and
the inspected implementation's retain policy require the owner's contract
answer before the rule lands.

### 4.3 Transition relation and proof targets

The relation will be factored into initialization, ready-event selection,
body-command execution, publication/wakeup, region iteration, occupied-time
advance, process/fork control and completion. Each item lands with its own
well-formedness preservation statement and executable examples.

Planned specification theorems are:

- **Determinism modulo explicit parameters:** fixed body semantics, legal
  oracle, environment, all policy parameters and initial state determine one
  step. This does not say racy designs agree across different oracles.
- **Time/phase discipline:** time never decreases; transitions within a
  scheduler phase obey its order, with explicitly permitted region re-entry.
  Global numerical region monotonicity is false for an iterative scheduler.
- **Publication coherence:** captured updates publish once, notify the proper
  waiters and cannot be replaced by later producer-frame values.
- **Identity/control coherence:** stale waits cannot wake a recycled process;
  terminal and explicitly suspended registrations are not spuriously runnable.
- **Completion characterization:** natural completion is initialized,
  out-of-drain event exhaustion, not absence of live/sensitized processes;
  explicit finish remains sticky. Progress/completion proofs require stated
  finiteness or convergence assumptions.

None of these is presently a theorem about the C++ implementation.

## 5. Two traces, not one accidental observable

Keep `Slot`/`RegionTrace` and `cycleOf` as the coarse language observation.
Introduce a separate event-level `KernelTrace` for scheduling conformance,
with time, region/iteration, event identity, process registration, command
origin, update capture/publication, wake/cancel, output and completion labels.
Audit labels expose causality without making every scheduler detail a
cycle-visible language result. A richer audit trace must not silently change
the existing `Deterministic` predicates.

The eventual kernelbench checker derives mandated predecessor constraints
from those labels and checks them against a finite trace. It must distinguish
invalid order from missing/unsupported trace evidence, and must not reject a
different legal same-region policy. Implementation FIFO order, slot numbers,
host addresses and publication-token magnitudes are not mandated-order facts.
Projection to output, signal snapshots and termination status is separate.

## 6. Questions routed to the kernel owner

These are also emitted as `REQUEST engine2:` lines in the lane journal. Until
answered, a missing contract is a blocked rule, not a guessed default.

| Topic | Required answer |
| --- | --- |
| Region mapping | Confirm the clause-4 roles/order of all seventeen enum entries, especially Pre-Observed and Pre-Postponed, and which may enqueue earlier-region work |
| Ready selection | Is snapshot-draining a policy only, or does the consumed contract require old ready work to run before work added during the same region? Which body boundaries permit rescheduling? |
| NBA provenance | Which per-process/same-target ordering edges are mandated, and does the ABI additionally promise a total enqueue/publication order across independent origins? |
| Finish boundary | Precisely which current-slot work drains after an in-body finish request, including Reactive/Postponed and fork-created work; what is its source `$finish` correspondence? |
| Drive sentinel | What replaces zero-delay/region-zero immediate publication, and how are illegal writes from read-only regions refused? |
| Delay range | What happens on `now + delayFs` overflow and when a bounded run stops with current-time work still pending? |
| Suspension | When a dependency fires during explicit process suspension, which ready/wait state and resume region are retained? |
| Wait surface | Is the named-event condition dependency allowed by ABI 19 already part of the contract, and should the Lean kernel expose condition predicates or only consumer-lowered event waits? |
| Publication identity | Are token equality/change observations the only guarantee, and what is the rollover rule? Is the publication accessor staying exported? |
| Fork cancellation | Confirm the precise scope of the recorded nonblocking/empty-join release distinction and the pending-update disposition on halt, kill, disable fork and named-block redirection |
| Callback admission | Reconcile the header's blanket wait prohibition with README's `wait_static` exception and the decision to remove that unused entry |
| Image tables | Reconcile the header's offset-table prose with the README and actual counted-pointer declarations; no layout guess belongs in the pure spec |

The README already marks zero-delay region-zero drive as a limitation. The
Lean tier must not turn that sentinel into a Preponed implementation, infer
source reachability from an enum, or special-case a particular workload.

## 7. Incremental acceptance plan

The next item is the region schema and ordering classification. Later turns
land one state piece or transition rule each: identity/lifecycle, event and
update queues, publication/waits, fork/control, then completion. Each rule
names all oracle/policy parameters and carries kernel-checked examples.

Before claiming differential coverage, extend the Sv harness with an explicit
Mox Engine 2 mode: the existing `harness/sv/diff_test.py` and `diff_test2.py`
compare the cycle tiers against Xcelium/Icarus, not this kernel relation.

The owner identifies the data-frame walker as the admitted-semantics reference
tier and the compiled emitter as the product tier, both consuming the same
kernel ABI. Separate three receipts: pure-kernel rule conformance, walker
body-semantics comparison against the Lean consumer, and compiled-body
refinement against the walker. A shared kernel does not prove body equivalence.

Small real fixtures should run through `mox-sim --mode=engine2-compiled`,
record admission/refusal separately, and compare observable traces under the
implementation's identified legal policy. A race fixture also needs distinct
legal Lean schedules; one implementation run is not evidence of a mandatory
relative order. Focused tests remain bounded to the rule being introduced.

Only after the schema/rules exist does the mandated-order checker become an
exported executable reference. No prototype theorem, assumed adequacy lemma,
new axiom or weakened existing statement closes that milestone.
