# ls-sv2 — lane backlog

Per-lane backlog, per `docs/family-architecture.md` §9.5. Entries are appended
by the ls-sv2 lane; ids are `YYYY-MM-DD-ls-sv2-<n>`.

---

## 2026-11-05-ls-sv2-1 — make RV differential cases and oracle provenance reproducible

Claude's ISA audit found that `harness/rv/diff_test.py` selected each ALU
corner with Python's process-salted `hash()`, despite exposing `--seed`, and
reported only the configured Sail path. This was a harness defect, not an ISA
semantic disagreement: repeated `gen_cases(0xC0FFEE)` calls produced unequal
case corpora before this landing.

The harness now selects corners with `zlib.crc32` (without consuming the main
seeded RNG stream), exposes `--self-test`, and prints the requested seed. A
normal run queries `sail_riscv_sim --version`, refuses anything other than the
pinned 0.13.1 release, and prints that version line plus the oracle binary's
SHA-256. The self-test passes under `PYTHONHASHSEED=1`, `2`, and `random`, with
all 257 cases equal on repeated generation. The local Sail binary is absent,
so no differential PASS count is claimed here.

**DECIDED:** this item changes harness generation and provenance checks only;
the RISC-V model and its semantics are unchanged. The next audit item is the
WFI/profile-resolution finding after the required inbox reread.

## 2026-11-05-ls-sv2-2 — expose the privileged WFI ordering as a platform profile

Claude's audit verified one real spec-legal resolution choice: when a freshly
reached WFI has a pending globally-enabled interrupt, the model had hardwired
WFI-first even though privileged v1.11 §3.3 permits WFI-first and
interrupt-first. The other CSR reset/WARL values are CV32E40P platform choices
already fixed by the scoped RTL contract, not unresolved ISA nondeterminism.

`WfiResolution` and `PlatformProfile` now carry the fresh-WFI order;
`isaStepWith` and `isaStepMemWith` consume the profile, while `isaStep` and
`isaStepMem` remain CV32E40P wrappers through `cv32e40pProfile`. The reusable
`isaStepWith_wfiPending` theorem states the dispatcher equation for every
profile, and the `Step.lean` battery covers both orders. `rvMachineWith` in the
refinement adapter is profile-parametric; the existing `rvMachine` remains the
CV32E40P adapter.

**MEASURED:** `lake build LeanModels.Rv.Step` passed (7 jobs), the focused
refinement/toy and PicoRV32 proof targets pass, and the toy proof's axiom
reports remain limited to `propext` and `Quot.sound`. `python3 tools/docs_check.py`,
`tools/backlog-index.sh --check`, and `git diff --check` pass. No Sail binary is
present, so this item adds no new differential PASS claim; the existing 257-row
oracle result remains the recorded validation.

**DECIDED:** the profile parameter is explicit at the ISA step and generic
refinement adapter, with the historical CV32E40P names preserved as wrappers.
The remaining audit item is the missing Sail refinement theorem/documentation
finding, after the required inbox reread.

## 2026-11-05-ls-sv2-3 — make the Sail boundary explicit and gate every decoder row

Claude's audit found that the generated Sail Lean package remains a separate
semantics with no refinement theorem, and that its support file carries 75
axioms. The generated tree is still outside the repository and cannot be
rewritten around its namespace defect. This landing records the honest
boundary rather than claiming a theorem that cannot compile.

`LeanModels/Isa/RiscV/Oracle.lean` defines `SailPlatformOracle`,
`SailFloatOracle`, and the combined `SailOracle M PA`, with all eight
platform/reservation/randomness signatures and all 67 floating-point/
conversion signatures as explicit fields. It has no default implementation or
axioms; a future generated Sail semantics must consume this parameter.

The differential runner now attributes retired parcels to the model's own
`decodeTable` rows and fails a run when any row lacks a passing Sail case.
`python3 harness/rv/diff_test.py --coverage-only` performs the model-side gate
without the oracle; the deterministic 257-case corpus reaches **57/57 rows**.
The Sail binary is absent on this host, so this is coverage attribution, not a
new oracle PASS result; the recorded 257/257 result remains the last Sail
comparison. The README and `docs/rv-model.md` now state this boundary.

**DECIDED:** do not invent a refinement theorem or vendor the broken generated
package. Keep `SailOracle` as the explicit integration contract and require a
real Sail differential result for the row gate when the pinned binary is
provisioned.

## 2026-11-05-ls-sv2-4 — re-probe the R2 cores after the memory route

The inbox was reread before this item.  The owner lane's generic one-rank
memory route is present on `origin/master`, so the three pinned in-order core
envelopes were re-probed without changing their RTL.  The CV32E40P envelope
(`e5888846…`, 21,289,394 bytes) still refuses at
`AlwaysPosedge: AlwaysPosedge:edge — edge-qualified clock requires its retained
event semantics`; Ibex (`ae014736…`, 13,914,127 bytes) still refuses at
`AlwaysLatch: unknown process kind "AlwaysLatch"`.  The current PicoRV32
envelope (`009cc395…`, 3,178,052 bytes) loads, but its default semantic
family still reports
`unsupported "Instantiate" "decl 'cpuregs': unpacked array storage outside E
(UnpackedDecl:memory)"`; the memory adapter still reports
`memory cycle route does not yet admit generate members`.

**DECIDED:** the generic memory work has not moved PicoRV32 past its first
source-shaped wall, and the CV32E40P/Ibex process-form walls are unchanged.
Keep the exact owner-lane requests in its inbox, make no core-specific
adaptation, and wait for a generic generate/member or process-semantics change
before adding proof glue.

## 2026-11-05-ls-sv2-5 — connect the measured PicoRV32 RVFI prefix to the ISA trace

The inbox was reread before this item.  The pinned PicoRV32 RVFI witness has a
four-instruction non-trapping prefix (`ADDI`, `SW`, `LW`, `ADDI`) whose rows
were already checked against Icarus 13.0 and Verilator 5.052.  Added
`Examples/system-verilog/cores/picorv32/trace_proof.lean`: explicit byte
memories model the post-store load response, and the axiom-free theorem
`pinned_nontrap_trace_refines_isa` proves that the normalized hardware rows
equal the finite `rvMachine` trace, including register and memory effects.

The measured `ebreak` row remains intentionally outside this equality.  The
core reports `pcWdata = 16` on the trap while the architectural model enters
`mtvec = 0`; the README records this visible RVFI/ISA contract boundary rather
than guessing a correction.  The theorem is therefore a finite observation
witness for the real pinned core, not a whole-core refinement theorem; the
loader's unpacked-memory/generate wall is unchanged.

**MEASURED:** `lake build LeanModels.Refine Examples.«system-verilog».cores.picorv32.trace_proof` passed (25 jobs); the two new theorem axiom reports contain only `propext` and `Quot.sound`. `python3 tools/docs_check.py` and `git diff --check` passed.

**DECIDED:** retain the four-row bridge as the first real-core use of the R1
ISA trace contract, and keep the trap-PC mismatch explicit until a core-wide
RVFI trap convention is specified and proved.

## 2026-11-05-ls-sv2-6 — certify finite RVFI order and normalization

The inbox was reread before this item.  The packed RVFI adapter converted rows
independently, so a caller could accidentally discard `valid` cycles or compare
rows without proving that their `order` fields were the architectural commit
sequence.  Added `RvfiTraceRefines` and `normalizeRvfiTrace?` to
`LeanModels/Refine/Rvfi.lean`.  Invalid cycles are explicit bubbles; valid
cycles must have the next consecutive order and a successful
`toRetirement?`, and `normalizeRvfiTrace?_iff` proves the executable checker is
equivalent to the inductive certificate.  The `start` parameter supports a
finite window cut from a longer RVFI run without assuming that its first order
is zero.

The PicoRV32 witness now certifies all five measured rows, including the
proof-side breakpoint annotation, and has a negative row whose order is
changed from 1 to 3; the checker returns `none` rather than sorting it.  The
four-row non-trapping ISA trace witness consumes the same certificate shape.

**MEASURED:** `lake build LeanModels.Refine.Rvfi
Examples.«system-verilog».cores.picorv32.rvfi_proof
Examples.«system-verilog».cores.picorv32.trace_proof` passed (18 jobs).  New
theorem axiom reports contain only the repository's standard `propext`,
`Classical.choice`, and `Quot.sound`; no `sorryAx`, `axiom`, or RTL change was
introduced.  The next validation is the normal docs/backlog checks followed by
the required commit and push.

**DECIDED:** keep order checking in the generic RVFI boundary.  A core-specific
proof must establish the observed order tags, while the adapter never chooses a
completion order or repairs a malformed valid row.

## 2026-11-05-ls-sv2-7 — compose the PicoRV32 observation and ISA traces

The inbox was reread before this item and had no new ls-sv2-specific request.
The preceding item proved an order-aware certificate for the packed RVFI rows
and separately proved that the finite ISA machine produced the expected
retirements.  Added `pinned_nontrap_observed_trace_refines_isa`, which rewrites
those two facts into one equality between the normalized measured RVFI stream
and `trace rvMachine ... nontrapInputs`.  The witness still ends before the
measured trap row because PicoRV32's `pcWdata = 16` differs from the ISA
model's `mtvec = 0` entry, as already documented.

**MEASURED:** the focused PicoRV32 trace build, docs check, backlog-index check,
and `git diff --check` passed.  The new theorem uses only the existing
`propext`/`Quot.sound` proof boundary; it adds no axiom and does not change the
RTL or the SV loader.

**DECIDED:** expose the composed equality as the core-specific R1 bridge while
keeping the generic order certificate reusable for later cores.  The next item
is another generic refinement obligation or a re-probe after an owner-lane
loader change.

## 2026-11-05-ls-sv2-8 — certify PicoRV32's measured byte-memory effects

The inbox was reread before this item and had no new ls-sv2-specific request.
The composed RVFI-to-ISA equality already compared the `SW` and `LW` rows as
retirement fields.  Added `nontrapMemoryRequests`, `nontrapMemoryEffects`, and
`pinned_nontrap_memory_effects` to the PicoRV32 trace witness.  The theorem
checks the exact `directRun` contract: a word write of 5 at `0x100` followed by
a word read at `0x100` returns the two measured effects, including load data 5.
It uses the same byte-addressed `storeVal`/`loadVal` semantics as the ISA
adapter, and leaves the real core's memory port unchanged.

**MEASURED:** the focused trace build, docs check, backlog-index check, and
`git diff --check` passed.  The theorem has only the existing standard axiom
ledger; no new axiom, RTL edit, or loader adaptation was introduced.

**DECIDED:** retain this memory certificate beside the observation-to-ISA
bridge.  It is a finite measured-memory witness, not a claim that the blocked
PicoRV32 RTL has been symbolically loaded; the unpacked-register-memory and
generate-member walls remain the next core-admission dependency.

## 2026-11-05-ls-sv2-9 — exercise the RVFI cycle bridge with measured bubbles

The inbox was reread before this item and had no new ls-sv2-specific request.
Added an eight-cycle `RvfiCycleMachine` witness around the measured PicoRV32
prefix: each of the four valid rows is preceded by an invalid RVFI bubble.  The
proof establishes that `retireInputs` retains exactly the four instruction
inputs, that `cycleTrace` produces exactly the four normalized retirements, and
that the filtered cycle trace equals the finite `rvMachine` trace.  The
machine emits only the already measured observation data; it does not model or
rewrite the pinned RTL.

**MEASURED:** the focused cycle/trace build, docs check, backlog-index check,
and `git diff --check` passed.  The new theorem reports remain within the
existing `propext`/`Quot.sound` ledger; no axiom, RTL edit, or loader
adaptation was introduced.

**DECIDED:** keep invalid RVFI cycles as explicit stutter at the generic cycle
boundary and preserve the finite filtered-trace theorem for later cores.  The
PicoRV32 symbolic proof still waits on the unchanged unpacked-memory and
generate-member loader support.

## 2026-11-05-ls-sv2-10 — add stateful RISC-V memory threading

The inbox was reread before this item and had no new ls-sv2-specific request.
The commit interface's `Input.memory` is an always-ready view, but a core
refinement needs memory to persist across stores and later loads.  Added
`RvMemoryState`, `rvMemoryMachineWith`, `threadRvInputs`, and the theorem
`rvMemoryMachine_trace` in `LeanModels/Refine/MemoryMachine.lean`.  The
stateful machine uses `isaStepWith` and `applyMemEffect`; the theorem proves
its retirement trace equals the existing stateless `rvMachineWith` trace after
each input is replaced by the memory state that precedes it.  The profile
parameter is retained, so WFI resolution remains explicit.

The PicoRV32 trace witness now instantiates this theorem over the measured
four-instruction prefix, alongside the concrete `directRun` write/read
certificate.  No memory contents are guessed from the core: the stateful
adapter is the exact byte-addressed ISA contract.

**MEASURED:** the focused stateful-memory and PicoRV32 trace build, docs check,
backlog-index check, and `git diff --check` passed.  New theorem reports stay
within the existing `propext`/`Quot.sound` ledger; no new axiom, RTL edit, or
loader adaptation was introduced.

**DECIDED:** use `RvMemoryState` as the memory-threading boundary for later
in-order and out-of-order core proofs.  The symbolic PicoRV32 loader remains
blocked at the unchanged unpacked-register-memory and generate-member routes.

## 2026-11-05-ls-sv2-11 — compose RVFI normalization across trace windows

The inbox was reread before this item; the current exact PicoRV32 envelope was
also re-probed and still reports the unchanged `cpuregs` unpacked-memory wall
and `memory cycle route does not yet admit generate members`.  Added the
generic theorem `normalizeRvfiTrace?_append` to `LeanModels/Refine/Rvfi.lean`.
It states that normalizing `first ++ second` is equivalent to normalizing the
first window, advancing the expected order by its retirement count, and then
normalizing the second window.  Invalid rows do not advance that count.

The PicoRV32 witness splits the four non-trapping rows after order 1 and
proves both chunk certificates and their composition, so a streamed capture
can be checked window by window without resetting order or sorting rows.

**MEASURED:** the focused Rvfi/PicoRV32 build, docs check, backlog-index check,
and `git diff --check` passed.  The theorem reports remain within the standard
`propext`/`Classical.choice`/`Quot.sound` ledger; no new axiom, RTL edit, or
loader adaptation was introduced.

**DECIDED:** keep chunk composition in the generic observation layer and keep
the concrete window split in the PicoRV32 witness.  The symbolic core remains
blocked on the owner lane's unchanged memory/generate route.

## 2026-11-05-ls-sv2-12 — bridge packed RVFI cycles to normalized cycle traces

The cycle adapter already projected each RVFI observation to an optional
retirement, but it had no generic theorem connecting that projection to the
order-aware packed-stream checker.  Added `rvfiObservations` and
`normalizeRvfiCycleTrace` to `LeanModels/Refine/Rvfi.lean`.  The theorem
inducts over every cycle and proves that, whenever normalization succeeds, the
existing `cycleTrace` emits exactly the normalized retirements.  Invalid rows
remain explicit bubbles and malformed valid rows cannot be silently dropped;
the proof does not sort or repair order tags.

The PicoRV32 bubble witness now proves normalization of its complete eight
cycle observation window and derives `pinned_cycle_trace` through the generic
bridge rather than evaluating the cycle trace independently.  The measured
four-row ISA equality and the stateful-memory witness remain unchanged.

**MEASURED:** `lake build LeanModels.Refine.Rvfi
Examples.«system-verilog».cores.picorv32.trace_proof` passed (20 jobs), with
the new theorem reports limited to the existing `propext`/`Quot.sound` ledger.
`python3 tools/docs_check.py`, `tools/backlog-index.sh --check`, and
`git diff --check` pass.  No `sorry`, new axiom, RTL edit, or SV-loader
adaptation was introduced.

**DECIDED:** keep the packed observation stream and cycle projection tied by a
single reusable theorem; later cores can discharge normalization from their
RVFI contracts without duplicating cycle recursion.  The symbolic PicoRV32
loader remains blocked at the unchanged unpacked-memory and generate-member
routes.

## 2026-11-05-ls-sv2-13 — project packed RVFI cycles into the ROB boundary

The reusable ROB layer already handled tagged in-order commit packets, but
the RVFI adapter had no connection to it.  Added `RvfiRob.lean` with
`RvfiCycleMachine.toRobMachine`: each decoded observation becomes a singleton
`TaggedCommit` carrying its original `order` and cycle input, while bubbles and
refused rows become empty packets.  The generic trace and input theorems prove
that this projection agrees exactly with `cycleTrace` and `retireInputs`; a
normalization corollary then supplies the ROB trace only after the packed
order/decode certificate succeeds.

The PicoRV32 eight-cycle witness now derives both `robTrace` and `robInputs`
for its four measured non-trapping instructions through this adapter.  No
completion order is reconstructed: the order tags are transported unchanged
and checked by `normalizeRvfiTrace?`.

**MEASURED:** `lake build LeanModels.Refine.RvfiRob
Examples.«system-verilog».cores.picorv32.trace_proof` passed (23 jobs), with
the three new theorem reports limited to `propext`/`Quot.sound`.
`python3 tools/docs_check.py`, `tools/backlog-index.sh --check`, and
`git diff --check` pass.  No `sorry`, new axiom, RTL edit, or SV-loader
adaptation was introduced.

**DECIDED:** keep the RVFI-to-ROB projection generic and one-entry-per-channel;
future superscalar cores can replace the packet producer while retaining the
same `TaggedPacketRefines`/`rob_trace_refines` contract.  PicoRV32 remains a
finite observed witness, not symbolic whole-core admission, at the unchanged
unpacked-memory and generate-member walls.

## 2026-11-05-ls-sv2-14 — support packetized RVFI observations

The one-entry RVFI-to-ROB adapter covers a single channel, while superscalar
cores expose a finite packet of channel rows at one cycle boundary.  Added
`RvfiPacketMachine`, `RvfiPacketEntry`, and `toPacketMachine` in
`LeanModels/Refine/RvfiPacket.lean`.  The packet theorem flattens observations
in the packet order supplied by the machine, filters only through
`toRetirement?`, and uses the new `normalizeRvfiTrace?_filterMap` lemma to
prove that a successful global order/decode certificate equals the generic
`packetTrace`.  Inputs remain attached to each row, so no cycle input is
silently reused for a different commit.

The PicoRV32 witness groups its measured bubble/retirement rows into four
two-entry packets (one bubble plus one valid row per packet).  It proves the
flattened normalization, the packet retirement stream, and the filtered
architectural inputs against the same four measured ISA instructions.  This is
a packet-boundary exercise over measured rows, not a claim that PicoRV32 is
superscalar.

**MEASURED:** `lake build LeanModels.Refine.RvfiPacket
Examples.«system-verilog».cores.picorv32.trace_proof` passed (24 jobs), and
the new theorem reports contain only `propext`/`Quot.sound`.  `python3
tools/docs_check.py`, `tools/backlog-index.sh --check`, and `git diff --check`
pass.  No `sorry`, new axiom, RTL edit, or SV-loader adaptation was
introduced.

**DECIDED:** keep packet flattening and order validation separate from the
core's scheduling or completion policy; a future superscalar proof can provide
its packet entries and consume the same `PacketRefines` contract.  The
PicoRV32 symbolic loader remains blocked at the unchanged memory/generate
walls.

## 2026-11-05-ls-sv2-15 — carry packetized RVFI rows into tagged ROB commits

The packet adapter now also exposes a tagged ROB view.  Added
`RvfiPacketMachine.toRobMachine`, preserving each row's RVFI `order` and
associated input in a `TaggedCommit`, plus trace and input projection
theorems.  `normalizeRvfiPacketRobTrace` reuses the flattened normalization
certificate before equating the tagged stream with retirements; the adapter
does not infer or reorder completion.

The PicoRV32 packet witness proves both tagged ROB outputs for the four
two-entry measured packets.  This exercises the same `robTrace`/`robInputs`
boundary that a future superscalar proof will use while keeping the measured
core's single-channel status explicit.

**MEASURED:** `lake build LeanModels.Refine.RvfiPacket
Examples.«system-verilog».cores.picorv32.trace_proof` passed (24 jobs), with
the new ROB theorem reports limited to `propext`/`Quot.sound`.
`python3 tools/docs_check.py`, `tools/backlog-index.sh --check`, and
`git diff --check` pass.  No `sorry`, new axiom, RTL edit, or SV-loader
adaptation was introduced.

**DECIDED:** keep packet and tagged-ROB projections as separate views over the
same observations so a core proof can state its commit-order certificate once.
The symbolic PicoRV32 loader remains blocked at the unchanged memory/generate
walls.

## 2026-11-05-ls-sv2-16 — certify packet tags from RVFI normalization

The packet-to-ROB projection preserved RVFI tags, but it did not yet expose
the local `InOrderTags` fact needed by `RobStepRefines`.  Added
`normalizeRvfiPacketTags`: from normalization of one packet at a supplied
starting order, its decoded `TaggedCommit` list is proved to equal the
consecutive `orderPrefix`; bubbles contribute no tag, and each valid row uses
the order equality already checked by the inductive certificate.

The PicoRV32 witness applies this theorem to the first measured two-entry
packet and proves its tag list starts at order zero.  The packet's retirement
and ROB trace proofs continue to use the same global normalization certificate.

**MEASURED:** `lake build LeanModels.Refine.RvfiPacket
Examples.«system-verilog».cores.picorv32.trace_proof` passed (24 jobs), and
`normalizeRvfiPacketTags` reports only `propext`/`Quot.sound`.
`python3 tools/docs_check.py`, `tools/backlog-index.sh --check`, and
`git diff --check` pass.  No `sorry`, new axiom, RTL edit, or SV-loader
adaptation was introduced.

**DECIDED:** retain tag certification as a proof obligation derived from the
packed stream; no sorting or completion-order choice is added.  The remaining
PicoRV32 symbolic admission walls are unchanged.

## 2026-11-05-ls-sv2-17 — thread packet tag certificates across cycles

Per-packet `InOrderTags` was available, but a cycle trace also needs the
starting order for every later packet.  Added `rvfiPacketTags` and
`InOrderPacketStream`, with `normalizeRvfiPacketTags_stream` proving that one
global normalized RVFI stream yields a consecutive tag certificate at every
packet boundary.  The proof uses the compositional normalization theorem and
the exact decoded-row count, so bubbles do not advance the order and packet
lengths cannot drift from retirement counts.

The PicoRV32 packet witness now proves the stream-level tag property for all
four measured two-entry packets, in addition to the first-packet local fact.

**MEASURED:** `lake build LeanModels.Refine.RvfiPacket
Examples.«system-verilog».cores.picorv32.trace_proof` passed (24 jobs), with
`normalizeRvfiPacketTags_stream` reporting only `propext`/`Quot.sound`.
`python3 tools/docs_check.py`, `tools/backlog-index.sh --check`, and
`git diff --check` pass.  No `sorry`, new axiom, RTL edit, or SV-loader
adaptation was introduced.

**DECIDED:** expose the packet-boundary order invariant as a reusable
certificate for `RobStepRefines`; leave completion scheduling and fairness to
the core relation.  PicoRV32's symbolic loader remains blocked at the same
memory/generate walls.

## 2026-11-05-ls-sv2-18 — compose normalized RVFI packets with ROB refinement

Added `normalizeRvfiPacketRobTrace_refines` to
`LeanModels/Refine/RvfiPacket.lean`.  Given a core-specific
`RobStepRefines` relation, its initial-state witness, and successful flattened
RVFI normalization, the theorem directly concludes that the normalized packet
retirements equal the ISA `trace` over the packet-associated inputs.  It is a
single composition of `normalizeRvfiPacketRobTrace` and the existing generic
`rob_trace_refines`; no new scheduling, fairness, or completion assumption is
introduced.

This is intentionally a generic theorem: the current PicoRV32 artifact has a
finite measured stream but no symbolic RTL relation because its loader is
still blocked.  Its packet trace and tag certificates remain the concrete
inputs a future core proof will feed to this conclusion.

**MEASURED:** `lake build LeanModels.Refine.RvfiPacket` passed (13 jobs), and
the new theorem reports only `propext`/`Quot.sound`.  `python3
tools/docs_check.py`, `tools/backlog-index.sh --check`, and `git diff --check`
pass.  No `sorry`, new axiom, RTL edit, or SV-loader adaptation was
introduced.

**DECIDED:** make this composition the reusable finish line for a packetized
RVFI/ROB core proof; leave the core relation and input admission to the
future real-core artifact.  PicoRV32's exact loader walls are unchanged.

## 2026-11-05-ls-sv2-19 — quantify PicoRV32 bus effects over latency

Added `pinned_nontrap_bus_effects` to
`Examples/system-verilog/cores/picorv32/trace_proof.lean`.  The theorem lifts
the measured PicoRV32 store/load certificate through
`runBus_oracle_projection`, so the completed effect stream is equal to the
same direct architectural effects for every `LatencyOracle`.  Timing is
therefore an explicit environment parameter; the proof does not choose a
fixed delay or infer an ordering beyond the FIFO bus contract.

**MEASURED:** `lake build
Examples.«system-verilog».cores.picorv32.trace_proof` passed (24 jobs), and
the new theorem's axiom report contains only the existing `propext` and
`Quot.sound` entries.  `python3 tools/docs_check.py`,
`tools/backlog-index.sh --check`, and `git diff --check` pass.  No `sorry`,
new axiom, RTL edit, or SV-loader adaptation was introduced.

**DECIDED:** keep latency erasure in the generic bus layer and expose only
the completed architectural effects to the PicoRV32 trace witness.  The
symbolic loader remains blocked at the unchanged unpacked-register-memory and
generate-member routes.

## 2026-11-05-ls-sv2-20 — compose tagged memory commits with timed buses

Added `taggedMemoryPacket_refines_bus` to `LeanModels/Refine/Memory.lean`.
The theorem composes a packet's exact byte-level memory certificate with
`runBus_oracle_projection`: for every `LatencyOracle`, the final memory and
the completed effect stream agree with the packet's in-order committed
requests and effects.  It preserves the packet's explicit order and does not
choose or reconstruct a completion schedule.

The toy memory witness now applies the theorem to a word store followed by
mixed-width loads, with a nonconstant latency function, through
`packet_projects_to_timed_bus` in
`Examples/system-verilog/cores/toy_rv32i/memory_proof.lean`.

**MEASURED:** `lake build LeanModels.Refine.Memory
Examples.«system-verilog».cores.toy_rv32i.memory_proof` passed (20 jobs), and
the new theorem and witness report only the existing `propext`/`Quot.sound`
entries.  `python3 tools/docs_check.py`, `tools/backlog-index.sh --check`,
and `git diff --check` pass.  No `sorry`, new axiom, RTL edit, or SV-loader
adaptation was introduced.

**DECIDED:** keep the memory packet certificate as the bridge between
arbitrary timed bus completion and architectural commit effects; later ROB
proofs can reuse it without adding a timing assumption.  The PicoRV32 loader
walls remain unchanged.

## 2026-11-05-ls-sv2-21 — add packet-boundary ROB progress

Added `packetSchedulePrefix`, `RobRetiresTarget`, and
`rob_progress_trace_refines` to `LeanModels/Refine/Progress.lean`.  The
existing progress contract is input-at-a-time; a tagged ROB may retire a
multi-instruction packet, so this contract makes target packet widths
explicit and proves the ISA trace equality at each witnessed packet boundary.
It introduces no fairness or scheduler choice: the witness remains a
quantified finite-prefix certificate.

The toy ROB witness now supplies a two-ADDI packet target, proves the emitted
input prefixes, and invokes `rob_progress_trace_refines` in
`Examples/system-verilog/cores/toy_rv32i/rob_proof.lean`.

**MEASURED:** `lake build LeanModels.Refine.Progress
Examples.«system-verilog».cores.toy_rv32i.rob_proof` passed (29 jobs), and
`rob_progress_trace_refines` plus the witness report only the existing
`propext`/`Quot.sound` entries.  `python3 tools/docs_check.py`,
`tools/backlog-index.sh --check`, and `git diff --check` pass.  No `sorry`,
new axiom, RTL edit, or SV-loader adaptation was introduced.

**DECIDED:** keep packet-width-aware progress separate from the one-input
`RetiresTarget` contract; later superscalar proofs can state liveness at the
ROB's actual commit boundaries without pretending that a partial packet was
observed.

## 2026-11-05-ls-sv2-22 — add flush-aware finite-prefix progress

Added `FlushRetiresTarget` and `flush_progress_trace_refines` to
`LeanModels/Refine/Progress.lean`.  This composes the existing
`FlushStepRefines` safety theorem with an explicit finite-prefix witness: a
flush may change core state without advancing the ISA, while every witnessed
retirement prefix still equals the corresponding ISA trace.

The toy flush witness now runs an initial speculative flush followed by a
repeated ADDI schedule, proves the filtered input prefix, and invokes the new
theorem in `Examples/system-verilog/cores/toy_rv32i/flush_proof.lean`.

**MEASURED:** `lake build LeanModels.Refine.Progress
Examples.«system-verilog».cores.toy_rv32i.flush_proof` passed (29 jobs), and
the new theorem and witness report only the existing `propext`/`Quot.sound`
entries.  `python3 tools/docs_check.py`, `tools/backlog-index.sh --check`,
and `git diff --check` pass.  No `sorry`, new axiom, RTL edit, or SV-loader
adaptation was introduced.

**DECIDED:** keep flush progress as a filtered finite-prefix contract; flush
cycles are explicit stutter in the architectural stream, and no fairness or
flush resolution is selected by the generic bridge.

## 2026-11-05-ls-sv2-23 — compose state-threaded RVFI packet windows

Added `rvfiPacketStateAfter` and
`rvfiPacketObservations_append` to `LeanModels/Refine/RvfiPacket.lean`.
These definitions carry the packet machine's post-window state explicitly;
they prove that flattening two adjacent windows neither drops nor replays a
packet.  `normalizeRvfiPacketTrace_append` then composes successful
normalization certificates, advancing the second window by the first
window's retirement count.

The PicoRV32 witness splits its four measured packets into two two-cycle
windows, proves each window's normalization (including the carried state),
and derives the combined certificate with the generic theorem.

**MEASURED:** `lake build LeanModels.Refine.RvfiPacket
Examples.«system-verilog».cores.picorv32.trace_proof` passed (24 jobs); the
state-threading theorem has no axioms, and the composition theorem and
witness report only existing `propext`/`Quot.sound` entries.  `python3
tools/docs_check.py`, `tools/backlog-index.sh --check`, and `git diff --check`
pass.  No `sorry`, new axiom, RTL edit, or SV-loader adaptation was
introduced.

**DECIDED:** keep packet-window state threading in the generic RVFI adapter;
streaming core captures must supply the carried state and the next order
explicitly, while normalization remains the sole authority for validity and
retirement order.

## 2026-11-05-ls-sv2-24 — lift packet-window composition to ROB traces

Added `normalizeRvfiPacketRobTrace_append` to
`LeanModels/Refine/RvfiPacket.lean`.  It transports the state-threaded,
order-advanced normalization composition directly to the tagged ROB
retirement stream, so a core capture can validate adjacent windows without
rebuilding one monolithic observation list.

The PicoRV32 witness now derives the concatenated two-window ROB trace from
the two local normalization certificates.

**MEASURED:** `lake build LeanModels.Refine.RvfiPacket
Examples.«system-verilog».cores.picorv32.trace_proof` passed (24 jobs), and
the new theorem/witness report only existing `propext`/`Quot.sound` entries.
`python3 tools/docs_check.py`, `tools/backlog-index.sh --check`, and `git
diff --check` pass.  No `sorry`, new axiom, RTL edit, or SV-loader adaptation
was introduced.

**DECIDED:** expose the ROB projection as a corollary of the normalized
window bridge; packet validation, state threading, and ROB retirement remain
separate proof layers.

## 2026-11-05-ls-sv2-25 — certify PicoRV32's tagged memory packet

Added a two-entry `TaggedMemoryPacket` to the pinned PicoRV32 trace witness,
with tags 1 and 2 for the measured store and load.  The new theorem
`pinned_nontrap_memory_packet` proves its exact byte-level effects and final
memory through `TaggedMemoryPacketRefines`; separate reduction lemmas identify
its requests and effects with the measured `nontrapMemoryRequests` and
`nontrapMemoryEffects`.

`pinned_nontrap_memory_packet_bus_effects` then lifts this core-specific
packet certificate through `taggedMemoryPacket_refines_bus` for every
`LatencyOracle`, connecting the measured RVFI memory rows to the timed-bus
architectural effect stream.

**MEASURED:** `lake build
Examples.«system-verilog».cores.picorv32.trace_proof` passed (25 jobs), and
the packet/effect/request theorems report only existing `propext`/`Quot.sound`
entries (the reduction lemmas have no axioms).  `python3 tools/docs_check.py`,
`tools/backlog-index.sh --check`, and `git diff --check` pass.  No `sorry`,
new axiom, RTL edit, or SV-loader adaptation was introduced.

**DECIDED:** keep the measured RVFI memory packet explicit at the core
boundary; its tags, effects, and requests are independently checked before
the generic latency theorem is applied.

## 2026-11-05-ls-sv2-26 — compose adjacent timed bus windows

Added `completed_append`, `runBus_append`, and `completed_runBus_append` to
`LeanModels/Refine/Bus.lean`.  These theorems thread the first window's final
memory into the second and preserve the two windows' response order after
timing bubbles are removed.  They make stream capture compositional without
assuming a fixed latency or reordering requests.

The toy bus witness now splits its mixed store/load request stream into two
windows, proves the timed schedule split, and applies the generic completed
window theorem in `timed_bus_windows_refine`.

**MEASURED:** `lake build LeanModels.Refine.Bus
Examples.«system-verilog».cores.toy_rv32i.bus_proof` passed (16 jobs), and the
new theorem reports only existing `propext`/`Quot.sound` entries.  `python3
tools/docs_check.py`, `tools/backlog-index.sh --check`, and `git diff --check`
pass.  No `sorry`, new axiom, RTL edit, or SV-loader adaptation was
introduced.

**DECIDED:** keep bus-window composition at the generic timed boundary;
later core proofs can validate long traces in finite windows while preserving
the explicit memory state and latency oracle.

## 2026-11-05-ls-sv2-27 — split latency schedules over arbitrary windows

Added `latencyShift` and the generic theorem `scheduleWith_append` to
`LeanModels/Refine/Bus.lean`.  The theorem decomposes the timed request stream
for any first and second windows while shifting the latency oracle by the
first window's length.  It preserves the explicit oracle parameter and makes
no fixed-delay or scheduling choice.

The toy bus witness now invokes this theorem directly for its store/load
split, so the concrete proof depends only on the measured window boundary and
the generic timed-bus composition theorem.

**MEASURED:** `lake build LeanModels.Refine.Bus
Examples.«system-verilog».cores.toy_rv32i.bus_proof` passed (16 jobs), and the
new schedule theorem reports only existing `propext`/`Quot.sound` entries.
`python3 tools/docs_check.py`, `tools/backlog-index.sh --check`, and `git diff
--check` pass.  No `sorry`, new axiom, RTL edit, or SV-loader adaptation was
introduced.

**DECIDED:** keep latency-index shifting in the generic bus scheduler;
windowed core traces must provide their own oracle, while bus composition
remains independent of any concrete latency pattern.

## 2026-11-05-ls-sv2-28 — compose tagged memory packets over timed windows

Added `taggedMemoryPacket_refines_bus_append` to
`LeanModels/Refine/Memory.lean`.  The theorem composes two independently
certified tagged memory packets, threads the first packet's final memory into
the second, and shifts the latency oracle by the first packet length.  It
proves the combined final memory and completed effect stream for every oracle
without choosing a completion order or a concrete delay pattern.

The toy memory witness now splits its four-entry store/load packet into two
windows and invokes the generic theorem, checking the packet tags and the
timed completed stream at the combined boundary.

**MEASURED:** `lake build LeanModels.Refine.Memory
Examples.«system-verilog».cores.toy_rv32i.memory_proof` passed (20 jobs), and
the new theorem reports only existing `propext`/`Quot.sound` entries.
`python3 tools/docs_check.py`, `tools/backlog-index.sh --check`, and `git diff
--check` pass.  No `sorry`, new axiom, RTL edit, or SV-loader adaptation was
introduced.

**DECIDED:** keep packet-window memory composition in the generic refinement
layer; core proofs provide explicit packet certificates and retain arbitrary
latency and completion-order witnesses at the boundary.

## 2026-11-05-ls-sv2-29 — compose state-threaded packet windows

Added `packetStateAfter`, `packetStateAfter_append`, `packetTrace_append`, and
`packetInputs_append` to `LeanModels/Refine/Packet.lean`.  These bridges carry
the packet machine's exact post-window state and compose both committed
retirements and their architectural inputs across adjacent cycle windows.

The toy wide-packet witness now applies all three append theorems to two
single-cycle windows, preserving the two-retirement packet emitted at each
boundary without replaying or dropping state.

**MEASURED:** `lake build LeanModels.Refine.Packet
Examples.«system-verilog».cores.toy_rv32i.packet_proof` passed (28 jobs).  The
state theorem has no axioms; trace/input composition reports only existing
`propext`/`Quot.sound`.  `python3 tools/docs_check.py`,
`tools/backlog-index.sh --check`, and `git diff --check` pass.  No `sorry`, new
axiom, RTL edit, or SV-loader adaptation was introduced.

**DECIDED:** keep packet-window state threading in the generic packet layer;
later ROB and RVFI proofs must carry the post-window core state explicitly
when composing finite observations.

## 2026-11-05-ls-sv2-30 — compose state-threaded ROB windows

Added `robStateAfter`, `robStateAfter_append`, `robTrace_append`, and
`robInputs_append` to `LeanModels/Refine/Rob.lean`.  These theorems preserve
the exact ROB state and committed packet/input order when two finite cycle
windows are joined, while leaving completion order inside the core relation.

The toy ROB witness applies all three append theorems to two cycles, checking
that each window's two-entry packet contributes four architectural inputs and
retirements in total.

**MEASURED:** `lake build LeanModels.Refine.Rob
Examples.«system-verilog».cores.toy_rv32i.rob_proof` passed (29 jobs).  The
state theorem has no axioms; trace/input composition reports only existing
`propext`/`Quot.sound`.  `python3 tools/docs_check.py`,
`tools/backlog-index.sh --check`, and `git diff --check` pass.  No `sorry`, new
axiom, RTL edit, or SV-loader adaptation was introduced.

**DECIDED:** keep ROB-window state threading separate from the order
certificate; window composition carries state and stream order, while each
packet still proves its own consecutive tags.

## 2026-11-05-ls-sv2-31 — compose stuttering cycle windows

Added `cycleStateAfter`, `cycleStateAfter_append`, `cycleTrace_append`, and
`retireInputs_append` to `LeanModels/Refine/Cycle.lean`.  The theorems thread
the exact state across adjacent cycle windows while preserving bubbles and
retirement-input filtering, so a stuttering window cannot replay or lose an
architectural retirement at its boundary.

The toy two-cycle pipeline witness applies all three append theorems to its
bubble/retire pair and checks the resulting one-retirement trace and input
stream.

**MEASURED:** `lake build LeanModels.Refine.Cycle
Examples.«system-verilog».cores.toy_rv32i.cycle_proof` passed (28 jobs).  The
state theorem has no axioms; trace/input composition reports only existing
`propext`/`Quot.sound`.  `python3 tools/docs_check.py`,
`tools/backlog-index.sh --check`, and `git diff --check` pass.  No `sorry`, new
axiom, RTL edit, or SV-loader adaptation was introduced.

**DECIDED:** keep cycle-window composition below packetization; stutter
behavior is retained in the cycle layer, while packet and ROB layers consume
the explicitly threaded post-window state.

## 2026-11-05-ls-sv2-32 — compose flush-aware cycle windows

Added `flushStateAfter`, `flushStateAfter_append`, `flushTrace_append`, and
`flushInputs_append` to `LeanModels/Refine/Flush.lean`.  The bridges carry
state across adjacent flush/retirement windows, preserving flush stutter and
packet input order without turning a flush into an ISA step.

The toy flush witness applies all three append theorems to its initial flush
window and following retirement window, checking the one-entry architectural
stream and its filtered input stream.

**MEASURED:** `lake build LeanModels.Refine.Flush
Examples.«system-verilog».cores.toy_rv32i.flush_proof` passed (29 jobs).  The
state theorem has no axioms; trace/input composition reports only existing
`propext`/`Quot.sound`.  `python3 tools/docs_check.py`,
`tools/backlog-index.sh --check`, and `git diff --check` pass.  No `sorry`, new
axiom, RTL edit, or SV-loader adaptation was introduced.

**DECIDED:** keep flush-window composition at the named flush boundary;
flushes remain explicit architectural stutter and packet refinement handles
only the events that actually retire.

## 2026-11-05-ls-sv2-33 — compose normalized RVFI cycle windows

Added `rvfiStateAfter`, `rvfiStateAfter_append`, `rvfiObservations_append`,
and `normalizeRvfiCycleTrace_append` to `LeanModels/Refine/Rvfi.lean`.  The
normalization bridge carries the exact post-window core state and advances
the RVFI order by the first window's retirement count before validating the
second window.

The PicoRV32 witness now splits its measured eight-cycle RVFI stream into two
four-cycle windows, proves each local normalization certificate, and invokes
the generic append theorem for the combined four-retirement result.

**MEASURED:** `lake build LeanModels.Refine.Rvfi
Examples.«system-verilog».cores.picorv32.trace_proof` passed (25 jobs).
`rvfiStateAfter_append` and `rvfiObservations_append` have no axioms; the
normalization composition and witness report only existing
`propext`/`Quot.sound`.  `python3 tools/docs_check.py`,
`tools/backlog-index.sh --check`, and `git diff --check` pass.  No `sorry`, new
axiom, RTL edit, or SV-loader adaptation was introduced.

**DECIDED:** keep RVFI order advancement at the normalization boundary;
windowed captures must provide the carried state and local certificates, and
invalid rows remain explicit bubbles rather than being repaired.

## 2026-11-05-ls-sv2-34 — compose architectural machine windows

Added `machineStateAfter`, `machineStateAfter_append`, and
`machineTrace_append` to `LeanModels/Refine/Commit.lean`.  The generic
architectural machine bridge now carries the exact post-window state and
splits a retirement trace over arbitrary adjacent input windows without any
core-specific assumptions.

The toy in-order witness applies `machineTrace_append` to two ADDI inputs,
checking the concrete architectural stream at the new generic boundary.

**MEASURED:** `lake build LeanModels.Refine.Commit
Examples.«system-verilog».cores.toy_rv32i.proof` passed (27 jobs), and both
generic append theorems report no axioms.  `python3 tools/docs_check.py`,
`tools/backlog-index.sh --check`, and `git diff --check` pass.  No `sorry`, new
axiom, RTL edit, or SV-loader adaptation was introduced.

**DECIDED:** use the architectural machine append bridge as the base state
threading law; cycle, packet, ROB, flush, and RVFI layers retain their
boundary-specific observations while sharing the same window discipline.

## 2026-11-05-ls-sv2-35 — compose stateful memory windows

Added `rvMemoryStateAfter`, `threadRvInputs_append`, and
`rvMemoryMachine_trace_append` to `LeanModels/Refine/MemoryMachine.lean`.
The stateful adapter now composes windows while carrying both the architectural
register state and the byte-addressed memory that precedes the next input.

The PicoRV32 witness splits its four non-trapping instructions into two
stateful-memory windows and applies the new bridge, so the second window reads
the memory produced by the first rather than a stale snapshot.

**MEASURED:** `lake build LeanModels.Refine.MemoryMachine
Examples.«system-verilog».cores.picorv32.trace_proof` passed (25 jobs).
`python3 tools/docs_check.py`, `tools/backlog-index.sh --check`, and `git diff
--check` pass.  The new bridge reports only existing `propext`/`Quot.sound`;
no `sorry`, new axiom, RTL edit, or SV-loader adaptation was introduced.

**DECIDED:** keep memory threading explicit at the stateful adapter; split
traces must carry the post-window memory into subsequent instruction inputs.

## 2026-11-05-ls-sv2-36 — transport refinement relations across windows

Added `machineStateAfter_refines` to `LeanModels/Refine/Commit.lean`.  A
`StepRefines` certificate now proves the simulation relation at the exact
post-state of every finite admitted input window, independently of the
retirement trace projection.

The toy in-order proof instantiates the theorem for its one-ADDI window,
showing that a later window may start from the transported relation witness
instead of rebuilding the invariant from the initial state.

**MEASURED:** `lake build LeanModels.Refine.Commit
Examples.«system-verilog».cores.toy_rv32i.proof` passed (27 jobs); the new
theorem reports only `propext`/`Quot.sound` already present in the refinement
layer.  `python3 tools/docs_check.py`, `tools/backlog-index.sh --check`, and
`git diff --check` pass.  No `sorry`, new axiom, RTL edit, or SV-loader
adaptation was introduced.

**DECIDED:** treat post-window relation transport as a separate safety lemma;
trace equality and progress remain independent obligations for a core proof.

## 2026-11-05-ls-sv2-37 — project packet certificates to final ISA state

Added `packet_refines_state` to `LeanModels/Refine/Packet.lean`.  Every
`PacketRefines` certificate now projects its final ISA state to
`machineStateAfter` over the packet's committed input sequence, so packet
proofs expose both retirement equality and the exact architectural state
needed by a following window.

The toy wide-packet witness applies the projection to its two-entry ADDI
certificate, connecting the packet final state directly to the ISA state after
the two packet inputs.

**MEASURED:** `lake build
Examples.«system-verilog».cores.toy_rv32i.packet_proof` passed (28 jobs), and
`packet_refines_state` reports no axioms.  `python3 tools/docs_check.py`,
`tools/backlog-index.sh --check`, and `git diff --check` pass.  No `sorry`, new
axiom, RTL edit, or SV-loader adaptation was introduced.

**DECIDED:** keep packet final-state projection in the generic packet layer;
packet certificates remain the source of both committed observations and the
state boundary consumed by later windows.

## 2026-11-05-ls-sv2-38 — project tagged ROB packets to final ISA state

Added `tagged_packet_refines_state` to `LeanModels/Refine/Rob.lean`.  A tagged
ROB packet now projects its final ISA state through the packet's input tags to
`machineStateAfter`, reusing the untagged packet certificate without changing
the explicit consecutive-order condition.

The toy ROB witness applies the theorem to its two-entry in-order commit
packet, connecting the ROB certificate's final state to the ISA state after
the two committed ADDIs.

**MEASURED:** `lake build LeanModels.Refine.Rob
Examples.«system-verilog».cores.toy_rv32i.rob_proof` passed (29 jobs), and
`tagged_packet_refines_state` reports only the existing `propext` dependency.
`python3 tools/docs_check.py`, `tools/backlog-index.sh --check`, and `git
diff --check` pass.  No `sorry`, new axiom, RTL edit, or SV-loader adaptation
was introduced.

**DECIDED:** keep the ROB state projection layered over `PacketRefines`; tag
validation constrains commit order while the shared packet certificate owns
the architectural state transition.

## 2026-11-05-ls-sv2-39 — transport refinement across flush windows

Added `flushStateAfter_refines` to `LeanModels/Refine/Flush.lean`.  A
`FlushStepRefines` certificate now transports the core/ISA relation across a
finite cycle window, retaining core state changes from flushes and advancing
the ISA only over the packet inputs emitted by retire events.

The toy flush proof applies the theorem to its initial flush followed by one
retirement, so the resulting relation is checked against the filtered
architectural input stream rather than against all cycle inputs.

**MEASURED:** `lake build LeanModels.Refine.Flush
Examples.«system-verilog».cores.toy_rv32i.flush_proof` passed (29 jobs), and
`flushStateAfter_refines` reports only the existing `Quot.sound` dependency.
`python3 tools/docs_check.py`, `tools/backlog-index.sh --check`, and `git
diff --check` pass.  No `sorry`, new axiom, RTL edit, or SV-loader adaptation
was introduced.

**DECIDED:** keep flush relation transport independent from trace equality;
flushes advance the core state without consuming an ISA step, while retire
packets use the shared packet state projection.

## 2026-11-05-ls-sv2-40 — transport refinement across cycle windows

Added `cycleStateAfter_refines` to `LeanModels/Refine/Cycle.lean`.  A
`CycleStepRefines` certificate now transports the relation across a finite
cycle window while filtering bubbles: stuttering cycles keep the ISA state,
and retiring cycles advance it on exactly the retained retirement inputs.

The toy two-cycle pipeline witness applies the theorem to a bubble/retirement
pair and checks the resulting relation against the filtered input stream.

**MEASURED:** `lake build LeanModels.Refine.Cycle
Examples.«system-verilog».cores.toy_rv32i.cycle_proof` passed (28 jobs), and
`cycleStateAfter_refines` reports only the existing `propext`/`Quot.sound`
dependencies.  `python3 tools/docs_check.py`, `tools/backlog-index.sh
--check`, and `git diff --check` pass.  No `sorry`, new axiom, RTL edit, or
SV-loader adaptation was introduced.

**DECIDED:** keep cycle relation transport aligned with the filtered input
semantics; bubbles are architectural stutter and never become fabricated ISA
steps.

## 2026-11-05-ls-sv2-41 — transport ROB relations and order across windows

Added `robStateAfter_refines` to `LeanModels/Refine/Rob.lean`.  The theorem
transports a `RobStepRefines` relation across a finite cycle window and
returns the final commit-order counter, proving it equals the starting order
plus the length of the emitted architectural input stream.

The toy ROB proof instantiates the result for one two-entry commit packet,
checking both the final architectural state and the order-counter accounting.

**MEASURED:** `lake build LeanModels.Refine.Rob
Examples.«system-verilog».cores.toy_rv32i.rob_proof` passed (29 jobs), and
`robStateAfter_refines` reports only existing `propext`/`Quot.sound`
dependencies.  `python3 tools/docs_check.py`, `tools/backlog-index.sh
--check`, and `git diff --check` pass.  No `sorry`, new axiom, RTL edit, or
SV-loader adaptation was introduced.

**DECIDED:** keep ROB order accounting in the state-transport theorem; the
architectural input stream, rather than physical completion order, determines
the counter advance.

## 2026-11-05-ls-sv2-42 — transport packet-machine relations across windows

Added `packetStateAfter_refines` to `LeanModels/Refine/Packet.lean`.  A
`PacketStepRefines` certificate now transports the core/ISA relation across a
finite packet-machine window, using each packet certificate to advance the ISA
over exactly its emitted inputs.

The toy wide-packet witness applies the theorem to one two-entry packet and
checks the resulting relation against the packet machine's input projection.

**MEASURED:** `lake build LeanModels.Refine.Packet
Examples.«system-verilog».cores.toy_rv32i.packet_proof` passed (28 jobs), and
`packetStateAfter_refines` reports only the existing `Quot.sound` dependency.
`python3 tools/docs_check.py`, `tools/backlog-index.sh --check`, and `git
diff --check` pass.  No `sorry`, new axiom, RTL edit, or SV-loader adaptation
was introduced.

**DECIDED:** keep packet-machine relation transport above individual packet
certificates; the emitted input stream remains the sole driver of ISA state.

## 2026-11-05-ls-sv2-43 — transport packetized RVFI state and order

Added `rvfiPacketStateAfter_refines` to `LeanModels/Refine/RvfiPacket.lean`.
It lifts the generic ROB state/order transport through the packetized RVFI
adapter, proving the final order counter against the packet machine's emitted
input stream.  The adapter also now has an explicit
`toRobMachine_stateAfter` bridge, so its retained state is not assumed
definitionally equal across projections.

The PicoRV32 witness checks this state bridge over its two packet windows,
alongside the existing normalization and ROB trace certificates.

**MEASURED:** `lake build LeanModels.Refine.RvfiPacket
Examples.«system-verilog».cores.picorv32.trace_proof` passed (25 jobs), and
the new generic state/order theorem reports only existing `propext`/`Quot.sound`
dependencies.  `python3 tools/docs_check.py`, `tools/backlog-index.sh
--check`, and `git diff --check` pass.  No `sorry`, new axiom, RTL edit, or
SV-loader adaptation was introduced.

**DECIDED:** keep packetized RVFI state transport as an adapter over the ROB
certificate; normalization validates observations and tags, while ROB
refinement supplies architectural state and order accounting.

## 2026-11-05-ls-sv2-44 — transport single-channel RVFI state

Added `RvfiCycleMachine.toCycleMachine_stateAfter` and
`rvfiStateAfter_refines` to `LeanModels/Refine/Rvfi.lean`.  The single-channel
RVFI adapter now lifts cycle relation transport to its retained packed-port
state, while bubbles continue to advance no ISA state.  The explicit adapter
equality avoids relying on definitional equality between the packed and
optional-retirement views.

The PicoRV32 witness checks the retained-state bridge over its measured RVFI
cycle stream alongside the existing normalization certificate.

**MEASURED:** `lake build LeanModels.Refine.Rvfi
Examples.«system-verilog».cores.picorv32.trace_proof` passed (25 jobs), and
the new state bridge reports no axioms while the lifted theorem reports only
existing `propext`/`Quot.sound`.  `python3 tools/docs_check.py`,
`tools/backlog-index.sh --check`, and `git diff --check` pass.  No `sorry`, new
axiom, RTL edit, or SV-loader adaptation was introduced.

**DECIDED:** keep single-channel RVFI state transport layered over the cycle
bridge; normalization remains the separate proof that packed rows are valid
architectural observations.

## 2026-11-05-ls-sv2-45 — project stateful memory to the ISA state

Added `rvMemoryStateAfter_arch` to `LeanModels/Refine/MemoryMachine.lean`.
The theorem proves that the architectural component of the stateful memory
machine after a window equals the ordinary ISA machine state after the same
window with `threadRvInputs` supplying each instruction's preceding memory.

The PicoRV32 witness applies it to the four-instruction non-trapping memory
run, alongside the existing stateful trace and memory-window laws.

**MEASURED:** `lake build LeanModels.Refine.MemoryMachine
Examples.«system-verilog».cores.picorv32.trace_proof` passed (25 jobs), and
`rvMemoryStateAfter_arch` reports only existing `propext`/`Quot.sound`
dependencies.  `python3 tools/docs_check.py`, `tools/backlog-index.sh
--check`, and `git diff --check` pass.  No `sorry`, new axiom, RTL edit, or
SV-loader adaptation was introduced.

**DECIDED:** keep stateful memory projection explicit: memory threading
determines the stateless ISA input view, while the architectural component
remains the state observed by refinement proofs.

## 2026-11-05-ls-sv2-46 — compose direct memory runs across windows

Added `directRun_append` to `LeanModels/Refine/Bus.lean`.  The untimed
byte-memory executor now composes adjacent request windows while threading the
first window's final memory and concatenating its exact effects.

The toy bus proof applies the law to a store/read request split, complementing
the existing arbitrary-latency `runBus` window theorem.

**MEASURED:** `lake build LeanModels.Refine.Bus
Examples.«system-verilog».cores.toy_rv32i.bus_proof` passed (16 jobs), and
`directRun_append` reports only existing `propext`/`Quot.sound` dependencies.
`python3 tools/docs_check.py`, `tools/backlog-index.sh --check`, and `git
diff --check` pass.  No `sorry`, new axiom, RTL edit, or SV-loader adaptation
was introduced.

**DECIDED:** keep untimed direct-run composition as the memory baseline; the
timed bus theorem can erase latency only after this state/effect split is
established.

## 2026-11-05-ls-sv2-47 — transport single-channel RVFI state through the ROB

Added `RvfiCycleMachine.toRobMachine_stateAfter` and
`rvfiRobStateAfter_refines` to `LeanModels/Refine/RvfiRob.lean`.  The
single-channel RVFI-to-ROB adapter now exposes the exact retained core state
after a cycle window, while the lifted ROB theorem carries the final commit
order counter and relates it to `retireInputs` from the ordinary cycle view.

The PicoRV32 witness checks this retained-state bridge over the measured
`pinnedCycleMachine` stream and `cycleInputs`.

**MEASURED:** `lake build LeanModels.Refine.RvfiRob
Examples.«system-verilog».cores.picorv32.trace_proof` passed (25 jobs), and the
new state/order theorem reports only the existing `propext`/`Quot.sound`
dependencies.  `python3 tools/docs_check.py`, `tools/backlog-index.sh
--check`, and `git diff --check` pass.  No `sorry`, new axiom, RTL edit, or
SV-loader adaptation was introduced.

**DECIDED:** keep single-channel RVFI state/order transport as an adapter over
the generic ROB certificate; packet contents remain observational while the
retired-input projection determines architectural state and order advance.

## 2026-11-05-ls-sv2-48 — compose normalized single-channel RVFI ROB windows

Added `normalizeRvfiRobTrace_append` to `LeanModels/Refine/RvfiRob.lean`.
Two adjacent single-channel RVFI windows can now be normalized at the carried
RVFI order and projected through the ROB adapter as one concatenated retirement
stream, with the first window's retained state feeding the second certificate.

The PicoRV32 witness applies the theorem to `cycleFirstInputs` and
`cycleSecondInputs`, proving the concatenated ROB stream equals the two measured
retirement chunks.

**MEASURED:** `lake build LeanModels.Refine.RvfiRob
Examples.«system-verilog».cores.picorv32.trace_proof` passed (25 jobs), and the
new composition theorem reports only the existing `propext`/`Quot.sound`
dependencies.  `python3 tools/docs_check.py`, `tools/backlog-index.sh
--check`, and `git diff --check` pass.  No `sorry`, new axiom, RTL edit, or
SV-loader adaptation was introduced.

**DECIDED:** keep normalization composition above the ROB adapter: order
certificates and retained state determine the concatenated stream, while the
adapter only transports each validated retirement into tagged commits.

## 2026-11-05-ls-sv2-49 — connect normalized single-channel ROB traces to ISA

Added `normalizeRvfiRobTrace_refines` to `LeanModels/Refine/RvfiRob.lean`.
Given a core-specific `RobStepRefines` certificate, successful normalization of
a packed single-channel RVFI window now concludes that its retirement stream
equals the ISA trace over the ROB-projected inputs.

The PicoRV32 witness checks the corresponding ROB-to-ISA trace equality for
the measured four-instruction stream, using the existing normalization and
input projections.

**MEASURED:** `lake build LeanModels.Refine.RvfiRob
Examples.«system-verilog».cores.picorv32.trace_proof` passed (25 jobs), and the
new reusable theorem reports only the existing `propext`/`Quot.sound`
dependencies.  `python3 tools/docs_check.py`, `tools/backlog-index.sh
--check`, and `git diff --check` pass.  No `sorry`, new axiom, RTL edit, or
SV-loader adaptation was introduced.

**DECIDED:** keep the normalized RVFI certificate and the ROB refinement
certificate as separate obligations; their composition is the reusable R1 to
R3 boundary and does not reinterpret or repair packed observations.

## 2026-11-05-ls-sv2-50 — certify normalized single-channel ROB counts

Added `robTrace_length_eq_robInputs_length` to `LeanModels/Refine/Rob.lean`
and `normalizeRvfiRobTrace_input_length` to
`LeanModels/Refine/RvfiRob.lean`.  The generic ROB projections now prove that
each tagged retirement contributes exactly one retained input, and a successful
single-channel RVFI normalization connects that input count to the checked
retirement count.

The PicoRV32 witness applies the normalized count theorem to its measured
four-instruction cycle stream.

**MEASURED:** `lake build LeanModels.Refine.Rob LeanModels.Refine.RvfiRob
Examples.«system-verilog».cores.picorv32.trace_proof` passed (25 jobs), and the
new count theorems report only the existing `propext`/`Quot.sound` dependencies.
`python3 tools/docs_check.py`, `tools/backlog-index.sh --check`, and `git diff
--check` pass.  No `sorry`, new axiom, RTL edit, or SV-loader adaptation was
introduced.

**DECIDED:** derive ROB order advancement from validated retirement cardinality;
bubbles and refused observations contribute to neither projection, so no
unchecked length or hidden repair enters the order certificate.

## 2026-11-05-ls-sv2-51 — combine normalized RVFI state and order transport

Added `rvfiRobStateAfter_refines_normalized` to
`LeanModels/Refine/RvfiRob.lean`.  A `RobStepRefines` relation transported over
a single-channel RVFI window now returns a final related state whose order
counter is exactly `start + retirements.length` when the packed window has
successfully normalized.

The PicoRV32 witness checks the corresponding zero-based order offset for its
measured four-retirement stream.

**MEASURED:** `lake build LeanModels.Refine.RvfiRob
Examples.«system-verilog».cores.picorv32.trace_proof` passed (25 jobs), and the
combined state/order theorem reports only the existing `propext`/`Quot.sound`
dependencies.  `python3 tools/docs_check.py`, `tools/backlog-index.sh
--check`, and `git diff --check` pass.  No `sorry`, new axiom, RTL edit, or
SV-loader adaptation was introduced.

**DECIDED:** make normalization the source of the order-count equality while
retaining the generic ROB relation and state transport as independent proof
obligations.

## 2026-11-05-ls-sv2-52 — certify single-channel RVFI order tags

Added the recursive `rvfiRobTags` projection and
`normalizeRvfiRobTags` to `LeanModels/Refine/RvfiRob.lean`.  The projection
retains each valid retirement's RVFI order, source input, and architectural
retirement; successful normalization now proves that the flattened tagged
stream is an in-order prefix, while bubbles and malformed rows contribute no
ROB entry.  The theorem reports only the existing `propext`/`Quot.sound`
dependencies.

The PicoRV32 witness adds `pinned_cycle_tags`, certifying the order tags over
the measured four-retirement cycle stream.

**MEASURED:** `lake build LeanModels.Refine.RvfiRob
Examples.«system-verilog».cores.picorv32.trace_proof` passed (25 jobs).
`python3 tools/docs_check.py`, `tools/backlog-index.sh --check`, and `git diff
--check` pass.  No `sorry`, new axiom, RTL edit, or SV-loader adaptation was
introduced.

**DECIDED:** keep tag certification as a normalization-side obligation over
the flattened RVFI stream; the ROB adapter preserves the packed order and
does not repair malformed observations.

## 2026-11-05-ls-sv2-53 — compose single-channel RVFI tag streams

Added `orderPrefix_add` and `inOrderTags_append` to
`LeanModels/Refine/Rob.lean`, making consecutive tag certificates compositional
at an explicit packet-width boundary.  `LeanModels/Refine/RvfiRob.lean` now
adds `rvfiRobTags_append` for state-threaded tagged-stream composition,
`rvfiRobTags_length` for the decoded-retirement cardinality, and
`normalizeRvfiRobTags_append` for combining two local normalization
certificates into one in-order certificate over the concatenated window.

The PicoRV32 witness proves both the structural tag-stream split and the
in-order certificate over its measured first and second cycle windows.

**MEASURED:** `lake build LeanModels.Refine.Rob LeanModels.Refine.RvfiRob
Examples.«system-verilog».cores.picorv32.trace_proof` passed (25 jobs), and
the new theorems report only the existing `propext`/`Quot.sound` dependencies.
`python3 tools/docs_check.py`, `tools/backlog-index.sh --check`, and `git diff
--check` pass.  No `sorry`, new axiom, RTL edit, or SV-loader adaptation was
introduced.

**DECIDED:** carry tag-stream boundaries through the packed RVFI state and
retirement count; local order certificates compose only after the first
window's exact decoded width is established.

## 2026-11-05-ls-sv2-54 — compose normalized RVFI windows through ISA refinement

Added `normalizeRvfiRobTrace_refines_append` to
`LeanModels/Refine/RvfiRob.lean`.  Two adjacent single-channel RVFI
normalization certificates now compose through the ROB adapter and its
`RobStepRefines` contract, concluding that the concatenated normalized
retirements equal the ISA trace over the concatenated ROB input stream.

The PicoRV32 witness applies the theorem to the measured first and second
cycle windows, with the adapter's exact state threading at the boundary.

**DECIDED:** keep the composition theorem above the adapter-specific
normalization law; ISA refinement consumes the complete concatenated ROB input
projection after each local window has been checked.

## 2026-11-05-ls-sv2-55 — compose packetized RVFI windows through ISA refinement

Added `normalizeRvfiPacketRobTrace_refines_append` to
`LeanModels/Refine/RvfiPacket.lean`.  Adjacent packetized RVFI windows now
compose through the packet-to-ROB adapter and a `RobStepRefines` certificate,
with the concatenated normalized retirements equal to the ISA trace over the
concatenated ROB input stream.

The PicoRV32 witness exposes the same result for its measured packet windows,
leaving the core-specific relation and admission predicate explicit for the
eventual hardware proof.

**DECIDED:** keep packet-window state threading in the adapter theorem and
reuse the generic ROB trace refinement for the final ISA equality.

## 2026-11-05-ls-sv2-56 — compose packetized RVFI tag streams

Added `packetStreamLength`, `inOrderPacketStream_append`,
`rvfiPacketTags_append`, and `rvfiPacketTags_length` to
`LeanModels/Refine/RvfiPacket.lean`.  The new
`normalizeRvfiPacketTags_stream_append` theorem combines local packet-stream
order certificates across adjacent windows, using the first window's exact
decoded retirement count as the second window's order boundary.

The PicoRV32 witness proves the composed packet tag stream is in order over
its measured first and second packet-cycle windows.

**DECIDED:** retain packet boundaries for local ROB certificates while using
the flattened normalization count to connect packet widths to RVFI order.

## 2026-11-05-ls-sv2-57 — flatten packetized RVFI order certificates

Added `inOrderPacketStream_flatten` and
`normalizeRvfiPacketTags_flat` to `LeanModels/Refine/RvfiPacket.lean`.
Packet-boundary order certificates now lift directly to the flattened tagged
ROB stream, preserving the same global order prefix.  The PicoRV32 witness
checks the flattened certificate over the complete measured packet stream.

**DECIDED:** keep packet boundaries available for packet-aware proofs, with a
single explicit flattening bridge for generic ROB consumers.

## 2026-11-05-ls-sv2-58 — expose flattened packet tags through the generic ROB view

Added `robTags` and `robTags_append` to `LeanModels/Refine/Rob.lean` for the
flattened tagged stream emitted over a finite ROB window.  The packetized RVFI
adapter now proves that its generic ROB tag stream is exactly the flattening
of `rvfiPacketTags`, and `normalizeRvfiPacketRobTags` lifts a successful
packet normalization certificate to that generic stream.  The PicoRV32
witness checks the resulting `InOrderTags` certificate on `toRobMachine`.

**DECIDED:** expose one generic flattened ROB tag stream so packet-aware and
generic ROB proofs share the same order certificate without changing packet
contents or selecting a completion order.

## 2026-11-05-ls-sv2-59 — compose packet tags through the generic ROB stream

Added `robTags_length_eq_robInputs_length` to the generic ROB layer and
`normalizeRvfiPacketRobTags_append` to the packetized RVFI adapter.  Adjacent
packet windows now compose their generic flattened `InOrderTags` certificate
using the first window's normalized retirement width as the second window's
order boundary.  The PicoRV32 witness checks the composed certificate over
the measured first and second packet windows.

**DECIDED:** derive generic ROB tag-window composition from normalized
retirement cardinality; packet boundaries remain available to packet-aware
proofs, while the generic stream sees the same in-order prefix.

## 2026-11-06-ls-sv2-60 — project generic ROB tags to architectural streams

Added `robTags_retirements` and `robTags_inputs` to the generic ROB layer.
Mapping the flattened tagged stream now recovers exactly the existing
retirement and source-input projections.  The PicoRV32 witness checks both
equalities for the packetized four-retirement stream.

**DECIDED:** keep tag metadata as an observational refinement layer whose
retirement and input erasures are definitionally aligned with the ROB
architectural projections.

## 2026-11-06-ls-sv2-61 — derive global ROB tag order from refinement

Added `robTags_in_order_of_refines` to `LeanModels/Refine/Rob.lean`.  A
`RobStepRefines` certificate now inductively lifts each packet's local
`InOrderTags` proof across the threaded order boundary to the complete
flattened stream.  The PicoRV32 trace witness exposes the result as a
parameterized theorem over its eventual core relation and admission predicate.

**DECIDED:** retain order as a proof obligation of the ROB refinement
relation; the flattened tag stream is certified by the same relation rather
than by a second scheduling or completion-order choice.

## 2026-11-06-ls-sv2-62 — compose normalized packet tags with ISA refinement

Added `normalizeRvfiPacketRobTags_refines` to
`LeanModels/Refine/RvfiPacket.lean`.  A successful packet normalization and a
`RobStepRefines` certificate now jointly state global `InOrderTags` and the
equality of the tagged retirement projection with the ISA trace over retained
ROB inputs.  The PicoRV32 witness exposes the combined theorem over its
abstract relation and admission predicate.

**DECIDED:** keep tag-order admission and architectural refinement as separate
proof components while providing one conjunction for consumers that need the
complete tagged retirement contract.

## 2026-11-06-ls-sv2-63 — transport normalized packet order through state refinement

Added `rvfiPacketStateAfter_refines_normalized` to
`LeanModels/Refine/RvfiPacket.lean`.  With a successful packet normalization,
the state-threaded packet/ISA relation now returns a final related state whose
order is exactly the starting order plus the normalized retirement count.  The
PicoRV32 witness exposes the resulting existential state/order theorem.

**DECIDED:** derive the final order increment from the packet adapter's exact
retained-input length and the normalized retirement stream; no packet or
completion order is inferred from an unvalidated observation.

## 2026-11-06-ls-sv2-64 — compose normalized packet state across windows

Added `rvfiPacketStateAfter_refines_normalized_append` to
`LeanModels/Refine/RvfiPacket.lean`.  Two adjacent packet normalization
certificates now compose through the state-threaded packet/ISA relation, with
the final order equal to the starting order plus the concatenated retirement
count.  The PicoRV32 witness pins the result over its measured first and
second packet windows.

**DECIDED:** compose state/order transport only through the explicit
normalization append certificate, retaining the first window's state boundary
and the second window's carried retirement offset.

## 2026-11-06-ls-sv2-65 — compose the packet tag/ISA contract across windows

Added `normalizeRvfiPacketRobTags_refines_append` to
`LeanModels/Refine/RvfiPacket.lean`.  Adjacent normalized packet windows now
compose the combined contract: the flattened generic ROB tags remain in order
and their retirement projection equals the ISA trace over the concatenated
retained inputs.  The PicoRV32 witness pins the result over both measured
packet windows.

**DECIDED:** reuse the normalized trace append certificate as the sole window
composition boundary; tag order and ISA equality remain jointly observable
without introducing a completion-order selection.

## 2026-11-06-ls-sv2-66 — expose the complete packet-window refinement contract

Added `normalizeRvfiPacketRobTags_refines_state_append` to
`LeanModels/Refine/RvfiPacket.lean`.  The two-window certificate now exposes
one conjunction containing global tagged ROB order, tagged retirement equality
with the ISA trace, the final related packet/ISA state, and the exact carried
order increment.  The PicoRV32 witness pins this complete result over its
measured first and second packet windows.

**DECIDED:** keep the tag/ISA stream equality and state/order transport as
separate proof components internally, then expose their conjunction as the
consumer-facing packet-window contract.

## 2026-11-06-ls-sv2-67 — expose the single-window packet refinement contract

Added `normalizeRvfiPacketRobTags_refines_state` to
`LeanModels/Refine/RvfiPacket.lean`.  A single normalized packet capture now
has one consumer-facing certificate containing global tagged ROB order, tagged
retirement equality with the ISA trace, the final related packet/ISA state,
and the exact order increment.  The PicoRV32 witness pins this contract over
the complete four-retirement packet trace.

**DECIDED:** provide the single-window conjunction directly while retaining
the existing stream and state theorems as the independently reusable proof
components.

## 2026-11-06-ls-sv2-68 — generalize packet refinement to finite window chains

Added `normalizeRvfiPacketWindows` and
`normalizeRvfiPacketWindows_flatten` to `LeanModels/Refine/RvfiPacket.lean`.
An arbitrary finite list of packet windows now carries its own state and order
boundaries, rejects mismatched retirement lists, and flattens to one exact
normalization certificate.  `normalizeRvfiPacketRobTags_refines_windows`
reuses that certificate to expose the complete tagged ROB/ISA and final
state/order contract for the whole chain.  The PicoRV32 witness pins the
two-window chain through the new generic route.

**DECIDED:** represent streamed captures as an inductive window chain and
flatten only after every local normalization has supplied its carried state
and order boundary; no completion or packet order is reconstructed.

## 2026-11-06-ls-sv2-69 — compose independently certified packet window chains

Added `normalizeRvfiPacketWindows_append` to
`LeanModels/Refine/RvfiPacket.lean`.  Two independently normalized finite
window chains now compose when the second starts from the first chain's
retained state and flattened retirement count.  The PicoRV32 witness proves
the same two-window certificate through the append theorem, alongside the
direct chain proof.

**DECIDED:** make chain composition explicit at the window-certificate
boundary; the append theorem carries state and order rather than inferring
either from flattened observations.

## 2026-11-06-ls-sv2-70 — lift window-chain append through ISA refinement

Added `normalizeRvfiPacketRobTags_refines_windows_append` to
`LeanModels/Refine/RvfiPacket.lean`.  Two independently certified packet
chains now compose directly into the complete contract: global tagged ROB
order, ISA retirement equality, final related state, and exact flattened
retirement order.  The PicoRV32 witness exercises the full append route over
the two singleton window chains.

**DECIDED:** reuse the local chain append certificate as the sole composition
step, then apply the generic flattened refinement theorem once at the combined
boundary.

## 2026-11-06-ls-sv2-71 — preserve packet boundaries across window chains

Added `normalizeRvfiPacketWindows_tags_stream` to
`LeanModels/Refine/RvfiPacket.lean`.  A finite chain certificate now also
proves `InOrderPacketStream` for the flattened cycle packets, preserving
packet-local order boundaries alongside the generic flattened ROB contract.
The PicoRV32 witness pins this packet-aware stream result over its two-window
chain.

**DECIDED:** derive packet-boundary order only from the same flattened
normalization certificate; no second packet ordering or completion choice is
introduced.

## 2026-11-06-ls-sv2-72 — compose packet streams across certified chains

Added `normalizeRvfiPacketWindows_tags_stream_append` to
`LeanModels/Refine/RvfiPacket.lean`.  Two independently certified window
chains now compose directly at the packet-aware boundary, preserving
`InOrderPacketStream` for the concatenated cycle packets.  The PicoRV32
witness exercises this append theorem over the two singleton windows.

**DECIDED:** compose packet-local order through the same state/order-carrying
window append certificate; the packet stream is never sorted or reconstructed
from completion order.

## 2026-11-06-ls-sv2-73 — expose flattened tags from packet window chains

Added `normalizeRvfiPacketWindows_tags_flat` to
`LeanModels/Refine/RvfiPacket.lean`.  The packet-aware chain certificate now
projects directly to a global `InOrderTags` proof after packet boundaries are
erased.  The PicoRV32 witness pins the flattened tag prefix over its complete
two-window capture.

**DECIDED:** obtain the flat tag certificate by the established
`InOrderPacketStream` erasure theorem; no independent tag scan or completion
ordering is introduced.

## 2026-11-06-ls-sv2-74 — compose flattened tags across window chains

Added `normalizeRvfiPacketWindows_tags_flat_append` to
`LeanModels/Refine/RvfiPacket.lean`.  Two independently certified window
chains now produce the global flattened `InOrderTags` certificate directly at
their append boundary.  The PicoRV32 witness exercises this flat append route
over the two singleton windows.

**DECIDED:** derive the flattened append result through chain composition and
packet-boundary erasure, retaining the established state/order carry.

## 2026-11-06-ls-sv2-75 — expose flattened ROB traces from packet window chains

Added `normalizeRvfiPacketWindows_rob_trace` to
`LeanModels/Refine/RvfiPacket.lean`.  A finite chain of packet-window
normalization certificates now exposes the exact flattened `robTrace` equality
against the flattened retirement windows, erasing packet boundaries only after
all carried state and order checks have succeeded.  The PicoRV32 witness
pins this route over its two certified packet windows.

**DECIDED:** derive the ROB trace through the existing flattened observation
certificate and packet projection theorem; no independent packet scan or
completion ordering is introduced.

## 2026-11-06-ls-sv2-76 — compose flattened ROB traces across window chains

Added `normalizeRvfiPacketWindows_rob_trace_append` to
`LeanModels/Refine/RvfiPacket.lean`.  Two independently certified packet
window chains now compose directly to the exact flattened `robTrace` equality,
with the second chain starting from the first chain's retained state and
retirement-order boundary.  The PicoRV32 witness exercises the append route
over its two singleton windows.

**DECIDED:** compose through `normalizeRvfiPacketWindows_append` and the
chain-level ROB trace projection; no packet completion order or independent
trace reconstruction is introduced.

## 2026-11-06-ls-sv2-77 — expose generic ROB tags from packet window chains

Added `normalizeRvfiPacketWindows_rob_tags` to
`LeanModels/Refine/RvfiPacket.lean`.  A certified finite packet-window chain
now projects directly to the generic `robTags` order certificate, reusing the
packet-aware flattened tag theorem and the exact packet-to-ROB projection.  The
PicoRV32 witness pins the generic ROB tag route over its two-window chain.

**DECIDED:** expose generic ROB tags by definitional projection from the
packet-aware tags; no second order scan or completion ordering is introduced.

## 2026-11-06-ls-sv2-78 — compose generic ROB tags across window chains

Added `normalizeRvfiPacketWindows_rob_tags_append` to
`LeanModels/Refine/RvfiPacket.lean`.  Two certified packet-window chains now
compose directly to the generic `robTags` order certificate after flattening
their packet boundaries.  The PicoRV32 witness exercises the append route over
its two singleton windows.

**DECIDED:** derive the generic tag result through chain certification and the
packet-to-ROB projection; no independent order scan or completion ordering is
introduced.

## 2026-11-06-ls-sv2-79 — expose ROB retirement payloads from packet chains

Added `normalizeRvfiPacketWindows_rob_tags_retirements` to
`LeanModels/Refine/RvfiPacket.lean`.  A certified packet-window chain now
proves that mapping retirement payloads from its generic `robTags` stream is
exactly the flattened retirement-window result accepted by normalization.  The
PicoRV32 witness pins this payload projection over its two-window chain.

**DECIDED:** derive payload equality through the existing ROB tag erasure and
flattened ROB trace bridge; no independent retirement extraction or completion
ordering is introduced.

## 2026-11-06-ls-sv2-80 — compose ROB retirement payloads across chains

Added `normalizeRvfiPacketWindows_rob_tags_retirements_append` to
`LeanModels/Refine/RvfiPacket.lean`.  Two independently certified packet-window
chains now compose directly to equality between the flattened generic ROB
retirement payloads and the concatenated retirement windows.  The PicoRV32
witness exercises this append route over its two singleton windows.

**DECIDED:** compose through the finite-window certificate and the existing ROB
payload projection; no independent retirement extraction or completion order is
introduced.

## 2026-11-06-ls-sv2-81 — connect ROB tag inputs to packet inputs

Added `RvfiPacketMachine.toRobMachine_tags_inputs` to
`LeanModels/Refine/RvfiPacket.lean`.  Mapping source inputs from the flattened
generic `robTags` stream now equals the packet machine's retained `packetInputs`
stream, reusing the existing packet-to-ROB projections.  The PicoRV32 witness
pins this input bridge over the certified two-window capture.

**DECIDED:** retain the packet machine's explicit input threading as the sole
source of ROB inputs; no input order or completion order is inferred.

## 2026-11-06-ls-sv2-82 — certify ROB tag cardinality for packet chains

Added `normalizeRvfiPacketWindows_rob_tags_length` to
`LeanModels/Refine/RvfiPacket.lean`.  A certified finite packet-window chain
now proves that the flattened generic ROB tag count equals the flattened
normalized retirement count, making the exact carried order increment explicit.
The PicoRV32 witness pins this cardinality over its two-window capture.

**DECIDED:** derive cardinality from the certified retirement payload equality;
no truncation, padding, or inferred completion order is introduced.

## 2026-11-06-ls-sv2-83 — certify ROB tag input cardinality

Added `normalizeRvfiPacketWindows_rob_tags_inputs_length` to
`LeanModels/Refine/RvfiPacket.lean`.  A certified packet-window chain now
proves that the mapped source inputs of its flattened generic ROB tags have the
same cardinality as the normalized retirement windows.  The PicoRV32 witness
pins this input-count contract over its two-window capture.

**DECIDED:** derive input cardinality from the tag cardinality theorem and
`List.length_map`; the packet input stream remains explicitly threaded and no
padding, truncation, or completion order is inferred.

## 2026-11-06-ls-sv2-84 — expose packet-chain ISA trace equality

Added `normalizeRvfiPacketWindows_rob_trace_refines` to
`LeanModels/Refine/RvfiPacket.lean`.  A certified finite packet-window chain
now exposes the exact equality between its flattened normalized retirement
payload and the ISA trace driven by the corresponding flattened generic ROB
inputs.  The PicoRV32 witness pins this refinement route over its two certified
packet windows.

**DECIDED:** derive the ISA trace equality from the existing ROB refinement
contract and certified packet retirement projection; no independent trace
reconstruction, scheduling, or completion order is introduced.

## 2026-11-06-ls-sv2-85 — compose packet-chain ISA trace equality

Added `normalizeRvfiPacketWindows_rob_trace_refines_append` to
`LeanModels/Refine/RvfiPacket.lean`.  Two independently certified packet
window chains now compose directly to the ISA trace equality, with the second
chain starting from the first chain's retained state and retirement-order
boundary.  The PicoRV32 witness exercises this append route over its two
singleton packet windows.

**DECIDED:** compose through `normalizeRvfiPacketWindows_append` and the
single-chain ISA trace theorem; no independent trace reconstruction,
scheduling, or completion order is introduced.

## 2026-11-06-ls-sv2-86 — expose packet-facing ISA trace equality

Added `normalizeRvfiPacketWindows_trace_refines` to
`LeanModels/Refine/RvfiPacket.lean`.  A certified packet-window chain now
exposes the exact equality between its flattened normalized retirement payload
and the ISA trace over the packet machine's architectural input stream,
without requiring callers to name the intermediate generic ROB projection.
The PicoRV32 witness pins this packet-facing contract over its two certified
packet windows.

**DECIDED:** transport the established ROB trace refinement through the exact
`toRobMachine_inputs` projection; no input stream is reconstructed or reordered.

## 2026-11-06-ls-sv2-87 — compose packet-facing ISA trace equality

Added `normalizeRvfiPacketWindows_trace_refines_append` to
`LeanModels/Refine/RvfiPacket.lean`.  Two independently certified packet
window chains now compose directly to the ISA trace equality over the packet
machine's architectural input stream, retaining the first chain's state and
retirement-order boundary.  The PicoRV32 witness pins this append route over
its two singleton packet windows.

**DECIDED:** compose through the finite window-chain certificate and the
packet-facing single-chain theorem; no input stream is reconstructed,
reordered, or inferred.

## 2026-11-06-ls-sv2-88 — expose packet-chain state refinement

Added `normalizeRvfiPacketWindows_refines_state` to
`LeanModels/Refine/RvfiPacket.lean`.  A certified finite packet-window chain
now exposes its final packet/ISA related state together with the exact order
increment equal to the flattened normalized retirement count, directly over
the packet machine's architectural input stream.  The PicoRV32 witness pins
this state/order contract over its two certified packet windows.

**DECIDED:** project the state/order component of the existing complete
window-chain contract; no tag stream, input order, or final state is inferred.

## 2026-11-06-ls-sv2-89 — compose packet-chain state refinement

Added `normalizeRvfiPacketWindows_refines_state_append` to
`LeanModels/Refine/RvfiPacket.lean`.  Two independently certified packet
window chains now compose directly to the final packet/ISA related state and
exact order increment over the packet machine's architectural input stream,
with the second chain starting from the first chain's retained state and
retirement-order boundary.  The PicoRV32 witness pins this append route over
its two singleton packet windows.

**DECIDED:** compose through the finite window-chain certificate and its
packet-facing state projection; no tag stream, input order, or final state is
inferred.

## 2026-11-06-ls-sv2-90 — expose the complete packet-facing chain contract

Added `normalizeRvfiPacketWindows_refines` to
`LeanModels/Refine/RvfiPacket.lean`.  A certified finite packet-window chain
now exposes one packet-facing contract containing normalized retirement
equality with the ISA trace over packet inputs, the final related state, and
the exact retirement-order increment.  The PicoRV32 witness pins this
consumer-facing contract over its two certified packet windows.

**DECIDED:** combine the independently reusable packet-facing trace and
state/order theorems; no tag stream, input order, or final state is inferred.

## 2026-11-06-ls-sv2-91 — compose the complete packet-facing chain contract

Added `normalizeRvfiPacketWindows_refines_append` to
`LeanModels/Refine/RvfiPacket.lean`.  Two independently certified packet
window chains now compose directly to the complete packet-facing contract:
normalized retirement equality with the ISA trace over packet inputs, the
final related state, and the exact retirement-order increment.  The PicoRV32
witness pins this append route over its two singleton packet windows.

**DECIDED:** compose through `normalizeRvfiPacketWindows_append` and the
single-chain packet-facing contract; no tag stream, input order, or final
state is inferred.

## 2026-11-06-ls-sv2-92 — expose the single packet refinement contract

Added `normalizeRvfiPacketRefines` to `LeanModels/Refine/RvfiPacket.lean`.
A single normalized packet window now exposes one direct packet-facing
contract: its retirement payload equals the ISA trace over `packetInputs`, and
the retained packet state is related to the ISA state with the exact
retirement-order increment. The PicoRV32 witness pins this direct contract
over its four-cycle packet capture.

**DECIDED:** combine the existing packet ROB trace refinement with the
normalized state/order theorem, then transport inputs through the exact
`toRobMachine_inputs` projection; no input stream is reconstructed or
reordered.

## 2026-11-06-ls-sv2-93 — compose the single packet refinement contract

Added `normalizeRvfiPacketRefines_append` to
`LeanModels/Refine/RvfiPacket.lean`. Two adjacent normalized packet windows
now compose directly to the packet-facing contract: concatenated retirements
equal the ISA trace over concatenated packet inputs, and the retained final
packet state is related to the ISA state with the exact combined order
increment. The PicoRV32 witness pins this append route over its two packet
windows.

**DECIDED:** compose through the normalized packet trace append theorem and
the single-window packet refinement contract; the second window's state and
retirement boundary remain explicit.

## 2026-11-06-ls-sv2-94 — expose single packet ISA trace equality

Added `normalizeRvfiPacketTrace_refines` to
`LeanModels/Refine/RvfiPacket.lean`. A normalized packet capture now exposes
its retirement payload directly as the ISA trace over the packet machine's
retained input stream, without requiring consumers to unpack the complete
state/order contract. The PicoRV32 witness pins this projection over its
four-cycle packet capture.

**DECIDED:** transport the existing ROB trace refinement through the exact
`toRobMachine_inputs` equality; the state relation remains available through
the complete packet contract and no input stream is reconstructed.

## 2026-11-06-ls-sv2-95 — compose single packet ISA trace equality

Added `normalizeRvfiPacketTrace_refines_append` to
`LeanModels/Refine/RvfiPacket.lean`. Two adjacent normalized packet windows
now compose directly to the packet-facing ISA trace equality over their
concatenated retained inputs. The PicoRV32 witness pins this append route over
its first and second packet windows.

**DECIDED:** compose through the normalized packet trace append certificate
and the trace-only packet projection; the carried state and retirement offset
remain explicit at the normalization boundary.

## 2026-11-06-ls-sv2-96 — expose single packet state refinement

Added `normalizeRvfiPacketState_refines` to
`LeanModels/Refine/RvfiPacket.lean`. A normalized packet capture now exposes
its final packet/ISA state relation and exact retirement-order increment
directly, without requiring consumers to unpack the complete trace contract.
The PicoRV32 witness pins this state/order projection over its four-cycle
packet capture.

**DECIDED:** reuse the existing normalized state transport theorem; the
packet input stream and retirement count remain explicitly threaded, with no
state reconstruction or order inference.

## 2026-11-06-ls-sv2-97 — compose single packet state refinement

Added `normalizeRvfiPacketState_refines_append` to
`LeanModels/Refine/RvfiPacket.lean`. Two adjacent normalized packet windows
now compose directly to the final packet/ISA state relation and exact combined
retirement-order increment. The PicoRV32 witness pins this state/order append
route over its first and second packet windows.

**DECIDED:** compose through the existing normalized state transport append
theorem; both window state transitions and the carried retirement offset stay
explicit.

## 2026-11-06-ls-sv2-98 — certify normalized packet input cardinality

Added `normalizeRvfiPacketInputs_length` to
`LeanModels/Refine/RvfiPacket.lean`. A successful packet normalization now
proves that the packet machine's retained architectural input stream has
exactly the normalized retirement cardinality. The PicoRV32 witness pins this
cardinality over its four-cycle packet capture.

**DECIDED:** derive the length through the exact packet-to-ROB input
projection and the generic ROB trace-length theorem; no padding, truncation,
or inferred completion order is introduced.

## 2026-11-06-ls-sv2-99 — compose normalized packet input cardinality

Added `normalizeRvfiPacketInputs_length_append` to
`LeanModels/Refine/RvfiPacket.lean`. Adjacent normalized packet windows now
compose directly to the exact combined cardinality of their retained packet
inputs and retirement payloads. The PicoRV32 witness pins this append
cardinality over its first and second packet windows.

**DECIDED:** use the packet input append theorem and the two local normalized
length certificates; the second window's state remains explicit and no
padding, truncation, or completion order is inferred.

## 2026-11-06-ls-sv2-100 — expose packet state-after projection

Added `RvfiPacketMachine.toPacketMachine_stateAfter` to
`LeanModels/Refine/RvfiPacket.lean`.  The packet-machine projection now
exposes the same retained state as the packetized RVFI view through a reusable
theorem, and the normalized input-cardinality append proof consumes that
bridge directly.  The PicoRV32 witness pins the projection over its two
packet windows.

**DECIDED:** expose the definitional state-threading equality once and reuse
it; no packet contents or retirement order are reconstructed at the bridge.

## 2026-11-06-ls-sv2-101 — expose packet-projected state refinement

Added `normalizeRvfiPacketState_refines_packet` and
`normalizeRvfiPacketState_refines_packet_append` to
`LeanModels/Refine/RvfiPacket.lean`.  The normalized state/order contract can
now be consumed directly through `packetStateAfter machine.toPacketMachine`,
for one window or two adjacent windows, while retaining the exact retirement
order increment.  The PicoRV32 witness pins both projections.

**DECIDED:** derive the packet-state statements only through the reusable
state-after bridge; no second state relation or packet reconstruction is
introduced.

## 2026-11-06-ls-sv2-102 — expose packet-projected refinement contract

Added `normalizeRvfiPacketRefines_packet` to
`LeanModels/Refine/RvfiPacket.lean`.  The complete normalized packet contract
now exposes both its ISA trace equality and its final state/order relation
through `packetStateAfter machine.toPacketMachine`.  The PicoRV32 witness pins
this direct projected contract.

**DECIDED:** transport only the state conjunct through the shared
`toPacketMachine_stateAfter` equality; the trace conjunct and retirement order
remain exactly those of the existing contract.

## 2026-11-06-ls-sv2-103 — compose projected packet refinement contract

Added `normalizeRvfiPacketRefines_packet_append` to
`LeanModels/Refine/RvfiPacket.lean`.  Two adjacent normalized packet windows
now compose into one complete contract stated over the generic packet-machine
state: concatenated retirements equal the ISA trace over concatenated packet
inputs, and the final packet state is related with the exact combined order
increment.  The PicoRV32 witness pins this projected append contract.

**DECIDED:** compose through the existing complete packet contract and the
shared state-after projection; no packet contents, state, or retirement order
is reconstructed.

## 2026-11-06-ls-sv2-104 — expose projected packet state composition

Added `RvfiPacketMachine.toPacketMachine_stateAfter_append` to
`LeanModels/Refine/RvfiPacket.lean`.  The generic packet projection now has a
direct state-threading append theorem, so adjacent windows can be composed
without naming the internal packetized-RVFI state.  The PicoRV32 witness pins
the equality over its first and second packet windows.

**DECIDED:** specialize the existing packet state append law through the
packet projection; no packet contents or retirement order is inspected.

## 2026-11-06-ls-sv2-105 — expose projected packet-window refinement

Added `normalizeRvfiPacketWindows_refines_packet` and
`normalizeRvfiPacketWindows_refines_packet_append` to
`LeanModels/Refine/RvfiPacket.lean`.  Finite chains of normalized packet
windows now expose their complete ISA trace and final state/order contract
through `packetStateAfter machine.toPacketMachine`, both directly and across
two adjacent chains.  The PicoRV32 witness pins both projected contracts.

**DECIDED:** transport only the final state through the shared packet
state-after bridge; the flattened inputs, retirement payloads, and order
boundary remain those certified by the existing window theorems.

## 2026-11-06-ls-sv2-106 — expose projected packet-window state refinement

Added `normalizeRvfiPacketWindows_refines_state_packet` and
`normalizeRvfiPacketWindows_refines_state_packet_append` to
`LeanModels/Refine/RvfiPacket.lean`.  Finite normalized window chains now
expose their state/order-only contract through `packetStateAfter
machine.toPacketMachine`, directly and across two adjacent chains.  The
PicoRV32 witness pins both projected state refinements.

**DECIDED:** transport only the state/order conjunct through the shared
state-after bridge; trace equality and retirement payloads remain in the
complete window contract.

## 2026-11-06-ls-sv2-107 — certify projected packet-window input cardinality

Added `normalizeRvfiPacketWindows_inputs_length` and
`normalizeRvfiPacketWindows_inputs_length_append` to
`LeanModels/Refine/RvfiPacket.lean`.  A normalized packet-window chain now
proves that its packet-facing architectural input stream has exactly the
flattened retirement cardinality, directly and across two adjacent chains.
The PicoRV32 witness pins both packet-input cardinality projections.

**DECIDED:** derive the window result from the flattened normalization and the
existing packet input-length theorem; the carried state, packet boundaries,
and retirement order remain explicit at the window append boundary.

## 2026-11-06-ls-sv2-108 — compose packet-window ROB tag cardinality

Added `normalizeRvfiPacketWindows_rob_tags_length_append` to
`LeanModels/Refine/RvfiPacket.lean`.  Two independently certified packet-window
chains now compose directly to the exact cardinality of the flattened generic
ROB tag stream and the concatenated normalized retirement windows.  The
PicoRV32 witness pins this append cardinality over its two singleton windows.

**DECIDED:** compose through the existing finite-window certificate and the
single-chain ROB-tag cardinality theorem; no tag stream, padding, or
completion order is reconstructed at the append boundary.

## 2026-11-06-ls-sv2-109 — compose packet-window ROB input cardinality

Added `normalizeRvfiPacketWindows_rob_tags_inputs_length_append` to
`LeanModels/Refine/RvfiPacket.lean`.  Two independently certified packet-window
chains now compose directly to the exact cardinality of the mapped generic ROB
source-input stream and the concatenated normalized retirement windows.  The
PicoRV32 witness pins this append cardinality over its two singleton windows.

**DECIDED:** compose through the existing finite-window certificate and the
single-chain mapped-input cardinality theorem; the packet input stream and
retirement order remain explicit, with no padding or completion order inferred.

## 2026-11-06-ls-sv2-110 — expose packet-to-ROB input threading

Added `RvfiPacketMachine.toRobMachine_inputs_append` to
`LeanModels/Refine/RvfiPacket.lean`.  The generic ROB input projection now has
an explicit append law: concatenated cycle windows produce concatenated ROB
inputs, with the second window evaluated from the first window's retained
packet state.  The PicoRV32 witness pins this state-threaded input projection
over its two packet windows.

**DECIDED:** transport the packet machine's existing `packetInputs_append`
law through the exact `toRobMachine_inputs` bridge and the retained RVFI state;
no input order or completion order is reconstructed.

## 2026-11-06-ls-sv2-111 — expose packet-to-ROB state threading

Added `RvfiPacketMachine.toRobMachine_stateAfter_append` to
`LeanModels/Refine/RvfiPacket.lean`.  The generic ROB projection now exposes
the state-after append law directly, preserving the first window's retained
ROB state as the starting state for the second window.  The PicoRV32 witness
pins this state-threading equality over its two packet windows.

**DECIDED:** reuse the generic ROB state append theorem at the packet
projection boundary; no packet contents, input order, or completion order is
reconstructed.

## 2026-11-06-ls-sv2-112 — expose packet-to-ROB trace threading

Added `RvfiPacketMachine.toRobMachine_trace_append` to
`LeanModels/Refine/RvfiPacket.lean`.  The generic ROB retirement trace now has
an explicit append law whose second segment starts from the first segment's
retained packet state.  The PicoRV32 witness pins this state-threaded trace
projection over its two packet windows.

**DECIDED:** transport the generic `robTrace_append` law through the exact
RVFI-to-ROB state bridge; no retirement order or packet contents are inferred.

## 2026-11-06-ls-sv2-113 — expose packet trace threading

Added `RvfiPacketMachine.toPacketMachine_trace_append` to
`LeanModels/Refine/RvfiPacket.lean`.  The packet-facing retirement trace now
has an explicit append law, with the second segment evaluated from the first
segment's retained packet state.  The PicoRV32 witness pins this trace
projection over its two packet windows.

**DECIDED:** reuse the generic `packetTrace_append` law at the packetized RVFI
projection boundary; no retirement order or packet contents are reconstructed.

## 2026-11-06-ls-sv2-114 — expose packet input threading

Added `RvfiPacketMachine.toPacketMachine_inputs_append` to
`LeanModels/Refine/RvfiPacket.lean`.  The packet-facing architectural input
stream now has an explicit append law, with the second segment evaluated from
the first segment's retained packet state.  The PicoRV32 witness pins this
projection over its two packet windows.

**DECIDED:** reuse the generic `packetInputs_append` law at the packetized RVFI
projection boundary; no input order or completion order is reconstructed.

## 2026-11-06-ls-sv2-115 — expose packet ROB tag threading

Added `RvfiPacketMachine.toRobMachine_tags_append` to
`LeanModels/Refine/RvfiPacket.lean`.  The generic tagged ROB stream now has an
explicit append law, with the second segment evaluated from the first segment's
retained RVFI state.  The PicoRV32 witness pins this projection over its two
packet windows.

**DECIDED:** transport the generic `robTags_append` law through the exact
RVFI-to-ROB state bridge; no tag order or completion order is reconstructed.

## 2026-11-06-ls-sv2-116 — expose packet ROB tag payload threading

Added `RvfiPacketMachine.toRobMachine_tags_retirements_append` to
`LeanModels/Refine/RvfiPacket.lean`.  Erasing `TaggedCommit` metadata from the
concatenated ROB tag stream now exposes the two packet traces with the first
window's retained state threaded into the second.  The PicoRV32 witness pins
this payload projection over its two packet windows.

**DECIDED:** reuse the existing ROB tag erasure and packet trace bridges; no
retirement payload or completion order is reconstructed.

## 2026-11-06-ls-sv2-117 — expose packet ROB tag input threading

Added `RvfiPacketMachine.toRobMachine_tags_inputs_append` to
`LeanModels/Refine/RvfiPacket.lean`.  Erasing `TaggedCommit` metadata from the
concatenated ROB tag stream now exposes the two packet input streams with the
first window's retained packet state threaded into the second.  The PicoRV32
witness pins this source-input projection over its two packet windows.

**DECIDED:** reuse the existing tag-input bridge and `packetInputs_append`; no
input order or completion order is reconstructed.

## 2026-11-06-ls-sv2-118 — expose packet ROB tag payload projection

Added `RvfiPacketMachine.toRobMachine_tags_retirements` to
`LeanModels/Refine/RvfiPacket.lean`.  Erasing `TaggedCommit` metadata from the
generic ROB tag stream now directly recovers the packet-facing retirement trace
for any finite cycle prefix.  The PicoRV32 witness pins this projection over
the complete packet capture.

**DECIDED:** compose the existing ROB tag erasure with the packet trace bridge;
no retirement payload or completion order is reconstructed.

## 2026-11-06-ls-sv2-119 — certify normalized packet ROB tag cardinality

Added `normalizeRvfiPacketRobTags_length` to
`LeanModels/Refine/RvfiPacket.lean`.  A successful normalized packet capture
now proves that the generic ROB tag stream has exactly the decoded retirement
cardinality.  The PicoRV32 witness pins this cardinality over the captured
packet trace.

**DECIDED:** derive the length equality from the existing packet trace
projection and `List.length`; no tag order or completion order is
reconstructed.

## 2026-11-06-ls-sv2-120 — certify normalized packet ROB tag input cardinality

Added `normalizeRvfiPacketRobTags_inputs_length` to
`LeanModels/Refine/RvfiPacket.lean`.  A successful normalized packet capture
now proves that the mapped source-input stream of the generic ROB tags has
exactly the decoded retirement cardinality.  The PicoRV32 witness pins this
input-count contract over the complete packet capture.

**DECIDED:** derive mapped-input cardinality from the generic ROB tag count
and `List.length_map`; no input order or completion order is reconstructed.

## 2026-11-06-ls-sv2-121 — compose normalized packet ROB tag cardinality

Added `normalizeRvfiPacketRobTags_length_append` to
`LeanModels/Refine/RvfiPacket.lean`.  Two adjacent normalized packet windows
now prove directly that the concatenated generic ROB tag stream has the
concatenated decoded retirement cardinality, with the second window evaluated
from the first window's retained state.  The PicoRV32 witness pins this direct
append route.

**DECIDED:** compose the existing normalized trace append theorem with the
flat ROB-tag cardinality projection; no tag order or completion order is
reconstructed.

## 2026-11-06-ls-sv2-122 — compose normalized packet ROB tag input cardinality

Added `normalizeRvfiPacketRobTags_inputs_length_append` to
`LeanModels/Refine/RvfiPacket.lean`.  Two adjacent normalized packet windows
now prove directly that the mapped source-input stream of the concatenated
generic ROB tags has the concatenated decoded retirement cardinality.  The
PicoRV32 witness pins this direct append route.

**DECIDED:** derive mapped-input cardinality from the flat tag append result
and `List.length_map`; no input order or completion order is reconstructed.

## 2026-11-06-ls-sv2-123 — expose normalized packet ROB tag retirements

Added `normalizeRvfiPacketRobTags_retirements` to
`LeanModels/Refine/RvfiPacket.lean`.  A successful normalized packet capture
now exposes its decoded retirement payload directly through the generic ROB
tag stream.  The PicoRV32 witness pins this normalized payload projection
over the complete packet capture.

**DECIDED:** reuse the exact packet-to-ROB tag retirement bridge and the
normalized packet trace theorem; no retirement order or completion order is
reconstructed.

## 2026-11-06-ls-sv2-124 — compose normalized packet ROB tag retirements

Added `normalizeRvfiPacketRobTags_retirements_append` to
`LeanModels/Refine/RvfiPacket.lean`.  Two adjacent normalized packet windows
now expose their concatenated decoded retirement payload directly through the
concatenated generic ROB tag stream.  The PicoRV32 witness pins this direct
append route.

**DECIDED:** compose the normalized packet trace append theorem through the
exact packet-to-ROB tag retirement projection; no retirement order or
completion order is reconstructed.

## 2026-11-06-ls-sv2-125 — expose packet-window ROB tag inputs

Added `normalizeRvfiPacketWindows_rob_tags_inputs` to
`LeanModels/Refine/RvfiPacket.lean`.  A certified packet-window chain now
exposes the packet-facing source-input stream carried by its flattened generic
ROB tags.  The PicoRV32 chain witness now routes through this reusable
projection theorem.

**DECIDED:** reuse the exact packet-to-ROB tag-input bridge; the normalization
certificate supplies the chain boundary but no input order is reconstructed.

## 2026-11-06-ls-sv2-126 — compose packet-window ROB tag inputs

Added `normalizeRvfiPacketWindows_rob_tags_inputs_append` to
`LeanModels/Refine/RvfiPacket.lean`.  Two certified packet-window chains now
compose their mapped generic ROB source-input streams over the concatenated
window chain, retaining the second chain's carried state.  The PicoRV32
witness pins this append projection.

**DECIDED:** compose through the finite window certificate and the exact
packet-to-ROB tag-input bridge; no input order or completion order is
reconstructed.

## 2026-11-06-ls-sv2-127 — expose normalized packet ROB tag inputs

Added `normalizeRvfiPacketRobTags_inputs` to
`LeanModels/Refine/RvfiPacket.lean`.  A successful normalized packet capture
now exposes its packet-facing source-input stream directly through the generic
ROB tag stream.  The PicoRV32 witness pins this normalized input projection
over the complete packet capture.

**DECIDED:** reuse the exact packet-to-ROB tag-input bridge; normalization
certifies the capture but does not reconstruct or reorder inputs.

## 2026-11-06-ls-sv2-128 — compose normalized packet ROB tag inputs

Added `normalizeRvfiPacketRobTags_inputs_append` to
`LeanModels/Refine/RvfiPacket.lean`.  Two adjacent normalized packet windows
now expose their concatenated packet-facing source-input stream directly
through the concatenated generic ROB tags, with the second window evaluated
from the first window's retained state.  The PicoRV32 witness pins this
normalized append projection.

**DECIDED:** compose through the normalized packet trace append theorem and
the exact packet-to-ROB tag-input bridge; no input order or completion order
is reconstructed.

## 2026-11-06-ls-sv2-129 — connect normalized packet ROB tag inputs to ROB inputs

Added `normalizeRvfiPacketRobTags_inputs_robInputs` to
`LeanModels/Refine/RvfiPacket.lean`.  A successful normalized packet capture
now exposes the source-input stream of its generic ROB tags directly as the
generic ROB machine's `robInputs` projection.  The PicoRV32 witness pins this
bridge over the complete packet capture.

**DECIDED:** reuse the exact `robTags_inputs` erasure theorem; normalization
certifies the capture but does not alter or reorder the generic ROB inputs.

## 2026-11-06-ls-sv2-130 — compose normalized packet ROB tag inputs over ROB inputs

Added `normalizeRvfiPacketRobTags_inputs_robInputs_append` to
`LeanModels/Refine/RvfiPacket.lean`.  Two adjacent normalized packet windows
now expose their concatenated tagged source-input stream as the concatenation
of the corresponding generic ROB `robInputs` streams, with the second stream
evaluated from the first window's retained state.  The PicoRV32 witness pins
this normalized append bridge.

**DECIDED:** compose the normalized capture theorem with the exact generic ROB
input append law; no input order or completion order is reconstructed.

## 2026-11-06-ls-sv2-131 — certify normalized packet ROB input cardinality

Added `normalizeRvfiPacketRobInputs_length` to
`LeanModels/Refine/RvfiPacket.lean`.  A successful normalized packet capture
now proves that the generic ROB machine's retained input stream has exactly
the decoded retirement cardinality.  The PicoRV32 witness pins this count
over the complete packet capture.

**DECIDED:** transport the established normalized packet-input cardinality
through the exact packet-to-ROB input projection; no input order is inferred.

## 2026-11-06-ls-sv2-132 — compose normalized packet ROB input cardinality

Added `normalizeRvfiPacketRobInputs_length_append` to
`LeanModels/Refine/RvfiPacket.lean`.  Two adjacent normalized packet windows
now prove directly that the concatenated generic ROB input stream has the
concatenated decoded retirement cardinality, with the second window evaluated
from the first window's retained state.  The PicoRV32 witness pins this
append count.

**DECIDED:** compose the normalized trace append certificate through the
exact packet-to-ROB input projection; no input order or completion order is
reconstructed.

## 2026-11-06-ls-sv2-133 — certify packet-window ROB input cardinality

Added `normalizeRvfiPacketWindows_robInputs_length` to
`LeanModels/Refine/RvfiPacket.lean`.  A certified finite packet-window chain
now proves that its flattened generic ROB input stream has exactly the
flattened normalized retirement cardinality.  The PicoRV32 witness pins this
chain count over its two measured windows.

**DECIDED:** flatten only after the window certificate supplies each carried
state and retirement boundary, then reuse the single-window ROB-input count.

## 2026-11-06-ls-sv2-134 — compose packet-window ROB input cardinality

Added `normalizeRvfiPacketWindows_robInputs_length_append` to
`LeanModels/Refine/RvfiPacket.lean`.  Two independently certified packet
window chains now prove directly that their concatenated generic ROB input
stream has the concatenated flattened retirement cardinality, retaining the
second chain's carried state and order boundary.  The PicoRV32 witness pins
this append count.

**DECIDED:** compose through the explicit window-chain append certificate and
the flattened generic ROB input count; no input order is reconstructed.

## 2026-11-06-ls-sv2-135 — certify packet-window ROB trace cardinality

Added `normalizeRvfiPacketWindows_rob_trace_length` to
`LeanModels/Refine/RvfiPacket.lean`.  A certified finite packet-window chain
now proves that its flattened generic ROB retirement trace has exactly the
flattened normalized retirement cardinality.  The PicoRV32 witness pins this
trace count over its two measured windows.

**DECIDED:** transport the generic ROB trace/input cardinality equality
through the certified packet-window input count; no trace payload or order is
reconstructed.

## 2026-11-06-ls-sv2-136 — compose packet-window ROB trace cardinality

Added `normalizeRvfiPacketWindows_rob_trace_length_append` to
`LeanModels/Refine/RvfiPacket.lean`.  Two independently certified packet
window chains now prove directly that their concatenated generic ROB
retirement trace has the concatenated flattened normalized retirement
cardinality, retaining the second chain's carried state and order boundary.
The PicoRV32 witness pins this append count.

**DECIDED:** compose through the explicit window-chain append certificate and
the flattened generic ROB trace cardinality; no trace payload or order is
reconstructed.

## 2026-11-06-ls-sv2-137 — certify packet-window trace cardinality

Added `normalizeRvfiPacketWindows_trace_length` to
`LeanModels/Refine/RvfiPacket.lean`.  A certified finite packet-window chain
now proves that its packet-facing retirement trace has exactly the flattened
normalized retirement cardinality.  The PicoRV32 witness pins this count over
its two measured windows.

**DECIDED:** transport the exact packet-to-ROB trace equality through the
certified ROB-trace cardinality; no packet trace payload or order is
reconstructed.

## 2026-11-06-ls-sv2-138 — compose packet-window trace cardinality

Added `normalizeRvfiPacketWindows_trace_length_append` to
`LeanModels/Refine/RvfiPacket.lean`.  Two independently certified packet
window chains now prove directly that their concatenated packet-facing
retirement trace has the concatenated flattened normalized retirement
cardinality, retaining the second chain's carried state and order boundary.
The PicoRV32 witness pins this append count.

**DECIDED:** compose through the explicit window-chain append certificate and
the exact packet-to-ROB trace cardinality; no trace payload or order is
reconstructed.

## 2026-11-06-ls-sv2-139 — expose packet-window retirement trace

Added `normalizeRvfiPacketWindows_trace` and
`normalizeRvfiPacketWindows_trace_append` to
`LeanModels/Refine/RvfiPacket.lean`.  A certified packet-window chain now
exposes its packet-facing retirement payload directly, and two certified
chains compose that payload with the second chain's carried state and order
boundary.  The PicoRV32 witnesses pin both forms.

**DECIDED:** erase the generic ROB boundary through the exact
`toRobMachine_trace` equality; no retirement payload or order is reconstructed.

## 2026-11-06-ls-sv2-140 — certify packet-window tagged retirement cardinality

Added `normalizeRvfiPacketWindows_rob_tags_retirements_length` and its append
form to `LeanModels/Refine/RvfiPacket.lean`.  A certified packet-window chain
and two adjacent certified chains now expose the exact cardinality of the
tagged generic ROB retirement payload.  The PicoRV32 witnesses pin both
forms.

**DECIDED:** derive cardinality from the exact tagged retirement payload
equality and `List.length`; no retirement order or payload is reconstructed.

## 2026-11-06-ls-sv2-141 — bridge packet-window tag inputs to ROB inputs

Added `normalizeRvfiPacketWindows_rob_tags_inputs_robInputs` and its append
form to `LeanModels/Refine/RvfiPacket.lean`.  A certified packet-window chain
now identifies the tagged generic ROB source-input projection with the
generic ROB machine's `robInputs` stream, and two adjacent chains compose the
same bridge while retaining the second chain's carried state.  The PicoRV32
witness pins both forms over its two measured windows.

**DECIDED:** reuse the exact `robTags_inputs` erasure and generic ROB input
append laws; the window certificate supplies state/order validity but does not
reconstruct or reorder inputs.

## 2026-11-06-ls-sv2-142 — bridge packet-window tag retirements to ROB traces

Added `normalizeRvfiPacketWindows_rob_tags_retirements_robTrace` and its
append form to `LeanModels/Refine/RvfiPacket.lean`.  A certified packet-window
chain now identifies the tagged generic ROB retirement payload with the
generic ROB retirement trace, and two adjacent chains compose the same bridge
while retaining the second chain's carried state.  The PicoRV32 witness pins
both forms over its two measured windows.

**DECIDED:** reuse the exact `robTags_retirements` erasure and generic ROB
trace append laws; the window certificate validates state/order but does not
reconstruct or reorder retirements.

## 2026-11-06-ls-sv2-143 — bridge normalized tag retirements to ROB traces

Added `normalizeRvfiPacketRobTags_retirements_robTrace` and its append form to
`LeanModels/Refine/RvfiPacket.lean`.  A normalized packet capture now
identifies mapped tagged retirements with the generic ROB retirement trace,
and adjacent normalized captures compose that bridge with the first capture's
retained state feeding the second.  The PicoRV32 witness pins both forms.

**DECIDED:** reuse the exact `robTags_retirements` erasure and the packetized
ROB trace append law; normalization supplies validity but does not reconstruct
or reorder retirements.

## 2026-11-06-ls-sv2-144 — certify normalized tag retirement cardinality

Added `normalizeRvfiPacketRobTags_retirements_length` and its append form to
`LeanModels/Refine/RvfiPacket.lean`.  A normalized packet capture now proves
that the mapped tagged retirement payload has exactly the decoded retirement
cardinality, and adjacent normalized captures compose the same count.  The
PicoRV32 witness pins both forms.

**DECIDED:** derive the count from the exact normalized tagged-retirement
equality and `List.length`; no retirement order or payload is reconstructed.

## 2026-11-06-ls-sv2-145 — certify normalized ROB trace cardinality

Added `normalizeRvfiPacketRobTrace_length` and its append form to
`LeanModels/Refine/RvfiPacket.lean`.  A normalized packet capture now proves
that the generic ROB retirement trace has exactly the decoded retirement
cardinality, and adjacent normalized captures compose the same count.  The
PicoRV32 witness pins both forms.

**DECIDED:** derive the count from the exact normalized ROB trace equality and
`List.length`; no retirement order or payload is reconstructed.

## 2026-11-06-ls-sv2-146 — certify normalized packet trace cardinality

Added `normalizeRvfiPacketTrace_length` and its append form to
`LeanModels/Refine/RvfiPacket.lean`.  A normalized packet capture now proves
that the packet-facing retirement trace has exactly the decoded retirement
cardinality, and adjacent normalized captures compose the same count.  The
PicoRV32 witness pins both forms.

**DECIDED:** derive the count from the exact normalized packet trace equality
and `List.length`; no retirement order or payload is reconstructed.

## 2026-11-06-ls-sv2-147 — certify normalized packet tag-stream cardinality

Added `normalizeRvfiPacketTags_length` and its append form to
`LeanModels/Refine/RvfiPacket.lean`.  A normalized packet capture now proves
that the packet-boundary tagged stream has exactly the decoded retirement
cardinality, and adjacent normalized captures compose the same count.  The
PicoRV32 witness pins both forms.

**DECIDED:** derive the packet-stream width from the exact generic
`rvfiPacketTags_length` projection and the normalization filter-map equality;
packet boundaries and retirement order remain unchanged.

## 2026-11-06-ls-sv2-148 — certify packet-window tag-stream cardinality

Added `normalizeRvfiPacketWindows_tags_length` and its append form to
`LeanModels/Refine/RvfiPacket.lean`.  A certified finite packet-window chain
now proves that its packet-boundary tagged stream has exactly the flattened
normalized retirement cardinality, and two certified chains compose the same
count while retaining the second chain's carried state and order boundary.
The PicoRV32 witness pins both forms.

**DECIDED:** flatten only after the window certificate supplies its carried
state and normalized retirement boundary, then reuse the normalized
packet-tag width theorem; packet boundaries and retirement order remain
unchanged.

## 2026-11-06-ls-sv2-149 — expose normalized packet tag retirements

Added `normalizeRvfiPacketTags_retirements` and its append form to
`LeanModels/Refine/RvfiPacket.lean`.  A successful normalized packet capture
now exposes its decoded retirement payload directly from the flattened
packet-boundary tag stream, and adjacent captures compose the same payload
with the first capture's state feeding the second.  The PicoRV32 witness pins
both forms.

**DECIDED:** reuse the exact packet-tag flattening and generic ROB erasure
bridges, then apply the normalized packet trace equality; no retirement order
or packet boundary is reconstructed.

## 2026-11-06-ls-sv2-150 — expose packet-window tag retirements

Added `normalizeRvfiPacketWindows_tags_retirements` and its append form to
`LeanModels/Refine/RvfiPacket.lean`.  A certified finite packet-window chain
now exposes its flattened packet-boundary tag retirement payload as the
flattened normalized retirement windows, and two certified chains compose the
same payload while retaining the second chain's carried state and order
boundary.  The PicoRV32 witness pins both forms.

**DECIDED:** flatten only after the window certificate supplies its carried
state and normalized retirement boundary, then reuse the normalized packet-tag
retirement projection; no retirement order or packet boundary is reconstructed.

## 2026-11-06-ls-sv2-151 — expose normalized packet tag inputs

Added `normalizeRvfiPacketTags_inputs` and its append form to
`LeanModels/Refine/RvfiPacket.lean`.  A successful normalized packet capture
now exposes its packet-facing source-input stream directly from the flattened
packet-boundary tagged stream, and adjacent captures compose the same stream
with the first capture's state feeding the second.  The PicoRV32 witness pins
both forms.

**DECIDED:** reuse the exact packet-tag flattening and generic ROB input
projection; normalization supplies validity but does not reconstruct or reorder
source inputs.

## 2026-11-06-ls-sv2-152 — expose packet-window tag inputs

Added `normalizeRvfiPacketWindows_tags_inputs` and its append form to
`LeanModels/Refine/RvfiPacket.lean`.  A certified finite packet-window chain
now exposes its flattened packet-boundary source-input stream, and two
adjacent certified chains compose that stream with the second chain's carried
state and order boundary.  The PicoRV32 witness pins both forms.

**DECIDED:** flatten only after the window certificate supplies its carried
state and normalized retirement boundary, then reuse the exact packet-input
append law; packet boundaries and source-input order remain unchanged.

## 2026-11-06-ls-sv2-153 — certify normalized packet tag-input cardinality

Added `normalizeRvfiPacketTags_inputs_length` and its append form to
`LeanModels/Refine/RvfiPacket.lean`.  A normalized packet capture now certifies
that the flattened packet-boundary source-input projection has exactly the
decoded retirement cardinality, and adjacent captures compose the same count.
The PicoRV32 witness pins both forms.

**DECIDED:** transport the exact normalized generic ROB-tag input cardinality
through `toRobMachine_tags`; no packet boundary or source-input order is
reconstructed.

## 2026-11-06-ls-sv2-154 — certify packet-window tag-input cardinality

Added `normalizeRvfiPacketWindows_tags_inputs_length` and its append form to
`LeanModels/Refine/RvfiPacket.lean`.  A certified finite packet-window chain
now certifies that its flattened packet-boundary source-input projection has
exactly the flattened normalized retirement cardinality, and adjacent chains
compose the same count while retaining the carried state and order boundary.
The PicoRV32 witness pins both forms.

**DECIDED:** flatten only after the window certificate supplies its carried
state and normalized retirement boundary, then transport the exact generic
ROB-tag input cardinality; packet boundaries and source-input order remain
unchanged.

## 2026-11-06-ls-sv2-155 — certify packet-tag input cardinality against packet inputs

Added `normalizeRvfiPacketTags_inputs_length_packetInputs` and its append form
to `LeanModels/Refine/RvfiPacket.lean`.  A successful normalized packet
capture now certifies that the flattened packet-tag source-input projection
has exactly the packet machine's `packetInputs` cardinality, and adjacent
captures compose the same bridge.  The PicoRV32 witness pins both forms.

**DECIDED:** take the length of the existing exact packet-tag input
projection; packet boundaries, source-input order, and normalization
cardinality are not reconstructed.

## 2026-11-06-ls-sv2-156 — certify packet-window tag-input cardinality against packet inputs

Added `normalizeRvfiPacketWindows_tags_inputs_length_packetInputs` and its
append form to `LeanModels/Refine/RvfiPacket.lean`.  A certified finite
packet-window chain now certifies that its flattened packet-tag source-input
projection has exactly the packet machine's flattened `packetInputs`
cardinality, and adjacent certified chains compose the same bridge while
retaining the carried state.  The PicoRV32 witness pins both forms.

**DECIDED:** take the length of the existing exact packet-window tag-input
projection and use the packet-input append law for the composed form; packet
boundaries, source-input order, and normalization cardinality are not
reconstructed.

## 2026-11-06-ls-sv2-157 — certify normalized packet tag-retirement cardinality

Added `normalizeRvfiPacketTags_retirements_length` and its append form to
`LeanModels/Refine/RvfiPacket.lean`.  A normalized packet capture now
certifies that the flattened packet-tag retirement projection has exactly the
decoded retirement cardinality, and adjacent captures compose the same count.
The PicoRV32 witness pins both forms.

**DECIDED:** take `List.length` of the existing exact packet-tag retirement
projection; retirement order, packet boundaries, and payloads are not
reconstructed.

## 2026-11-06-ls-sv2-158 — certify packet-window tag-retirement cardinality

Added `normalizeRvfiPacketWindows_tags_retirements_length` and its append form
to `LeanModels/Refine/RvfiPacket.lean`.  A certified finite packet-window
chain now certifies that its flattened packet-tag retirement projection has
exactly the flattened normalized retirement cardinality, and adjacent chains
compose the same count while retaining the carried state and order boundary.
The PicoRV32 witness pins both forms.

**DECIDED:** take `List.length` of the exact packet-window tag-retirement
projection; packet boundaries, retirement order, and payloads are not
reconstructed.

## 2026-11-06-ls-sv2-159 — certify normalized packet tag-retirement cardinality against packet trace

Added `normalizeRvfiPacketTags_retirements_length_packetTrace` and its append
form to `LeanModels/Refine/RvfiPacket.lean`.  A normalized packet-tag
retirement projection now certifies the exact cardinality of the packet
machine's retirement trace, and adjacent normalized captures compose the same
bridge while retaining the first capture's state for the second.  The PicoRV32
witness pins both forms.

**DECIDED:** take `List.length` of the exact packet-tag retirement projection
and bridge it through the normalized packet trace equality; retirement order,
packet boundaries, and payloads are not reconstructed.

## 2026-11-06-ls-sv2-160 — certify packet-window tag-retirement cardinality against packet trace

Added `normalizeRvfiPacketWindows_tags_retirements_length_packetTrace` and
its append form to `LeanModels/Refine/RvfiPacket.lean`.  A certified finite
packet-window chain now certifies the exact cardinality of its flattened
packet-tag retirement projection against the packet machine's retirement
trace, and adjacent chains compose the bridge while retaining the carried
state and order boundary.  The PicoRV32 witness pins both forms.

**DECIDED:** flatten only after the window certificate supplies carried state
and normalized retirement boundaries, then bridge the exact tag-retirement
projection through the packet trace; packet boundaries, retirement order, and
payloads are not reconstructed.

## 2026-11-06-ls-sv2-161 — certify normalized ROB tag-retirement cardinality against ROB trace

Added `normalizeRvfiPacketRobTags_retirements_length_robTrace` and its append
form to `LeanModels/Refine/RvfiPacket.lean`.  A normalized packet capture now
certifies that the generic ROB tagged-retirement projection has exactly the
corresponding ROB retirement-trace cardinality, and adjacent normalized
captures compose the same bridge while retaining the first capture's state
boundary.  The PicoRV32 witness pins both forms.

**DECIDED:** take `List.length` of the exact normalized generic-ROB
tag-retirement/ROB-trace equality; retirement order, packet boundaries, and
payloads are not reconstructed.

## 2026-11-06-ls-sv2-162 — certify packet-window ROB tag-retirement cardinality against ROB trace

Added `normalizeRvfiPacketWindows_rob_tags_retirements_length_robTrace` and
its append form to `LeanModels/Refine/RvfiPacket.lean`.  A certified finite
packet-window chain now certifies the exact cardinality of its generic ROB
tagged-retirement projection against the generic ROB retirement trace, and
adjacent chains compose the bridge while retaining the carried state and order
boundary.  The PicoRV32 witness pins both forms.

**DECIDED:** take `List.length` of the exact packet-window generic-ROB
tag-retirement/ROB-trace equality; packet boundaries, retirement order, and
payloads are not reconstructed.

## 2026-11-06-ls-sv2-163 — certify normalized ROB tag-input cardinality against ROB inputs

Added `normalizeRvfiPacketRobTags_inputs_length_robInputs` and its append form
to `LeanModels/Refine/RvfiPacket.lean`.  A normalized packet capture now
certifies that the generic ROB tagged source-input projection has exactly the
corresponding ROB input cardinality, and adjacent normalized captures compose
the same bridge while retaining the first capture's state boundary.  The
PicoRV32 witness pins both forms.

**DECIDED:** take `List.length` of the exact normalized generic-ROB tag-input/
ROB-input equality; retirement order, packet boundaries, and payloads are not
reconstructed.

## 2026-11-06-ls-sv2-164 — certify packet-window ROB tag-input cardinality against ROB inputs

Added `normalizeRvfiPacketWindows_rob_tags_inputs_length_robInputs` and its
append form to `LeanModels/Refine/RvfiPacket.lean`.  A certified finite
packet-window chain now certifies the exact cardinality of its generic ROB
tagged source-input projection against `robInputs`, and adjacent chains
compose the bridge while retaining the carried state and order boundary.  The
PicoRV32 witness pins both forms.

**DECIDED:** take `List.length` of the exact packet-window generic-ROB
tag-input/ROB-input equality; packet boundaries, source-input order, and
payloads are not reconstructed.

## 2026-11-06-ls-sv2-165 — certify normalized ROB tag-input cardinality against packet inputs

Added `normalizeRvfiPacketRobTags_inputs_length_packetInputs` and its append
form to `LeanModels/Refine/RvfiPacket.lean`.  A normalized packet capture now
certifies that the generic ROB tagged source-input projection has exactly the
packet machine's input cardinality, and adjacent normalized captures compose
the same bridge while retaining the first capture's state boundary.  The
PicoRV32 witness pins both forms.

**DECIDED:** take `List.length` of the exact normalized generic-ROB tag-input/
packet-input equality and use the packet-input append law for the composed
form; retirement order, packet boundaries, source-input order, and payloads
are not reconstructed.

## 2026-11-06-ls-sv2-166 — certify packet-window ROB tag-input cardinality against packet inputs

Added `normalizeRvfiPacketWindows_rob_tags_inputs_length_packetInputs` and its
append form to `LeanModels/Refine/RvfiPacket.lean`.  A certified finite
packet-window chain now certifies the exact packet-machine input cardinality of
its generic ROB tagged source-input projection, and adjacent chains compose the
same bridge while retaining the carried state and order boundary.  The
PicoRV32 witness pins both forms.

**DECIDED:** take `List.length` of the exact certified packet-window generic-ROB
tag-input/packet-input equality; packet boundaries, source-input order, and
payloads are not reconstructed.

## 2026-11-06-ls-sv2-167 — certify normalized ROB tag-retirement cardinality against packet trace

Added `normalizeRvfiPacketRobTags_retirements_length_packetTrace` and its
append form to `LeanModels/Refine/RvfiPacket.lean`.  A normalized packet
capture now certifies that the generic ROB tagged-retirement projection has
exactly the packet machine's retirement-trace cardinality, and adjacent
captures compose the same bridge while retaining the first capture's state
boundary.  The PicoRV32 witness pins both forms.

**DECIDED:** bridge the exact normalized generic-ROB tag-retirement/ROB-trace
cardinality through `toRobMachine_trace` to the packet trace; retirement
order, packet boundaries, and payloads are not reconstructed.

## 2026-11-06-ls-sv2-168 — certify packet-window ROB tag-retirement cardinality against packet trace

Added `normalizeRvfiPacketWindows_rob_tags_retirements_length_packetTrace` and
its append form to `LeanModels/Refine/RvfiPacket.lean`.  A certified finite
packet-window chain now certifies the exact packet-machine retirement-trace
cardinality of its generic ROB tagged-retirement projection, and adjacent
chains compose the same bridge while retaining the carried state and order
boundary.  The PicoRV32 witness pins both forms.

**DECIDED:** flatten only after the window certificate supplies carried state
and normalized retirement boundaries, then bridge the exact generic-ROB
tag-retirement/ROB-trace cardinality through `toRobMachine_trace` to the packet
trace; packet boundaries, retirement order, and payloads are not reconstructed.

## 2026-11-06-ls-sv2-169 — certify normalized ROB input cardinality against packet inputs

Added `normalizeRvfiPacketRobInputs_length_packetInputs` and its append form
to `LeanModels/Refine/RvfiPacket.lean`.  A normalized packet capture now
certifies that the generic ROB input stream has exactly the packet machine's
input cardinality, and adjacent captures compose the same bridge while
retaining the first capture's state boundary.  The PicoRV32 witness pins both
forms.

**DECIDED:** take `List.length` of the exact `toRobMachine_inputs` projection
and compose it across normalized captures; retirement order, packet
boundaries, source-input order, and payloads are not reconstructed.

## 2026-11-06-ls-sv2-170 — certify packet-window ROB input cardinality against packet inputs

Added `normalizeRvfiPacketWindows_robInputs_length_packetInputs` and its
append form to `LeanModels/Refine/RvfiPacket.lean`.  A certified finite
packet-window chain now certifies the exact packet-machine input cardinality of
its generic ROB input stream, and adjacent chains compose the same bridge while
retaining the carried state and order boundary.  The PicoRV32 witness pins
both forms.

**DECIDED:** take `List.length` of the exact `toRobMachine_inputs` projection
after the window certificate supplies its carried state, and compose it across
chains; packet boundaries, source-input order, and payloads are not
reconstructed.

## 2026-11-06-ls-sv2-171 — certify normalized packet input cardinality against packet trace

Added `normalizeRvfiPacketInputs_length_packetTrace` and its append form to
`LeanModels/Refine/RvfiPacket.lean`.  A normalized packet capture now
certifies that the packet machine's architectural input stream has exactly its
retirement-trace cardinality, and adjacent captures compose the same bridge
while retaining the first capture's state boundary.  The PicoRV32 witness
pins both forms.

**DECIDED:** bridge the exact normalized packet-input cardinality and packet
trace cardinality through the shared decoded-retirement count; retirement
order, packet boundaries, source-input order, and payloads are not
reconstructed.

## 2026-11-06-ls-sv2-172 — certify packet-window input cardinality against packet trace

Added `normalizeRvfiPacketWindows_inputs_length_packetTrace` and its append
form to `LeanModels/Refine/RvfiPacket.lean`.  A certified packet-window chain
now determines that its packet input stream has exactly the packet-machine
retirement-trace cardinality, and adjacent chains compose the same bridge
through their carried state boundary.  The PicoRV32 witness pins both forms.

**DECIDED:** flatten only through the existing packet-window certificate,
reuse the normalized packet-input/packet-trace cardinality theorem, and retain
the carried state; packet boundaries, retirement order, source-input order,
and payloads are not reconstructed.

## 2026-11-06-ls-sv2-173 — certify normalized ROB trace cardinality against packet trace

Added `normalizeRvfiPacketRobTrace_length_packetTrace` and its append form to
`LeanModels/Refine/RvfiPacket.lean`.  A normalized packet capture now
certifies that the generic ROB retirement trace and packet retirement trace
have equal cardinality, and adjacent captures compose the same bridge while
retaining the first capture's state boundary.  The PicoRV32 witness pins both
forms.

**DECIDED:** take `List.length` of the exact normalized generic ROB and packet
trace equalities and compose through normalized trace append; retirement
payloads, packet boundaries, and order are not reconstructed.

## 2026-11-06-ls-sv2-174 — certify packet-window ROB trace cardinality against packet trace

Added `normalizeRvfiPacketWindows_rob_trace_length_packetTrace` and its append
form to `LeanModels/Refine/RvfiPacket.lean`.  A certified packet-window chain
now certifies equal generic-ROB and packet retirement-trace cardinalities, and
adjacent chains compose the bridge through their carried state boundary.  The
PicoRV32 witness pins both forms.

**DECIDED:** flatten only through the existing packet-window certificate,
reuse the normalized ROB-trace/packet-trace cardinality bridge, and retain the
carried state; packet boundaries, retirement payloads, and order are not
reconstructed.

## 2026-11-06-ls-sv2-175 — certify normalized ROB trace cardinality against packet inputs

Added `normalizeRvfiPacketRobTrace_length_packetInputs` and its append form to
`LeanModels/Refine/RvfiPacket.lean`.  A normalized packet capture now
certifies that the generic ROB retirement trace has exactly the packet input
cardinality, and adjacent captures compose the bridge through their retained
state boundary.  The PicoRV32 witness pins both forms.

**DECIDED:** take `List.length` of the exact normalized ROB-trace and
packet-input cardinalities and compose through normalized trace append;
retirement payloads, packet boundaries, and order are not reconstructed.

## 2026-11-06-ls-sv2-176 — certify packet-window ROB trace cardinality against packet inputs

Added `normalizeRvfiPacketWindows_rob_trace_length_packetInputs` and its
append form to `LeanModels/Refine/RvfiPacket.lean`.  A certified packet-window
chain now certifies equal generic-ROB trace and packet-input cardinalities,
and adjacent chains compose the bridge through their carried state boundary.
The PicoRV32 witness pins both forms.

**DECIDED:** flatten only through the existing packet-window certificate,
reuse the normalized ROB-trace/packet-input cardinality bridge, and retain the
carried state; packet boundaries, retirement payloads, and order are not
reconstructed.

## 2026-11-06-ls-sv2-177 — certify normalized ROB input cardinality against packet trace

Added `normalizeRvfiPacketRobInputs_length_packetTrace` and its append form to
`LeanModels/Refine/RvfiPacket.lean`.  A normalized packet capture now
certifies that the generic ROB input stream has exactly the packet retirement
trace cardinality, and adjacent captures compose the bridge through their
retained state boundary.  The PicoRV32 witness pins both forms.

**DECIDED:** take `List.length` of the exact normalized ROB-input and packet
trace cardinalities and compose through normalized trace append; packet
boundaries, source-input order, retirement payloads, and order are not
reconstructed.

## 2026-11-06-ls-sv2-178 — certify packet-window ROB input cardinality against packet trace

Added `normalizeRvfiPacketWindows_robInputs_length_packetTrace` and its
append form to `LeanModels/Refine/RvfiPacket.lean`.  A certified packet-window
chain now certifies equal generic ROB-input and packet-retirement-trace
cardinalities, and adjacent chains compose the bridge through their carried
state boundary.  The PicoRV32 witness pins both forms.

**DECIDED:** flatten only through the existing packet-window certificate,
reuse the normalized ROB-input/packet-trace cardinality bridge, and retain the
carried state; packet boundaries, source-input order, retirement payloads, and
order are not reconstructed.

## 2026-11-06-ls-sv2-179 — certify normalized ROB input cardinality against ROB trace

Added `normalizeRvfiPacketRobInputs_length_robTrace` and its append form to
`LeanModels/Refine/RvfiPacket.lean`.  A normalized packet capture now
certifies that the generic ROB input and retirement-trace streams have equal
cardinality, and adjacent captures compose the same bridge.  The PicoRV32
witness pins both forms.

**DECIDED:** reuse the exact generic `robTrace_length_eq_robInputs_length`
projection (symmetrically) and retain the normalized capture parameters;
retirement payloads, packet boundaries, input order, and completion order are
not reconstructed.

## 2026-11-06-ls-sv2-180 — certify packet-window ROB input cardinality against ROB trace

Added `normalizeRvfiPacketWindows_robInputs_length_robTrace` and its append
form to `LeanModels/Refine/RvfiPacket.lean`.  A certified packet-window chain
now certifies equal generic ROB-input and ROB-retirement-trace cardinalities,
and adjacent chains compose the same bridge while retaining the carried state
boundary.  The PicoRV32 witness pins both forms.

**DECIDED:** reuse the exact generic `robTrace_length_eq_robInputs_length`
projection symmetrically after the window certificate supplies its carried
state; packet boundaries, source-input order, retirement payloads, and
completion order are not reconstructed.

## 2026-11-06-ls-sv2-181 — certify normalized ROB tag cardinality against packet trace

Added `normalizeRvfiPacketRobTags_length_packetTrace` and its append form to
`LeanModels/Refine/RvfiPacket.lean`.  A normalized packet capture now
certifies that the generic ROB tag stream has exactly the packet retirement
trace cardinality, and adjacent captures compose the bridge through their
retained state boundary.  The PicoRV32 witness pins both forms.

**DECIDED:** bridge the exact normalized generic ROB-tag cardinality through
the normalized packet-trace length equality; tag payloads, packet boundaries,
retirement order, and source-input order are not reconstructed.

## 2026-11-06-ls-sv2-182 — certify packet-window ROB tag cardinality against packet trace

Added `normalizeRvfiPacketWindows_rob_tags_length_packetTrace` and its append
form to `LeanModels/Refine/RvfiPacket.lean`.  A certified packet-window chain
now certifies that its generic ROB-tag stream has exactly the packet
retirement-trace cardinality, and adjacent chains compose the bridge through
their carried state boundary.  The PicoRV32 witness pins both forms.

**DECIDED:** flatten only through the existing packet-window certificate,
reuse the normalized ROB-tag/packet-trace cardinality bridge, and retain the
carried state; tag payloads, packet boundaries, retirement order, and
source-input order are not reconstructed.

## 2026-11-06-ls-sv2-183 — certify normalized ROB tag cardinality against packet inputs

Added `normalizeRvfiPacketRobTags_length_packetInputs` and its append form to
`LeanModels/Refine/RvfiPacket.lean`.  A normalized packet capture now
certifies that the generic ROB-tag stream has exactly the packet-input
cardinality, and adjacent captures compose the bridge through their retained
state boundary.  The PicoRV32 witness pins both forms.

**DECIDED:** take `List.length` of the exact normalized generic ROB-tag and
packet-input cardinalities and compose through normalized trace append; tag
payloads, packet boundaries, retirement order, and source-input order are not
reconstructed.

## 2026-11-06-ls-sv2-184 — certify packet-window ROB tag cardinality against packet inputs

The packet-window counterpart was included with the normalized ROB-tag/input
bridge: `normalizeRvfiPacketWindows_rob_tags_length_packetInputs` and its
append form are in `LeanModels/Refine/RvfiPacket.lean`, with PicoRV32
witnesses `pinned_packet_windows_rob_tags_length_packetInputs_chain` and
`pinned_packet_windows_rob_tags_length_packetInputs_append`.  A certified
window chain therefore carries the same exact ROB-tag/packet-input cardinality
through its flattened windows and through adjacent chains.

**DECIDED:** use the existing window certificate and retained state boundary;
do not reconstruct packet boundaries, tag payloads, retirement order, or
source-input order.

## 2026-11-06-ls-sv2-185 — certify normalized ROB tag cardinality against ROB trace

Added `normalizeRvfiPacketRobTags_length_robTrace` and its append form to
`LeanModels/Refine/RvfiPacket.lean`.  A normalized packet capture now
certifies equal cardinality for the generic ROB-tag stream and generic ROB
retirement trace, including adjacent captures.  The PicoRV32 witness pins
both forms.

**DECIDED:** compose the exact `robTags_length_eq_robInputs_length` and
`robTrace_length_eq_robInputs_length` projections; tag payloads, packet
boundaries, retirement order, and source-input order are not reconstructed.

## 2026-11-06-ls-sv2-186 — certify packet-window ROB tag cardinality against ROB trace

Added `normalizeRvfiPacketWindows_rob_tags_length_robTrace` and its append
form to `LeanModels/Refine/RvfiPacket.lean`.  A certified packet-window chain
now carries the exact generic ROB-tag/ROB-trace cardinality through its
flattened windows, and adjacent chains compose it through the retained state
boundary.  The PicoRV32 witness pins both forms.

**DECIDED:** flatten only through the existing packet-window certificate and
reuse the generic ROB-tag/ROB-trace cardinality bridge; packet boundaries, tag
payloads, retirement order, and source-input order are not reconstructed.

## 2026-11-06-ls-sv2-187 — certify normalized ROB tag cardinality against ROB inputs

Added `normalizeRvfiPacketRobTags_length_robInputs` and its append form to
`LeanModels/Refine/RvfiPacket.lean`.  A normalized packet capture now
certifies equal cardinality for the generic ROB-tag stream and generic ROB
input stream, including adjacent captures.  The PicoRV32 witness pins both
forms.

**DECIDED:** reuse the exact `robTags_length_eq_robInputs_length` projection;
tag payloads, packet boundaries, retirement order, and source-input order are
not reconstructed.

## 2026-11-06-ls-sv2-188 — certify packet-window ROB tag cardinality against ROB inputs

Added `normalizeRvfiPacketWindows_rob_tags_length_robInputs` and its append
form to `LeanModels/Refine/RvfiPacket.lean`.  A certified packet-window chain
now carries equal generic ROB-tag and generic ROB-input cardinalities through
flattening and adjacent retained state boundaries.  The PicoRV32 witness pins
both forms.

**DECIDED:** flatten only through the existing packet-window certificate and
reuse the generic ROB-tag/ROB-input cardinality bridge; packet boundaries, tag
payloads, retirement order, and source-input order are not reconstructed.

## 2026-11-06-ls-sv2-189 — certify normalized packet tag-stream cardinality against packet trace

Added `normalizeRvfiPacketTags_length_packetTrace` and its append form to
`LeanModels/Refine/RvfiPacket.lean`.  A normalized packet capture now
certifies equal cardinality for the packet-boundary tag stream and packet
retirement trace, including adjacent captures.  The PicoRV32 witness pins
both forms.

**DECIDED:** bridge the exact packet tag-stream width through the normalized
packet-trace length equality; packet boundaries, tag payloads, retirement
order, and source-input order are not reconstructed.

## 2026-11-06-ls-sv2-190 — certify packet-window tag-stream cardinality against packet trace

Added `normalizeRvfiPacketWindows_tags_length_packetTrace` and its append
form to `LeanModels/Refine/RvfiPacket.lean`.  A certified packet-window chain
now certifies equal cardinality for the packet-boundary tag stream and packet
retirement trace, including adjacent chains.  The PicoRV32 witness pins both
forms.

**DECIDED:** flatten only through the existing packet-window certificate and
reuse the normalized packet tag-stream/packet-trace cardinality bridge;
packet boundaries, tag payloads, retirement order, and source-input order are
not reconstructed.

## 2026-11-06-ls-sv2-191 — certify normalized packet tag-stream cardinality against packet inputs

Added `normalizeRvfiPacketTags_length_packetInputs` and its append form to
`LeanModels/Refine/RvfiPacket.lean`.  A normalized packet capture now
certifies equal cardinality for the packet-boundary tag stream and packet
input stream, including adjacent captures.  The PicoRV32 witness pins both
forms.

**DECIDED:** bridge through the exact normalized packet-trace/input
cardinality equality; packet boundaries, tag payloads, retirement order, and
source-input order are not reconstructed.

## 2026-11-06-ls-sv2-192 — certify packet-window tag-stream cardinality against packet inputs

Added `normalizeRvfiPacketWindows_tags_length_packetInputs` and its append
form to `LeanModels/Refine/RvfiPacket.lean`.  Certified packet-window chains
now determine equal cardinality for the packet-boundary tag stream and packet
input stream, including adjacent chains.  The PicoRV32 witness pins both
forms.

**DECIDED:** flatten only through the existing packet-window certificate and
reuse the normalized packet tag-stream/packet-input cardinality bridge;
packet boundaries, tag payloads, retirement order, and source-input order are
not reconstructed.

## 2026-11-06-ls-sv2-193 — certify packet tag-stream cardinality against ROB trace

Added `normalizeRvfiPacketTags_length_robTrace` and its append form to
`LeanModels/Refine/RvfiPacket.lean`.  A normalized packet tag stream now
certifies the exact generic ROB retirement-trace cardinality, including
adjacent captures.  The PicoRV32 witness pins both forms.

**DECIDED:** bridge through the exact normalized ROB-trace/packet-trace
cardinality equality; packet boundaries, tag payloads, retirement order, and
source-input order are not reconstructed.

## 2026-11-06-ls-sv2-194 — certify packet-window tag-stream cardinality against ROB trace

Added `normalizeRvfiPacketWindows_tags_length_robTrace` and its append form
to `LeanModels/Refine/RvfiPacket.lean`.  Certified packet-window chains now
determine the exact generic ROB retirement-trace cardinality of their
packet-boundary tag stream, including adjacent chains.  The PicoRV32 witness
pins both forms.

**DECIDED:** flatten only through the existing packet-window certificate and
reuse the normalized packet tag-stream/ROB-trace cardinality bridge; packet
boundaries, tag payloads, retirement order, and source-input order are not
reconstructed.

## 2026-11-06-ls-sv2-195 — certify normalized packet tag-stream cardinality against ROB inputs

Added `normalizeRvfiPacketTags_length_robInputs` and its append form to
`LeanModels/Refine/RvfiPacket.lean`.  A normalized packet tag stream now
certifies the exact generic ROB-input cardinality, including adjacent
captures.  The PicoRV32 witness pins both forms.

**DECIDED:** bridge through the exact normalized ROB-input/packet-input
cardinality equality; packet boundaries, tag payloads, retirement order, and
source-input order are not reconstructed.

## 2026-11-06-ls-sv2-196 — certify packet-window tag-stream cardinality against ROB inputs

Added `normalizeRvfiPacketWindows_tags_length_robInputs` and its append form
to `LeanModels/Refine/RvfiPacket.lean`.  Certified packet-window chains now
determine the exact generic ROB-input cardinality of their packet-boundary tag
stream, including adjacent chains.  The PicoRV32 witness pins both forms.

**DECIDED:** flatten only through the existing packet-window certificate and
reuse the normalized packet tag-stream/ROB-input cardinality bridge; packet
boundaries, tag payloads, retirement order, and source-input order are not
reconstructed.

## 2026-11-06-ls-sv2-197 — certify normalized packet tag-retirement cardinality against ROB trace

Added `normalizeRvfiPacketTags_retirements_length_robTrace` and its append
form to `LeanModels/Refine/RvfiPacket.lean`.  A normalized packet tag
retirement projection now certifies the exact generic ROB retirement-trace
cardinality, including adjacent captures.  The PicoRV32 witness pins both
forms.

**DECIDED:** bridge the exact normalized packet tag-retirement/packet-trace
cardinality through the generic ROB-trace/packet-trace equality; packet
boundaries, retirement payloads, retirement order, and source-input order are
not reconstructed.

## 2026-11-06-ls-sv2-198 — certify packet-window tag-retirement cardinality against ROB trace

Added `normalizeRvfiPacketWindows_tags_retirements_length_robTrace` and its
append form to `LeanModels/Refine/RvfiPacket.lean`.  Certified packet-window
chains now determine the exact generic ROB retirement-trace cardinality of
their packet-tag retirement projection, including adjacent chains.  The
PicoRV32 witness pins both forms.

**DECIDED:** flatten only through the existing packet-window certificate and
reuse the normalized packet tag-retirement/ROB-trace cardinality bridge;
packet boundaries, retirement payloads, retirement order, and source-input
order are not reconstructed.

## 2026-11-06-ls-sv2-199 — certify normalized packet tag-retirement cardinality against ROB inputs

Added `normalizeRvfiPacketTags_retirements_length_robInputs` and its append
form to `LeanModels/Refine/RvfiPacket.lean`.  A normalized packet tag-retirement
projection now certifies the exact generic ROB-input cardinality, including
adjacent captures.  The PicoRV32 witness pins both forms.

**DECIDED:** reuse the normalized packet tag-retirement/ROB-trace bridge and
the generic ROB trace/input length equality; packet boundaries, retirement
payloads, retirement order, and source-input order are not reconstructed.

## 2026-11-06-ls-sv2-200 — certify packet-window tag-retirement cardinality against ROB inputs

Added `normalizeRvfiPacketWindows_tags_retirements_length_robInputs` and its
append form to `LeanModels/Refine/RvfiPacket.lean`.  Certified packet-window
chains now determine the exact generic ROB-input cardinality of their
packet-tag retirement projection, including adjacent chains.  The PicoRV32
witness pins both forms.

**DECIDED:** flatten only through the existing packet-window certificate and
reuse the normalized packet tag-retirement/ROB-input cardinality bridge;
packet boundaries, retirement payloads, retirement order, and source-input
order are not reconstructed.

## 2026-11-06-ls-sv2-201 — certify normalized packet tag-retirement cardinality against packet inputs

Added `normalizeRvfiPacketTags_retirements_length_packetInputs` and its
append form to `LeanModels/Refine/RvfiPacket.lean`.  A normalized packet
tag-retirement projection now certifies the exact packet-input cardinality,
including adjacent captures.  The PicoRV32 witness pins both forms.

**DECIDED:** bridge the exact normalized packet tag-retirement/packet-trace
cardinality through normalized packet-input/packet-trace length equality;
packet boundaries, retirement payloads, retirement order, and source-input
order are not reconstructed.

## 2026-11-06-ls-sv2-202 — certify packet-window tag-retirement cardinality against packet inputs

Added `normalizeRvfiPacketWindows_tags_retirements_length_packetInputs` and
its append form to `LeanModels/Refine/RvfiPacket.lean`.  Certified
packet-window chains now determine the exact packet-input cardinality of their
packet-tag retirement projection, including adjacent chains.  The PicoRV32
witness pins both forms.

**DECIDED:** flatten only through the existing packet-window certificate and
reuse the normalized packet tag-retirement/packet-input cardinality bridge;
packet boundaries, retirement payloads, retirement order, and source-input
order are not reconstructed.

## 2026-11-06-ls-sv2-203 — certify normalized ROB-tag retirement cardinality against ROB inputs

Added `normalizeRvfiPacketRobTags_retirements_length_robInputs` and its
append form to `LeanModels/Refine/RvfiPacket.lean`.  A normalized packet
capture now certifies equal cardinality for the generic ROB-tag retirement
projection and generic ROB inputs, including adjacent captures.  The PicoRV32
witness pins both forms.

**DECIDED:** compose the exact tagged-retirement/ROB-trace cardinality with
the generic ROB-trace/ROB-input length equality; retirement payloads, packet
boundaries, retirement order, and source-input order are not reconstructed.

## 2026-11-06-ls-sv2-204 — certify packet-window ROB-tag retirement cardinality against ROB inputs

Added `normalizeRvfiPacketWindows_rob_tags_retirements_length_robInputs` and
its append form to `LeanModels/Refine/RvfiPacket.lean`.  Certified
packet-window chains now carry equal generic ROB-tag retirement and generic
ROB-input cardinalities through flattening and adjacent retained state
boundaries.  The PicoRV32 witness pins both forms.

**DECIDED:** flatten through the existing packet-window certificate and reuse
the generic tagged-retirement/ROB-input cardinality bridge; packet boundaries,
retirement payloads, retirement order, and source-input order are not
reconstructed.

## 2026-11-06-ls-sv2-205 — certify normalized ROB-tag retirement cardinality against packet inputs

Added `normalizeRvfiPacketRobTags_retirements_length_packetInputs` and its
append form to `LeanModels/Refine/RvfiPacket.lean`.  A normalized packet
capture now certifies equal cardinality for the generic ROB-tag retirement
projection and packet inputs, including adjacent captures.  The PicoRV32
witness pins both forms.

**DECIDED:** compose the exact generic ROB-tag retirement/ROB-input bridge
with the generic ROB-input/packet-input cardinality equality; retirement
payloads, packet boundaries, retirement order, and source-input order are not
reconstructed.

## 2026-11-06-ls-sv2-206 — certify packet-window ROB-tag retirement cardinality against packet inputs

Added `normalizeRvfiPacketWindows_rob_tags_retirements_length_packetInputs`
and its append form to `LeanModels/Refine/RvfiPacket.lean`.  Certified
packet-window chains now carry equal generic ROB-tag retirement and packet
input cardinalities through flattening and adjacent retained state boundaries.
The PicoRV32 witness pins both forms.

**DECIDED:** flatten through the existing packet-window certificate and reuse
the generic ROB-tag retirement/packet-input cardinality bridge; packet
boundaries, retirement payloads, retirement order, and source-input order are
not reconstructed.

## 2026-11-06-ls-sv2-207 — certify normalized ROB-tag input cardinality against ROB trace

Added `normalizeRvfiPacketRobTags_inputs_length_robTrace` and its append form
to `LeanModels/Refine/RvfiPacket.lean`.  A normalized packet capture now
certifies equal cardinality for the generic ROB-tag input projection and the
generic ROB retirement trace, including adjacent captures.  The PicoRV32
witness pins both forms.

**DECIDED:** compose the normalized ROB-tag input/ROB-input cardinality bridge
with the generic ROB-trace/ROB-input length equality; retirement payloads,
packet boundaries, retirement order, and source-input order are not
reconstructed.

## 2026-11-06-ls-sv2-208 — certify packet-window ROB-tag input cardinality against ROB trace

Added `normalizeRvfiPacketWindows_rob_tags_inputs_length_robTrace` and its
append form to `LeanModels/Refine/RvfiPacket.lean`.  Certified packet-window
chains now determine the exact generic ROB retirement-trace cardinality of
their tagged source-input projection, including adjacent chains.  The PicoRV32
witness pins both forms.

**DECIDED:** flatten through the existing packet-window certificate and reuse
the generic ROB-tag input/ROB-input cardinality bridge with the generic
ROB-trace/ROB-input length equality; packet boundaries, tag payloads,
retirement order, and source-input order are not reconstructed.

## 2026-11-06-ls-sv2-209 — certify normalized ROB-tag input cardinality against packet trace

Added `normalizeRvfiPacketRobTags_inputs_length_packetTrace` and its append
form to `LeanModels/Refine/RvfiPacket.lean`.  A normalized packet capture now
certifies equal cardinality for the generic ROB-tag input projection and the
packet-machine retirement trace, including adjacent captures.  The PicoRV32
witness pins both forms.

**DECIDED:** compose the normalized ROB-tag input/ROB-trace cardinality bridge
with the generic ROB-trace/packet-trace equality; retirement payloads, packet
boundaries, retirement order, and source-input order are not reconstructed.

## 2026-11-06-ls-sv2-210 — certify packet-window ROB-tag input cardinality against packet trace

Added `normalizeRvfiPacketWindows_rob_tags_inputs_length_packetTrace` and its
append form to `LeanModels/Refine/RvfiPacket.lean`.  Certified packet-window
chains now determine the exact packet-machine retirement-trace cardinality of
their tagged source-input projection, including adjacent chains.  The PicoRV32
witness pins both forms.

**DECIDED:** flatten through the existing packet-window certificate and reuse
the packet-window ROB-tag input/ROB-trace cardinality bridge with the generic
ROB-trace/packet-trace equality; packet boundaries, tag payloads, retirement
order, and source-input order are not reconstructed.

## 2026-11-06-ls-sv2-211 — certify normalized packet-tag input cardinality against ROB trace

Added `normalizeRvfiPacketTags_inputs_length_robTrace` and its append form to
`LeanModels/Refine/RvfiPacket.lean`.  A normalized packet-tag source-input
projection now certifies equal cardinality for the generic ROB retirement
trace, including adjacent captures.  The PicoRV32 witness pins both forms.

**DECIDED:** reuse the normalized generic ROB-tag input/ROB-trace cardinality
bridge after the packet-tag projection; packet boundaries, tag payloads,
retirement order, and source-input order are not reconstructed.

## 2026-11-06-ls-sv2-212 — certify packet-window packet-tag input cardinality against ROB trace

Added `normalizeRvfiPacketWindows_tags_inputs_length_robTrace` and its append
form to `LeanModels/Refine/RvfiPacket.lean`.  Certified packet-window chains
now determine the exact generic ROB retirement-trace cardinality of their
flattened packet-tag source-input projection, including adjacent chains.  The
PicoRV32 witness pins the chain and append forms.

**DECIDED:** flatten through the existing packet-window certificate and reuse
the normalized packet-tag input/ROB-trace cardinality bridge; packet
boundaries, tag payloads, retirement order, and source-input order are not
reconstructed.

## 2026-11-06-ls-sv2-213 — certify normalized packet-tag input cardinality against packet trace

Added `normalizeRvfiPacketTags_inputs_length_packetTrace` and its append form
to `LeanModels/Refine/RvfiPacket.lean`.  A normalized packet-tag source-input
projection now certifies equal cardinality for the packet-machine retirement
trace, including adjacent captures.  The PicoRV32 witness pins both forms.

**DECIDED:** reuse the normalized generic ROB-tag input/packet-trace
cardinality bridge after the packet-tag projection; packet boundaries, tag
payloads, retirement order, and source-input order are not reconstructed.

## 2026-11-06-ls-sv2-214 — certify packet-window packet-tag input cardinality against packet trace

Added `normalizeRvfiPacketWindows_tags_inputs_length_packetTrace` and its
append form to `LeanModels/Refine/RvfiPacket.lean`.  Certified packet-window
chains now determine the exact packet-machine retirement-trace cardinality of
their flattened packet-tag source-input projection, including adjacent chains.
The PicoRV32 witness pins the chain and append forms.

**DECIDED:** flatten through the existing packet-window certificate and reuse
the normalized packet-tag input/packet-trace cardinality bridge; packet
boundaries, tag payloads, retirement order, and source-input order are not
reconstructed.

## 2026-11-06-ls-sv2-215 — certify normalized packet-tag input cardinality against ROB inputs

Added `normalizeRvfiPacketTags_inputs_length_robInputs` and its append form to
`LeanModels/Refine/RvfiPacket.lean`.  A normalized packet-tag source-input
projection now certifies equal cardinality for generic ROB inputs, including
adjacent captures.  The PicoRV32 witness pins both forms.

**DECIDED:** reuse the normalized generic ROB-tag input/ROB-input cardinality
bridge after the packet-tag projection; packet boundaries, tag payloads,
retirement order, and source-input order are not reconstructed.

## 2026-11-06-ls-sv2-216 — certify packet-window packet-tag input cardinality against ROB inputs

Added `normalizeRvfiPacketWindows_tags_inputs_length_robInputs` and its
append form to `LeanModels/Refine/RvfiPacket.lean`.  Certified packet-window
chains now determine the exact generic ROB-input cardinality of their
flattened packet-tag source-input projection, including adjacent chains.  The
PicoRV32 witness pins the chain and append forms.

**DECIDED:** flatten through the existing packet-window certificate and reuse
the normalized packet-tag input/ROB-input cardinality bridge; packet
boundaries, tag payloads, retirement order, and source-input order are not
reconstructed.

## 2026-11-06-ls-sv2-217 — bridge normalized packet-tag retirements to packet trace

Added `normalizeRvfiPacketTags_retirements_packetTrace` and its append form to
`LeanModels/Refine/RvfiPacket.lean`.  A normalized packet-tag retirement
projection now identifies the exact packet-machine retirement trace, including
adjacent captures.  The PicoRV32 witness pins both forms.

**DECIDED:** compose the existing normalized packet-tag retirement payload and
packet-trace equalities; retirement order and payloads are preserved exactly,
and no new packet reconstruction is introduced.

## 2026-11-06-ls-sv2-218 — bridge packet-window packet-tag retirements to packet trace

Added `normalizeRvfiPacketWindows_tags_retirements_packetTrace` and its append
form to `LeanModels/Refine/RvfiPacket.lean`.  Certified packet-window chains
now identify the exact packet-machine retirement trace of their flattened
packet-tag retirement projection, including adjacent chains.  The PicoRV32
witness pins the chain and append forms.

**DECIDED:** flatten through the existing packet-window certificate and reuse
the normalized packet-tag retirement/packet-trace payload bridge; retirement
order and payloads are preserved exactly, with the carried state boundary
retained.

## 2026-11-06-ls-sv2-219 — bridge normalized packet-tag retirements to ROB trace

Added `normalizeRvfiPacketTags_retirements_robTrace` and its append form to
`LeanModels/Refine/RvfiPacket.lean`.  A normalized packet-tag retirement
projection now identifies the exact generic ROB retirement trace, including
adjacent captures.  The PicoRV32 witness pins both forms.

**DECIDED:** compose the packet-tag retirement/packet-trace payload equality
with the packetized RVFI-to-ROB trace projection; retirement order and payloads
remain exact, and no new reconstruction is introduced.

## 2026-11-06-ls-sv2-220 — bridge packet-window packet-tag retirements to ROB trace

Added `normalizeRvfiPacketWindows_tags_retirements_robTrace` and its append
form to `LeanModels/Refine/RvfiPacket.lean`.  Certified packet-window chains
now identify the exact generic ROB retirement trace of their flattened
packet-tag retirement projection, including adjacent chains.  The PicoRV32
witness pins the chain and append forms.

**DECIDED:** flatten through the existing packet-window certificate and reuse
the normalized packet-tag retirement/ROB-trace payload bridge; retirement
order and payloads remain exact, with the carried state boundary retained.

## 2026-11-06-ls-sv2-221 — bridge normalized ROB-tag retirements to packet trace

Added `normalizeRvfiPacketRobTags_retirements_packetTrace` and its append form
to `LeanModels/Refine/RvfiPacket.lean`. A normalized generic ROB-tag
retirement projection now identifies the exact packet-machine retirement trace,
including adjacent captures. The PicoRV32 witness pins both forms.

**DECIDED:** compose the existing normalized ROB-tag retirement payload and
packet-trace equalities; retirement order and payloads remain exact, and no new
packet reconstruction is introduced.

## 2026-11-06-ls-sv2-222 — bridge packet-window ROB-tag retirements to packet trace

Added `normalizeRvfiPacketWindows_rob_tags_retirements_packetTrace` and its
append form to `LeanModels/Refine/RvfiPacket.lean`. Certified packet-window
chains now identify the exact packet-machine retirement trace of their generic
ROB-tag retirement projection, including adjacent chains. The PicoRV32 witness
pins the chain and append forms.

**DECIDED:** flatten through the existing packet-window certificate and reuse
the normalized generic ROB-tag retirement/packet-trace payload bridge;
retirement order and payloads are preserved exactly, with the carried state
boundary retained.

## 2026-11-06-ls-sv2-223 — connect normalized packet-tag inputs to ROB inputs

Added `normalizeRvfiPacketTags_inputs_robInputs` and its append form to
`LeanModels/Refine/RvfiPacket.lean`. A normalized packet-tag source-input
projection now identifies the exact generic ROB input stream, including
adjacent captures. The PicoRV32 witness pins both forms.

**DECIDED:** compose the normalized packet-tag input/packet-input equality
with the packetized RVFI-to-ROB input bridge; source-input order and payloads
remain exact, and no packet reconstruction is introduced.

## 2026-11-06-ls-sv2-224 — connect packet-window packet-tag inputs to ROB inputs

Added `normalizeRvfiPacketWindows_tags_inputs_robInputs` and its append form
to `LeanModels/Refine/RvfiPacket.lean`. Certified packet-window chains now
identify the exact generic ROB input stream of their flattened packet-tag
source-input projection, including adjacent chains. The PicoRV32 witness pins
the chain and append forms.

**DECIDED:** flatten through the existing packet-window tag-input certificate
and compose it with the packetized RVFI-to-ROB input bridge; packet boundaries,
source-input order, and payloads remain exact, with the carried state boundary
retained.

## 2026-11-06-ls-sv2-225 — bridge normalized ROB trace to packet trace

Added `normalizeRvfiPacketRobTrace_packetTrace` and its append form to
`LeanModels/Refine/RvfiPacket.lean`. A successful normalized packet capture
now identifies the generic ROB retirement trace with the packet-facing
retirement trace, including adjacent captures. The PicoRV32 witness pins both
forms.

**DECIDED:** reuse the exact `toRobMachine_trace` projection after carrying
normalization through the append boundary; retirement payloads and order are
preserved without reconstructing either trace.

## 2026-11-06-ls-sv2-226 — bridge packet-window ROB trace to packet trace

Added `normalizeRvfiPacketWindows_rob_trace_packetTrace` and its append form
to `LeanModels/Refine/RvfiPacket.lean`. Certified packet-window chains now
identify the generic ROB retirement trace with the packet-facing retirement
trace, including adjacent chains. The PicoRV32 witness pins the chain and
append forms.

**DECIDED:** flatten through the existing packet-window certificate and reuse
the exact `toRobMachine_trace` projection; retirement payloads and order are
preserved without reconstructing either trace, with the carried state boundary
retained for the append form.

## 2026-11-06-ls-sv2-227 — bridge normalized ROB trace refinement to packet inputs

Added `normalizeRvfiPacketRobTrace_refines_packet` and its append form to
`LeanModels/Refine/RvfiPacket.lean`. A normalized ROB retirement capture now
exposes the ISA trace over the packet machine's architectural input stream,
including adjacent captures. The PicoRV32 witness pins both forms.

**DECIDED:** reuse the existing normalized ROB-trace/ROB-input refinement and
the exact `toRobMachine_inputs` projection; packet-input order and retirement
payloads are preserved without reconstructing either stream.

## 2026-11-06-ls-sv2-228 — bridge packet-window ROB trace refinement to packet inputs

Added `normalizeRvfiPacketWindows_rob_trace_refines_packet` and its append form
to `LeanModels/Refine/RvfiPacket.lean`. A certified packet-window ROB trace
now exposes the ISA trace over the packet machine's architectural input stream,
including adjacent certified chains. The PicoRV32 witness pins both forms.

**DECIDED:** flatten through the existing packet-window ROB-trace/ROB-input
refinement and apply the exact `toRobMachine_inputs` projection; packet-input
order and retirement payloads are preserved with the carried chain boundary.

## 2026-11-06-ls-sv2-229 — combine normalized ROB trace refinement with state transport

Added `normalizeRvfiPacketRobTrace_refines_state` and its append form to
`LeanModels/Refine/RvfiPacket.lean`. A normalized ROB retirement capture now
exposes both the ISA trace over generic ROB inputs and the final packet-machine
state/order relation. The PicoRV32 witness pins the single-window and adjacent
capture forms.

**DECIDED:** compose the existing normalized ROB-trace/ISA equality with the
state-threaded packet transport lemma; the exact ROB input boundary and
retirement order remain explicit, with no new state reconstruction.

## 2026-11-06-ls-sv2-230 — combine packet-window ROB trace refinement with state transport

Added `normalizeRvfiPacketWindows_rob_trace_refines_state` and its append form
to `LeanModels/Refine/RvfiPacket.lean`. Certified packet-window chains now
expose both the ISA trace over generic ROB inputs and the final packet-machine
state/order relation. The PicoRV32 witness pins the chain and adjacent-chain
forms.

**DECIDED:** compose the packet-window ROB-trace/ISA equality with the existing
flattened state transport through the normalization certificate; the generic
ROB input boundary and carried retirement order stay explicit.

## 2026-11-06-ls-sv2-231 — expose normalized ROB trace state refinement through packet state

Added `normalizeRvfiPacketRobTrace_refines_state_packet` and its append form to
`LeanModels/Refine/RvfiPacket.lean`. A normalized ROB retirement capture now
states both its ISA trace equality and final relation directly through the
packet machine's input and state projections. The PicoRV32 witness pins both
single-window and adjacent-capture forms.

**DECIDED:** transport the already-proved generic ROB trace/state contract
through the exact packet-machine projections; no new state or trace
reconstruction was introduced.

## 2026-11-06-ls-sv2-232 — expose packet-window ROB trace state refinement through packet state

Added `normalizeRvfiPacketWindows_rob_trace_refines_state_packet` and its
append form to `LeanModels/Refine/RvfiPacket.lean`. Certified packet-window
ROB traces now state both their ISA trace equality and final relation directly
through packet inputs and packet state. The PicoRV32 witness pins the chain
and adjacent-chain forms.

**DECIDED:** transport the certified generic ROB trace/state contract through
the exact packet-machine input and state projections; packet boundaries and
the carried retirement order remain unchanged.


## 2026-11-06-ls-sv2-233 — expose normalized ROB-tag state refinement through packet state

Added `normalizeRvfiPacketRobTags_refines_state_packet` and its append form to
`LeanModels/Refine/RvfiPacket.lean`. A normalized generic ROB-tag capture now
states its in-order tagged retirement/ISA equality together with the final
relation directly through packet state and packet inputs. The PicoRV32 witness
pins both the single capture and adjacent capture forms.

**DECIDED:** transport the existing normalized ROB-tag state contract through
exact packet-machine projections; tagged retirement order and the carried
state/order boundary remain unchanged.

## 2026-11-06-ls-sv2-234 — expose normalized ROB-tag window refinement through packet state

Added `normalizeRvfiPacketRobTags_refines_windows_packet` and its append form
to `LeanModels/Refine/RvfiPacket.lean`. A finite normalized ROB-tag window
chain now states its in-order tagged retirement/ISA equality and final relation
directly through packet inputs and packet state. The PicoRV32 witness pins the
chain and adjacent-chain forms.

**DECIDED:** flatten through the existing normalized ROB-tag window contract,
then apply exact packet input/state projections; tagged retirement order and
the carried state/order boundary remain unchanged.

## 2026-11-06-ls-sv2-235 — expose normalized ROB-tag refinement through packet inputs

Added `normalizeRvfiPacketRobTags_refines_packet` and its append form to
`LeanModels/Refine/RvfiPacket.lean`. A normalized generic ROB-tag retirement
contract now identifies the ISA trace over packet-machine inputs, including
adjacent captures. The PicoRV32 witness pins both forms.

**DECIDED:** reuse the existing ROB-tag order/refinement proof and apply the
exact `toRobMachine_inputs` projection; tagged retirement order and payloads
remain unchanged.

## 2026-11-06-ls-sv2-236 — expose normalized packet-tag refinement

Added `normalizeRvfiPacketTags_refines` and its append form to
`LeanModels/Refine/RvfiPacket.lean`. A normalized packet-boundary tag stream
now retains its `InOrderPacketStream` certificate while its flattened
retirement payload equals the ISA trace over packet-machine inputs, including
adjacent captures. The PicoRV32 witness pins both forms.

**DECIDED:** preserve packet boundaries for consumers that need per-cycle
commit widths, then use the exact ROB-tag and input projections for the ISA
trace; no new `_packet` alias or packet reconstruction was introduced.

## 2026-11-06-ls-sv2-237 — expose normalized packet-window tag refinement

Added `normalizeRvfiPacketWindows_tags_refines` and its append form to
`LeanModels/Refine/RvfiPacket.lean`. A finite normalized packet-window chain
now preserves its `InOrderPacketStream` boundary certificate while its
flattened packet-tag retirement payload equals the ISA trace over packet
inputs, including adjacent chains. The PicoRV32 witness pins both forms.

**DECIDED:** compose the exact window tag-stream and normalized trace bridges;
retain packet boundaries and carried state/order offsets without adding a
second ROB reconstruction or packet-facing alias.

## 2026-11-06-ls-sv2-238 — expose normalized packet-tag state refinement

Added `normalizeRvfiPacketTags_refines_state` and its append form to
`LeanModels/Refine/RvfiPacket.lean`. A normalized packet-boundary tag stream
now carries its in-order/ISA trace contract together with the final machine
state relation and retirement-order endpoint. The PicoRV32 witness pins both
single-capture and adjacent-capture forms.

**DECIDED:** compose the existing packet-tag refinement with the normalized
packet-state theorem, preserving exact packet inputs, state threading, and
retirement-order offsets without introducing a second state or trace model.

## 2026-11-06-ls-sv2-239 — expose normalized packet-window tag state refinement

Added `normalizeRvfiPacketWindows_tags_refines_state` and its append form to
`LeanModels/Refine/RvfiPacket.lean`. A certified finite packet-window chain
now combines its packet-boundary order/ISA trace contract with the final
machine-state relation and exact normalized retirement-order endpoint. The
PicoRV32 witness pins both the chain and adjacent-chain forms.

**DECIDED:** compose the existing packet-window tag refinement with the
state/order transport, retaining the original window boundaries, carried
state, and packet-input projection without introducing a second trace or
state model.

## 2026-11-06-ls-sv2-240 — expose normalized packet-tag state through packet state

Added `normalizeRvfiPacketTags_refines_state_packet` and its append form to
`LeanModels/Refine/RvfiPacket.lean`. A normalized packet-boundary tag/state
contract now exposes the final relation through `packetStateAfter`, while
retaining packet-tag order and ISA trace equality over packet inputs. The
PicoRV32 witness pins both single-capture and adjacent-capture forms.

**DECIDED:** apply the exact `toPacketMachine_stateAfter` projection to the
existing packet-tag state contract; packet boundaries, retirement payloads,
and carried order remain unchanged.

## 2026-11-06-ls-sv2-241 — expose normalized packet-window tag state through packet state

Added `normalizeRvfiPacketWindows_tags_refines_state_packet` and its append
form to `LeanModels/Refine/RvfiPacket.lean`. A certified packet-window tag
contract now exposes its final relation through `packetStateAfter`, retaining
packet-boundary order and ISA trace equality over packet inputs. The PicoRV32
witness pins both the finite chain and adjacent-chain forms.

**DECIDED:** apply the exact `toPacketMachine_stateAfter` projection to the
existing packet-window tag/state contract; window boundaries, retirement
payloads, carried state, and order offsets remain unchanged.

## 2026-11-06-ls-sv2-243 — expose packet-window tag refinement through ROB inputs

Added `normalizeRvfiPacketWindows_tags_refines_rob` and its append form to
`LeanModels/Refine/RvfiPacket.lean`. A certified finite packet-window tag
stream now retains its `InOrderPacketStream` certificate while its flattened
retirement payload equals the ISA trace over generic ROB inputs, including
adjacent certified chains. The PicoRV32 witness pins both forms.

**DECIDED:** flatten through the existing packet-window tag refinement and
apply the exact `toRobMachine_inputs` projection; window boundaries,
retirement payloads, carried state, and order offsets remain unchanged.

## 2026-11-06-ls-sv2-244 — expose packet-tag ROB-input state refinement

Added `normalizeRvfiPacketTags_refines_rob_state` and its append form to
`LeanModels/Refine/RvfiPacket.lean`. A normalized packet-boundary tag stream
now combines its `InOrderPacketStream`/ISA equality over generic ROB inputs
with the final packet-state relation and exact retirement-order endpoint,
including adjacent captures. The PicoRV32 witness pins both forms.

**DECIDED:** compose the packet-tag ROB-input projection with the existing
state-threaded normalization theorem; packet boundaries, retirement payloads,
state threading, and order offsets remain unchanged.

## 2026-11-06-ls-sv2-245 — choose PicoRV32 and state the real-core R2 theorem

The inbox was reread before this item.  The owner redirected this lane from the
packet-window projection matrix to R2's real-core result: choose the smallest
unmodified core that loads today, state the theorem exactly, and name the first
core invariant.  The existing generic memory/generate request in the `ls-sv`
inbox was reread; no new owner-lane request is needed here.

The selected core is YosysHQ PicoRV32, source commit
`ef203c2b0a3fb793280f5114941416c425c5b461`, under the ISC license, with the
single `picorv32` module and no RTL adaptation.  It is the only one of the
three candidates whose envelope loads today: CV32E40P stops at retained
`AlwaysPosedge` event semantics and Ibex at `AlwaysLatch`.  PicoRV32's current
canonical envelope is 3,178,052 bytes with SHA-256
`009cc39591b3fcb1c88403ca44f822cb1854d2ebc0b5c728c7cade06a2e47b1b`; its first
semantic wall remains the `cpuregs` unpacked memory, and the source-shaped
memory route still refuses generated members.  The older 3,181,105-byte hash
in the initial census was an earlier extractor snapshot and is now explicitly
identified as historical in the core census.

The theorem to prove is the following, stated over the exact SystemVerilog
semantics rather than a hand-built cycle model.  Let `pico` be the unmodified
pinned RTL instantiated at the RV32I/no-interrupt profile
(`COMPRESSED_ISA = 0`, `ENABLE_MUL = 0`, `ENABLE_FAST_MUL = 0`,
`ENABLE_DIV = 0`, `ENABLE_PCPI = 0`, `ENABLE_IRQ = 0`, `ENABLE_TRACE = 0`,
`ENABLE_COUNTERS = 0`, `ENABLE_COUNTERS64 = 0`, all 32 integer registers
enabled, and reset PC `0`; the remaining source parameters are pinned to their
declared defaults).  For every admissible reset state, RV32I program, initial
byte memory, and every legal memory response, event schedule, and 0/1
resolution of unknown bits, every finite completed E-run from reset satisfies

```text
rvfiRetirements run
  = trace (rvMachineWith picorv32Profile) isaInit (retirementInputs run)
∧ CoreIsaRel (finalCoreState run)
    (machineStateAfter (rvMachineWith picorv32Profile)
      isaInit (retirementInputs run))
```

Here `rvfiRetirements` is the order-checked RVFI stream (bubbles omitted only
by the existing normalizer), `retirementInputs` is the exact instruction and
byte-memory view at each completed retirement, and `CoreIsaRel` relates the
RTL architectural state—including its memory-visible effects—to the ISA state.
The run quantifier ranges over all resolutions admitted by E; it does not pick
one simulator schedule or one value for an unknown.  The theorem is scoped to
RV32I, no interrupts, minimal CSRs, and explicit trap boundaries; unsupported
extensions and traps outside that profile remain loud until their contracts are
added.

The first proof milestone is an RTL invariant for `ADDI`, quantified over every
program and every legal run.  At each instruction boundary, if the next valid
RVFI commit decodes as `addi rd, rs1, imm`, then its PC and instruction equal
the related ISA state's PC and fetched word, `pc_wdata = pc + 4`, its register
effect is `rd := (x[rs1] + signExtend(imm))` (or no write for `rd = x0`), its
memory masks and trap are empty, and the post-commit RTL state is related to
the ISA state after exactly one `isaStep` for that input.  The invariant also
preserves the byte memory and x0.  This is a genuine RTL boundary invariant;
it must be discharged from the loaded PicoRV32 state and not assumed as a
`RobStepRefines` hypothesis.

**DECIDED:** use PicoRV32 as the R2 target and make its whole-core theorem a
universal E-run/RV32I trace-and-final-state statement.  Build the `ADDI`
boundary invariant first; do not add another conditional packet projection or
call the existing finite RVFI witnesses a core theorem.

## 2026-11-06-ls-sv2-242 — expose normalized packet-tag refinement through ROB inputs

Added `normalizeRvfiPacketTags_refines_rob` and its append form to
`LeanModels/Refine/RvfiPacket.lean`. A normalized packet-boundary tag stream
now retains its `InOrderPacketStream` certificate while its flattened
retirement payload equals the ISA trace over the generic ROB input projection,
including adjacent captures. The PicoRV32 witness pins both forms.

**DECIDED:** reuse the packet-tag ISA refinement and apply the exact
`toRobMachine_inputs` projection; packet boundaries, retirement payloads,
and the carried state/order boundary remain unchanged.

## 2026-11-06-ls-sv2-246 — reproduce PicoRV32's generated-member memory wall

The inboxes were reread before this item.  The owner lane's next priority is
the generic wall that keeps PicoRV32's one-rank memory route from loading:
`instantiateMemD2` currently refuses any design whose memory declarations are
accompanied by generated members.  Two clean-room designs reproduce the wall
without changing the pinned core: `generate if` around a memory read and
`generate for` over generated taps.  Their loader declarations succeed, while
the memory route returns the exact refusal
`unsupported "Instantiate" "memory cycle route does not yet admit generate members"`.

The repros and their approved envelopes live under
`Examples/system-verilog/cores/picorv32/`; their hashes and `rfl` probes are
recorded in the PicoRV32 README.  A dated `REQUEST ls-sv:` asks the owner lane
to admit generated members in the existing memory route with exact
parameter/generate semantics, preserving a loud refusal outside the supported
shape and without lowering or unrolling the source.

**DECIDED:** treat this as generic loader/semantics work required by the real
PicoRV32 target.  No PicoRV32 RTL edit or core-specific workaround is allowed;
the R2 proof remains parked at this wall until the owner lane lands support.

## 2026-11-06-ls-sv2-247 — establish the RV32I ADDI architectural boundary

The inbox was reread before this item.  The generated-member request is now
parked with `ls-sv`; while the owner lane works on that generic wall, this item
moves the R2 proof forward in the owned refinement layer without constructing a
model of PicoRV32.

Added `LeanModels/Refine/Rv32i.lean` with the exact ADDI boundary contract:
`isaStepWith_addi` reduces every interrupt-free decoded 32-bit ADDI to its
architectural register update and `pc + 4`, `isaStepMemWith_addi` proves that
its byte memory is unchanged, and `rvMachineWith_addi` exposes the same result
as the RVFI-shaped `Retirement.ofRvStep` commit.  The decoder hypothesis is on
`Fetched.decode`, so a future loaded-core invariant must establish it from the
actual RTL instruction word.  `addiRetirement` is the reusable expected commit
and `addiNext`/`addiEffects` are the exact state/effect equations.

The PicoRV32-side witness
`Examples/system-verilog/cores/picorv32/addi_boundary.lean` pins the measured
`addi x1, x0, 5` word (`0x00500093`) and proves both the memory-threaded ISA
boundary and the generic commit boundary.  These are architecture-side
contracts only; no theorem assumes `RobStepRefines`, and no finite RVFI witness
is promoted to a core theorem.

**DECIDED:** make this exact ADDI contract the first proof target for the
future invariant extracted from loaded PicoRV32 state.  Keep the contract
profile-parametric and preserve the current no-interrupt/RV32I scope; generated
memory support remains an owner-lane prerequisite for the actual RTL proof.

## 2026-11-07-ls-sv2-248 — add the raw RVFI ADDI boundary predicate

The inboxes were reread before this item.  The owner lane still has the
generic generated-member memory request as its current `ls-sv` priority, so
this item advances only the owned refinement/API layer and does not adapt or
rewrite PicoRV32.

Added `LeanModels/Refine/RvfiAddi.lean` and exported it from
`LeanModels.Refine`.  `RvfiObservation.addiFields` records the exact raw
RVFI facts for an interrupt-free 32-bit `ADDI`: the input is the reported
32-bit word and decodes to the specified `rd`, `rs1`, and sign-extended
immediate; `pcWdata` is `pcRdata + 4`; the source and destination values match
the architectural state; mode/XLEN and masks are well formed; and trap,
interrupt, cause, and both data-memory masks are clear.  The enclosing
`RvfiObservation.addiBoundary` additionally requires the row's
`toRetirement?` to equal the reusable `addiRetirement`, so the raw bus cannot
silently disagree with the semantic commit.  The file also exposes the
profile-independent ADDI facts that memory is unchanged and x0 is preserved.

Added `rvfi_addi_boundary.lean` for the measured PicoRV32 RVFI row
`addi x1, x0, 5` at reset.  The axiom-free witness proves the full raw
predicate, projects its semantic equality and no-trap/no-memory facts, and
checks x0 preservation.  The README now points to this witness and the
reusable contract.

**MEASURED:** `slot-run.sh lake build LeanModels.Refine` and the focused
PicoRV32 witness build passed; direct elaboration of
`rvfi_addi_boundary.lean` passed.  The new theorem reports contain only the
existing `propext`/`Quot.sound` boundary and no `sorryAx`.  `python3
tools/docs_check.py`, `./tools/backlog-index.sh --check`, and `git diff --check`
pass.

**DECIDED:** keep raw wire checks and semantic equality in one reusable
predicate, leave `rdWdataValid` to the existing commit adapter's explicit
write-change semantics, and require the eventual loaded-core invariant to
establish this predicate from actual PicoRV32 state.  The generated-memory
loader wall remains the dependency for any symbolic RTL theorem.

## 2026-11-07-ls-sv2-249 — bridge the raw ADDI boundary to one ISA step

The inboxes were reread before this item.  The owner lane's generated-member
memory request is unchanged, so this item adds only owned refinement
infrastructure and does not bypass the blocked PicoRV32 loader route.

Extended `LeanModels/Refine/RvfiAddi.lean` with
`RvfiObservation.addiBoundary_isaStepMemWith` and
`RvfiObservation.addiBoundary_rvMachineWith`.  From the raw boundary
predicate, the first theorem derives the exact profile-parametric
`isaStepMemWith` result with the same fetched word, zero interrupt input, and
unchanged byte memory.  The second theorem derives the generic machine
adapter's `(addiNext, addiRetirement)` commit after normalizing the input
record, so a future loaded-core invariant can consume the raw RVFI facts
without restating the ISA calculation or assuming `RobStepRefines`.

The PicoRV32 witness now proves both derived equations for the measured reset
row in addition to the raw predicate, no-trap/no-memory projections, and x0
preservation.  The README records this direct raw-to-ISA bridge.

**DECIDED:** make the raw RVFI predicate the sole premise of the ADDI step
bridge.  Keep profile and memory explicit, preserve the no-interrupt/RV32I
scope, and leave the eventual RTL state relation to the loaded-core proof.

## 2026-11-07-ls-sv2-250 — exercise the ADDI boundary after state threading

The inboxes were reread before this item.  The owner lane still has no new
loader result, so this item validates the owned boundary against a later row
of the measured PicoRV32 stream rather than inventing a symbolic core state.

Extended `rvfi_addi_boundary.lean` with a state-threaded witness for the
measured `ADDI x3, x2, 1` row after the `ADDI/SW/LW` prefix.  The witness
retains the source fields that the compact five-row normalization fixture did
not need (`rs1_addr = 2`, `rs1_rdata = 5`), computes the architectural prefix
with `machineStateAfter`, and proves `pc = 12`, `x2 = 5`, and `x0 = 0`.  It
then proves the full raw `RvfiObservation.addiBoundary` and derives the exact
profile-parametric `isaStepMemWith` result for that non-reset state.

**DECIDED:** use the same raw-to-ISA predicate at reset and after a measured
memory-affecting prefix; keep state threading in the architectural machine
until the loaded PicoRV32 invariant can supply its own related state.

## 2026-11-07-ls-sv2-251 — establish the RV32I SW memory boundary

The inboxes were reread before this item.  The generated-member memory route
is still blocked in the owner lane, so this item advances the owned ISA/RVFI
contract needed for the measured PicoRV32 memory prefix.

Added `LeanModels/Refine/Rv32iMem.lean` with the exact profile-parametric
`SW` equations: the architectural state advances by four bytes without a
register update, the effect is one word write at `rs1 + imm` carrying `rs2`,
and `isaStepMemWith` applies that write through the byte-addressed
`storeVal`.  Added `LeanModels/Refine/RvfiMem.lean` with
`RvfiObservation.swBoundary`, which keeps the fetched decode, both source
register reads, effective address, `wmask = 0b1111`, write data, no register
write, and no trap alongside equality with `swRetirement`.

Added `rvfi_sw_boundary.lean` for the measured `SW x1, 0x100(x0)` row after
the first ADDI.  It computes the threaded state (`pc = 4`, `x1 = 5`, `x0 = 0`)
and proves the raw predicate, exact `storeVal` transition, and generic
`rvMachineWith` commit.  The theorem reports contain only the existing
`propext`/`Quot.sound` boundary and no `sorryAx`.

**DECIDED:** make the store boundary explicit before adding the load boundary;
the future loaded-core invariant must establish these raw source and memory
facts from PicoRV32's actual RVFI row.  No RTL, loader, or `LeanModels/Sv/**`
file changed.

## 2026-11-07-ls-sv2-252 — establish the RV32I LW memory boundary

The inboxes were reread before this item.  The generated-member memory route
is still parked with `ls-sv`, so this item completes the owned contract for
the measured load in the PicoRV32 prefix.

Extended `LeanModels/Refine/Rv32iMem.lean` with the exact unsigned word-load
state, read effect, retirement, profile-parametric step, memory-threaded
step, and `rvMachineWith` equations.  Extended `LeanModels/Refine/RvfiMem.lean`
with `RvfiObservation.lwBoundary`, retaining the source read, destination
writeback, effective address, `rmask = 0b1111`, returned memory data, clear
write mask, no trap, and semantic retirement equality.

Added `rvfi_lw_boundary.lean` for the measured `LW x2, 0x100(x0)` row after
the ADDI/SW prefix.  It proves the threaded state (`pc = 8`, `x1 = 5`,
`x0 = 0`), the raw boundary, the exact load result from `memFive`, and the
generic `rvMachineWith` commit.  The new theorem reports contain only the
existing `propext`/`Quot.sound` boundary and no `sorryAx`.

**DECIDED:** keep the load memory view explicit in both the architectural
state equation and the raw predicate; the eventual core invariant must relate
PicoRV32's returned bus data to this `loadVal` result.  No RTL, loader, or
`LeanModels/Sv/**` file changed.

## 2026-11-07-ls-sv2-253 — certify the stateful ADDI/SW/LW prefix

The inboxes were reread before this item.  The owner lane still has the
generated-member memory-route refusal, so this item composes the owned
stateful-memory adapter with the measured three-instruction prefix.

Added `rvfi_prefix_boundary.lean`, which evaluates the first `ADDI`, `SW`,
and `LW` rows through `rvMemoryMachineWith` from reset and proves the concrete
post-prefix state (`pc = 12`, `x2 = 5`, `x0 = 0`).  It also proves pointwise
that the threaded byte memory equals `memFive` (the view used by the measured
load and later `ADDI`).  This turns the previously abstract stateful-memory
equivalence into a concrete state relation without assuming a loaded RTL
invariant or changing the core source.

**DECIDED:** use the stateful memory machine for the prefix relation so the
future PicoRV32 invariant can connect its architectural memory to the same
`storeVal`/`loadVal` state before applying the ADDI boundary.  No RTL, loader,
or `LeanModels/Sv/**` file changed.

## 2026-11-07-ls-sv2-254 — extend the stateful prefix through ADDI x3

The inboxes were reread after item 253 was pushed; the generated-member
memory-route refusal is unchanged.  This item continues in the owned
stateful-memory witness rather than changing the blocked loader path.

Extended `rvfi_prefix_boundary.lean` with `fullState`, which threads the
measured fourth `ADDI x3, x2, 1` from the proved three-instruction state.  The
new theorem proves the final architectural values (`pc = 16`, `x2 = 5`,
`x3 = 6`, `x0 = 0`) and that the fourth instruction leaves the threaded memory
equal to `memFive`.  Its step equation is derived from the same exact
profile-parametric `isaStepWith` ADDI contract used by the earlier boundary.

**DECIDED:** keep the fourth instruction as a stateful machine step from
`prefixState`; this makes the complete measured non-trapping window explicit
while preserving the exact memory relation needed by a future core invariant.
No RTL, loader, or `LeanModels/Sv/**` file changed.

## 2026-11-07-ls-sv2-255 — connect the full stateful window to the observed trace

The inboxes were reread before this item.  The owner lane still reports the
generic generated-member memory-route refusal, so this item stays in the owned
stateful-memory and RVFI witness layer.

Extended `rvfi_prefix_boundary.lean` with three full-window bridges.  The
`pinned_full_state_machine` theorem exposes the final `fullState.arch` as the
stateless `rvMachineWith` state after the memory views generated by
`threadRvInputs`.  `pinned_full_window_trace` proves that the stateful machine
itself emits exactly the four measured non-trapping retirements, and
`pinned_full_window_observed` connects the normalized RVFI observations to
that stateful trace.  The README now records that the final architectural
state and the observed commit stream are one concrete four-instruction
certificate.

**DECIDED:** keep the stateful memory endpoint and the observation normalizer
linked through the existing `threadRvInputs` contract.  This gives the future
loaded-core invariant one window-level state/trace target without inventing a
second memory model or claiming symbolic RTL refinement.

## 2026-11-07-ls-sv2-256 — bridge raw ADDI rows into the stateful machine

The inboxes were reread before this item.  The owner lane's generated-member
memory-route refusal is unchanged, so this item remains in the owned RVFI and
stateful-memory contracts.

Added `RvfiObservation.addiBoundary_rvMemoryMachineWith` to the raw ADDI
predicate.  It consumes the same fetched/decode/interrupt-free facts as the
existing stateless bridge, applies the exact profile-parametric ADDI step to
`{ arch := s, memory := input.memory }`, and proves that the returned memory
is unchanged while the architectural state and retirement are `addiNext` and
`addiRetirement`.  The PicoRV32 witness exercises the theorem both at reset
and for the measured `ADDI x3, x2, 1` row after the ADDI/SW/LW prefix.

**DECIDED:** keep the raw RVFI predicate as the sole premise for both the
stateless and stateful ADDI bridges.  A future loaded-core invariant can now
consume a row while retaining its memory relation, with no duplicate semantic
step or hidden memory replacement.

## 2026-11-07-ls-sv2-257 — bridge raw SW and LW rows into the stateful machine

The inboxes were reread before this item.  The generated-member memory-route
wall remains with `ls-sv`, so this item extends only the owned RVFI and
stateful-memory contracts.

Added `RvfiObservation.swBoundary_rvMemoryMachineWith` and
`RvfiObservation.lwBoundary_rvMemoryMachineWith`.  The SW bridge consumes its
raw source/effective-address/write-mask facts and returns the exact
`storeVal`-updated byte memory with `swNext` and `swRetirement`; the LW bridge
retains the supplied memory while returning `lwNext` and `lwRetirement`.  The
PicoRV32 store and load witnesses exercise both bridges on the measured rows,
so the ADDI/SW/LW prefix now has raw-to-stateful contracts for every memory
operation it uses.

**DECIDED:** keep each raw RVFI predicate as the sole premise of its
stateful bridge and expose the memory transition explicitly.  This preserves
the exact load/store view needed by the eventual loaded-core invariant and
avoids a second memory semantics or implicit bus-data substitution.

## 2026-11-07-ls-sv2-258 — bundle the raw and stateful window certificate

The inboxes were reread before this item.  The generated-member memory-route
wall remains with `ls-sv`, so this item stays in the owned RVFI/stateful-memory
layer.

Added `pinned_raw_stateful_window_certificate` to
`rvfi_prefix_boundary.lean`.  Its first component retains the four measured
raw RVFI predicates (`ADDI`, `SW`, `LW`, and the post-prefix `ADDI`); its
second component gives the corresponding `rvMemoryMachineWith` state and
retirement equations.  The focused proof compiles with only the existing
`propext`/`Quot.sound` boundary and no `sorryAx`.

**DECIDED:** expose one reusable concrete certificate that lets a future
loaded-core invariant consume both the wire-level facts and the exact
state-threaded memory transition for the complete measured window.  The
invalid proposition `#guard` was removed; no RTL, loader, or
`LeanModels/Sv/**` file changed.

## 2026-11-07-ls-sv2-259 — require valid RVFI rows to normalize before cycle refinement

The inboxes were reread before this item.  The owner lane's generated-member
memory-route refusal is unchanged, and its CombView migration remains owner
work, so this item advances the owned generic refinement boundary only.

Added `RvfiCycleStepRefines` to `LeanModels/Refine/Rvfi.lean`.  It states the
cycle simulation directly over packed RVFI observations: invalid rows stutter,
while every valid row must produce a `toRetirement?` result equal to the ISA
step's retirement and carry the state relation forward.  Thus a malformed
valid row cannot become a bubble through the optional-retirement projection.
The theorem `rvfiCycleStepRefines_toCycleStepRefines` proves that this strict
raw contract implies the existing `CycleStepRefines` interface, preserving all
trace and state transport theorems for downstream core proofs.  The theorem's
axiom report contains only the existing `propext`/`Quot.sound` boundary.

**DECIDED:** make raw RVFI validity a proof obligation at the loaded-core
boundary and retain the optional adapter only as a derived view.  No RTL,
loader, or `LeanModels/Sv/**` file changed.

## 2026-11-07-ls-sv2-260 — transport trace and state directly from strict RVFI refinement

The inboxes were reread before this item.  The owner lane still has the
generated-member memory-route refusal, and its CombView migration remains
outside this lane.

Added `rvfiCycleStepRefines_trace_refines` and
`rvfiCycleStepRefines_stateAfter_refines` to `LeanModels/Refine/Rvfi.lean`.
They consume the strict raw packed-cycle contract from item 259 and expose,
respectively, the finite retirement trace equality and the retained
post-window relation.  Both wrappers derive the existing generic cycle
theorems through `rvfiCycleStepRefines_toCycleStepRefines`, so a core proof can
start with raw RVFI validity and then use trace/state transport without a
second hand-written adapter step.  The new theorem reports contain only the
existing `propext`/`Quot.sound` boundary.

**DECIDED:** make the strict raw contract the single entry point for the
loaded-core trace and state obligations; keep the optional adapter as an
internal derivation.  No RTL, loader, or `LeanModels/Sv/**` file changed.

## 2026-11-07-ls-sv2-261 — compose strict RVFI refinement with raw normalization

The inboxes were reread before this item.  No newer lane-specific request was
present: the generated-member memory-route wall remains with `ls-sv`, while
this lane continues the owned generic refinement boundary.

Added `rvfiCycleStepRefines_normalized_trace_refines` to
`LeanModels/Refine/Rvfi.lean`.  Given the strict packed-cycle contract, the
admitted input window, and a successful `normalizeRvfiTrace?` certificate, it
returns the normalized retirement list's equality with the ISA trace over the
retiring inputs.  The proof composes `normalizeRvfiCycleTrace` with the strict
trace wrapper; malformed valid rows remain rejected by the normalization
certificate rather than being repaired by the optional adapter.

Added `pinned_cycle_normalized_trace_refines_of` to the PicoRV32 trace witness.
It instantiates the composition on the measured eight-cycle window while
leaving the symbolic relation and admission predicate as the hypotheses that
the eventual loaded-core invariant must discharge.  No RTL, loader, or
`LeanModels/Sv/**` file changed.

**DECIDED:** keep raw normalization and architectural refinement as separate
obligations, with one theorem composing them at the loaded-core boundary.  A
successful wire certificate now leads directly to the ISA trace without a
manual optional-retirement adapter step.

## 2026-11-07-ls-sv2-262 — certify normalized RVFI retirement counts

The inboxes were reread before this item.  No newer lane-specific request was
present: generated members in the memory route remain an `ls-sv` dependency.

Added the generic `cycleTrace_length_eq_retireInputs_length` lemma to
`LeanModels/Refine/Cycle.lean`, then lifted it through
`normalizeRvfiCycleTrace_input_length` in `LeanModels/Refine/Rvfi.lean`.
Whenever raw RVFI normalization succeeds, the retained cycle inputs and the
decoded retirement list therefore have identical lengths.  The PicoRV32 trace
witness records this fact for the measured bubble/interleaved eight-cycle
window, providing the order-count premise needed by adjacent-window proofs.
No RTL, loader, or `LeanModels/Sv/**` file changed.

**DECIDED:** keep retirement-count transport as a generic cycle fact and make
normalization consume it, rather than deriving counts from a particular core's
order fields or from a filtered list implementation.

## 2026-11-07-ls-sv2-263 — bundle the strict normalized RVFI boundary

The inboxes were reread before this item.  No newer lane-specific request was
present: generated-member support in the memory route remains with `ls-sv`.

Added `rvfiCycleStepRefines_normalized` to `LeanModels/Refine/Rvfi.lean`.
It packages the strict contract's normalized ISA trace equality and its
state-threaded post-window relation, while retaining the successful raw
normalization certificate and input-admission proof as explicit premises.
Added `pinned_cycle_normalized_refines_of` to the PicoRV32 witness, fixing the
pair on the measured eight-cycle machine and leaving the symbolic invariant
as the hypothesis the loaded-core proof must establish.  No RTL, loader, or
`LeanModels/Sv/**` file changed.

**DECIDED:** expose one complete raw-to-ISA/state boundary for a loaded-core
window, but keep trace normalization and step refinement as separate premises
inside its proof so malformed valid rows remain loud.

## 2026-11-07-ls-sv2-264 — compose strict normalized RVFI windows

The inboxes were reread before this item.  No newer lane-specific request was
present: generated-member support in the memory route remains with `ls-sv`.

Added `rvfiCycleStepRefines_normalized_append` to
`LeanModels/Refine/Rvfi.lean`.  It combines two successful raw normalization
certificates, with the second certificate starting at the first retirement
count, and applies the strict contract to the concatenated cycle stream.  The
result retains both the concatenated ISA trace equality and the final
state relation.  The PicoRV32 witness `pinned_cycle_normalized_append_refines_of`
exercises this on the measured first/second window split.  No RTL, loader, or
`LeanModels/Sv/**` file changed.

**DECIDED:** preserve normalization boundaries when composing windows, while
using one strict refinement proof over the concatenated stream so no local
window can silently weaken the raw valid-row obligation.

## 2026-11-07-ls-sv2-265 — expose the normalized window-chain boundary

The inboxes and goal file were reread before this item.  Generated-member
support in the memory route remains an `ls-sv` dependency.

Added `rvfiCycleStepRefines_normalized_chain` to
`LeanModels/Refine/Rvfi.lean`.  It exposes both normalized windows separately:
the first retirement equality and post-window relation, followed by the
second retirement equality from the ISA state reached by the first window and
the final relation.  The second proof therefore resumes at the exact
state-threaded boundary rather than reconstructing the prefix.  The
PicoRV32 witness `pinned_cycle_normalized_chain_refines_of` instantiates all
four facts for the measured split, with separate admission premises for the
two windows.  No RTL, loader, or `LeanModels/Sv/**` file changed.

**DECIDED:** keep the segmented boundary explicit in the generic contract.
The concatenated theorem remains available, while loaded-core invariants can
now discharge and reuse one normalized window at a time.

## 2026-11-07-ls-sv2-266 — project valid RVFI rows to concrete retirements

The inboxes and goal file were reread before this item.  The generated-member
memory-route refusal remains with `ls-sv`.

Added `rvfiCycleStepRefines_valid_step` to `LeanModels/Refine/Rvfi.lean`.
For a strict-contract cycle known to have `valid = true`, it proves the raw
observation is `wellFormed`, transports the state relation through that cycle,
and identifies the observation's concrete `toRetirement` with the ISA step's
retirement.  The proof uses a direct `Bool` split on the executable
well-formedness flag, so the theorem adds no classical-choice dependency.
Updated the PicoRV32 README and backlog/index.  No RTL, loader, or
`LeanModels/Sv/**` file changed.

**DECIDED:** make the strict raw-row boundary expose the concrete packed
retirement directly.  Future loaded-core invariants can consume validity and
well-formedness as proved facts instead of reopening the optional adapter.

## 2026-11-07-ls-sv2-267 — project invalid RVFI rows to stuttering

The inboxes and goal file were reread before this item.  The generated-member
memory-route refusal remains with `ls-sv`.

Added `rvfiCycleStepRefines_invalid_step` to `LeanModels/Refine/Rvfi.lean`.
For a strict-contract cycle known to have `valid = false`, it directly
transports the core relation across the cycle and leaves the ISA state
unchanged.  This is the bubble-side companion to the valid-row projection,
and the PicoRV32 README records the pair as the per-cycle raw boundary.  No
RTL, loader, or `LeanModels/Sv/**` file changed.

**DECIDED:** expose both strict branches as named projections.  Loaded-core
proofs can now handle every raw cycle through explicit valid-retirement or
invalid-stutter facts without reopening the contract's branch or silently
dropping a row.

## 2026-11-07-ls-sv2-268 — certify well-formed rows in normalized streams

The inboxes and goal file were reread before this item.  The generated-member
memory-route refusal remains with `ls-sv`.

Added the adapter inversion lemma
`RvfiObservation.wellFormed_of_toRetirement?_eq_some` and
`normalizeRvfiTrace?_wellFormed` to `LeanModels/Refine/Rvfi.lean`.  A
successful executable normalization now proves, for every raw row, either
`valid = false` or `wellFormed`; the proof follows the checker directly and
does not use the existing classical certificate-equivalence theorem.  The
strict valid-row projection reuses the inversion lemma.  Updated the PicoRV32
README and backlog/index.  No RTL, loader, or `LeanModels/Sv/**` file changed.

**DECIDED:** make raw normalization itself carry the wire well-formedness
certificate.  The loaded-core proof can now separate malformed-valid refusal
from explicit bubbles before applying architectural refinement.
