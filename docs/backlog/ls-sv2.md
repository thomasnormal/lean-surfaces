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
