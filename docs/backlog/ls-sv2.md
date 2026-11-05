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
