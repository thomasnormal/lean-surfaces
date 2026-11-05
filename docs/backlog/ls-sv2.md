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
