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
