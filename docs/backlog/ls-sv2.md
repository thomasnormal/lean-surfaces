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
