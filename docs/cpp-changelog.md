# C++ tier changelog

The C++ tier has its own prerelease line because its surface and measured
coverage advance independently from the Python tier.

## [Unreleased]

## [0.1.0] — 2026-10-22

### Added

- A pinned differential and Clang AST grammar harness, with generated coverage
  and rung-status pages.
- Translation-unit root admission and a rung-1 integral object store covering
  static, thread, automatic, and dynamic storage identities.
- Typed scalar initialization and assignment through borrowed object references,
  including source conversion, shared readback, const-write refusal, and stale
  lifetime/released-storage refusal.
- Kernel-reduced lifecycle witnesses and native C++ probes for the admitted
  boundaries.

### Measured

- The checked-in corpus contains 11 differential rows and 24 grammar witnesses.
  This host has no pinned Clang/LLVM 21.1.8, so the run reports 0 MATCH,
  0 DIVERGE, 0 REFUSE, 0 TIMEOUT, and 11 ORACLE rows; grammar reports 24
  ORACLE rows. Missing oracle inputs are kept explicit rather than counted as
  agreement.
