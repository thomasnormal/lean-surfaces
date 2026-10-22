# C++ tier changelog

The C++ tier has its own prerelease line because its surface and measured
coverage advance independently from the Python tier.

## [Unreleased]

## [0.1.5] — 2026-10-22

### Added

- Rung-4 callable witnesses for void returns, forward `goto`/labels, automatic
  local declarations, and nested compound-block scope cleanup.

### Measured

- The checked-in corpus now contains 35 differential rows and 24 grammar
  witnesses. With pinned Clang/LLVM 21.1.8 unavailable, the run reports 0
  MATCH, 0 DIVERGE, 0 REFUSE, 0 TIMEOUT, and 35 ORACLE rows; grammar reports
  24 ORACLE rows.

## [0.1.4] — 2026-10-22

### Added

- Rung-4 callable witnesses for `if`, `while`, `do`/`while`, `for`, `break`,
  and `continue`, alongside the existing switch boundary.

### Measured

- The checked-in corpus now contains 30 differential rows and 24 grammar
  witnesses. With pinned Clang/LLVM 21.1.8 unavailable, the run reports 0
  MATCH, 0 DIVERGE, 0 REFUSE, 0 TIMEOUT, and 30 ORACLE rows; grammar reports
  24 ORACLE rows.

## [0.1.3] — 2026-10-22

### Added

- Rung-3 callable witnesses for logical `&&`/`||` short circuiting, plain
  assignment, and direct helper calls with integral arguments.
- A rung-4 switch statement witness covering case selection and the default
  arm, plus Boolean statement probes in the differential harness.

### Measured

- The checked-in corpus now contains 24 differential rows and 24 grammar
  witnesses. With pinned Clang/LLVM 21.1.8 unavailable, the run reports 0
  MATCH, 0 DIVERGE, 0 REFUSE, 0 TIMEOUT, and 24 ORACLE rows; grammar reports
  24 ORACLE rows.

## [0.1.2] — 2026-10-22

### Added

- Rung-3 callable witnesses for prefix and postfix increment, comma
  sequencing, compound assignment, and conditional branch selection.
- Native differential rows for the admitted callable expression boundaries.

### Measured

- The checked-in corpus now contains 19 differential rows and 24 grammar
  witnesses. With pinned Clang/LLVM 21.1.8 unavailable, the run reports 0
  MATCH, 0 DIVERGE, 0 REFUSE, 0 TIMEOUT, and 19 ORACLE rows; grammar reports
  24 ORACLE rows.

## [0.1.1] — 2026-10-22

### Added

- Rung-1 witnesses for vacuous default initialization and its
  uninitialized-read refusal.
- Rung-2 scalar conversion, width and promotion evidence, plus rung-3 defined
  integral expression, unary and shift witnesses with explicit undefined-case
  outcomes.
- Scalar and expression check rows in the differential harness, alongside the
  existing lifecycle and callable rows.

### Measured

- The checked-in corpus now contains 15 differential rows and 24 grammar
  witnesses. With pinned Clang/LLVM 21.1.8 unavailable, the run reports 0
  MATCH, 0 DIVERGE, 0 REFUSE, 0 TIMEOUT, and 15 ORACLE rows; grammar reports
  24 ORACLE rows.

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
