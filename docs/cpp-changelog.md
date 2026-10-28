# C++ tier changelog

The C++ tier has its own prerelease line because its surface and measured
coverage advance independently from the Python tier.

## [Unreleased]

## [0.1.144] — 2026-10-28

### Added

- Added five callable statement witnesses for selected and nonselected
  standalone `switch` initialization, assignment, return, and fallthrough
  paths.

### Measured

- The checked-in corpus now contains **885 differential rows**: **868 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.143] — 2026-10-28

### Added

- Added ten callable statement witnesses for nonselected standalone `switch`
  paths covering direct and computed initialization, assignment, return, and
  fallthrough cases.

### Measured

- The checked-in corpus now contains **879 differential rows**: **862 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.142] — 2026-10-28

### Added

- Added one callable statement witness for a nonselected default-shadow
  initialization fallthrough assignment path in a standalone `switch`.

### Measured

- The checked-in corpus now contains **868 differential rows**: **851 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.141] — 2026-10-27

### Added

- Added five callable statement witnesses for nonselected computed return and
  assignment-return paths across standalone `switch` and its `default` arm.

### Measured

- The checked-in corpus now contains **863 differential rows**: **846 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.140] — 2026-10-27

### Added

- Added six callable statement witnesses for computed case-local fallthrough
  and nonselected default-shadow initialization paths across standalone
  `switch` and `for`, `while`, and `do while` loops.

### Measured

- The checked-in corpus now contains **857 differential rows**: **840 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.139] — 2026-10-27

### Added

- Added five callable statement witnesses for nonselected computed shadow
  initialization paths where a `default` arm falls through to a later `case`,
  covering standalone `switch` and `for`, `while`, and `do while` loops.

### Measured

- The checked-in corpus now contains **851 differential rows**: **834 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.138] — 2026-10-27

### Added

- Added five callable statement witnesses for nonselected case paths in
  switch fallthrough, covering direct and computed shadow initialization in
  `for`, `while`, and `do while`.

### Measured

- The checked-in corpus now contains **846 differential rows**: **829 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.137] — 2026-10-27

### Added

- Added five callable statement witnesses for computed shadow initialization
  and assignment that falls through from a selected `case` to `default` in
  `for`, `while`, and the standalone switch contexts.

### Measured

- The checked-in corpus now contains **841 differential rows**: **824 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.136] — 2026-10-27

### Added

- Added five callable statement witnesses for nonterminal `default` labels
  that fall through to later `case` labels, including computed shadow
  initialization and the `for`, `while`, `do while`, and standalone switch
  contexts.

### Measured

- The checked-in corpus now contains **836 differential rows**: **819 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.135] — 2026-10-27

### Added

- Added five callable statement witnesses for shadow-local assignments and
  switch fallthrough nested under `for`, `while`, and `do while`, covering
  default-arm transfers and case-to-default fallthrough.

### Measured

- The checked-in corpus now contains **831 differential rows**: **814 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.134] — 2026-10-27

### Added

- Added a callable `do while` statement witness for a nonselected `switch`
  default arm with shadow-local initialization, assignment, and loop
  completion.

### Measured

- The checked-in corpus now contains **826 differential rows**: **809 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.133] — 2026-10-27

### Added

- Added five callable statement witnesses for shadow-local assignments in
  selected and default `switch` arms nested under `for`, `while`, and `do …
  while`, covering ordinary assignment, return, and nonselected paths.

### Measured

- The checked-in corpus now contains **818 differential rows**: **801 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.132] — 2026-10-27

### Added

- Added five callable statement witnesses for computed shadow-local
  assignments in selected `switch` arms nested under `for`, covering
  assignment, return, nonselected, `continue`, and enclosing-loop `break`
  paths.

### Measured

- The checked-in corpus now contains **813 differential rows**: **796 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.131] — 2026-10-27

### Added

- Added five callable statement witnesses for computed shadow-local
  assignments in selected `switch` arms nested under `while`, covering
  assignment, return, nonselected, `continue`, and enclosing-loop `break`
  paths.

### Measured

- The checked-in corpus now contains **808 differential rows**: **791 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.130] — 2026-10-27

### Added

- Added five callable statement witnesses for computed shadow-local
  assignments in selected `switch` arms nested under `do … while`, covering
  assignment, return, nonselected, `continue`, and enclosing-loop `break`
  paths.

### Measured

- The checked-in corpus now contains **803 differential rows**: **786 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.129] — 2026-10-27

### Added

- Added five callable statement witnesses for computed shadow-local
  assignments in `switch` default arms nested under `for` and `while`,
  covering assignment, return, nonselected, `continue`, and `break` paths.

### Measured

- The checked-in corpus now contains **798 differential rows**: **781 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.128] — 2026-10-27

### Added

- Added five callable statement witnesses for computed shadow-local
  assignments in `switch` default arms nested under `for` and `while`,
  covering assignment, return, nonselected, and loop-exit paths.

### Measured

- The checked-in corpus now contains **793 differential rows**: **776 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.127] — 2026-10-27

### Added

- Added five callable statement witnesses for computed shadow-local
  assignments in `switch` default arms nested under `do … while`, covering
  return, nonselected, `continue`, and enclosing-loop `break` paths.

### Measured

- The checked-in corpus now contains **788 differential rows**: **771 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.126] — 2026-10-27

### Added

- Added six callable statement witnesses for shadow-local assignments in
  switches nested under `for`, `while`, and `do … while`, covering selected
  and nonselected cases plus default-arm assignment paths.

### Measured

- The checked-in corpus now contains **783 differential rows**: **766 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.125] — 2026-10-27

### Added

- Added five callable statement witnesses for shadow-local assignments in
  switches nested under `for`, `while`, and `do … while`, covering return,
  continue, and switch-owned break propagation.

### Measured

- The checked-in corpus now contains **777 differential rows**: **760 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.124] — 2026-10-27

### Added

- Added five callable statement witnesses for shadow-local assignments in
  switch fallthrough and nested loop control flow, covering `continue` and
  switch-owned `break` propagation through `for`, `while`, and `do … while`.

### Measured

- The checked-in corpus now contains **772 differential rows**: **755 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.123] — 2026-10-27

### Added

- Added five callable statement witnesses for switch shadow-local
  initialization, fallthrough, assignment, return, and false-selection paths,
  including default arms.

### Measured

- The checked-in corpus now contains **767 differential rows**: **750 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.122] — 2026-10-27

### Added

- Added five callable statement witnesses for shadowed local-initialization
  assignment and return paths across `for`, `while`, `do … while`, and
  `switch` control flow, including switch default arms.

### Measured

- The checked-in corpus now contains **762 differential rows**: **745 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.121] — 2026-10-27

### Added

- Added thirteen callable statement witnesses for local-initialization
  assignment paths across `switch`, `while`, `do … while`, and `for`, covering
  shadowed locals, default arms, and return, `continue`, and `break` transfers.

### Measured

- The checked-in corpus now contains **757 differential rows**: **740 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.120] — 2026-10-27

### Added

- Added ten callable statement witnesses for plain local-initialization
  assignment paths across `switch`, `while`, `do … while`, and `for`, covering
  return, `continue`, and `break` transfers.

### Measured

- The checked-in corpus now contains **744 differential rows**: **727 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.119] — 2026-10-27

### Added

- Added five callable statement witnesses for plain local initialization in
  `for` and `switch` statements, covering case/default return and assignment
  paths.

### Measured

- The checked-in corpus now contains **734 differential rows**: **717 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.118] — 2026-10-26

### Added

- Added eight callable statement witnesses for assignment-return paths in
  `switch` (including default and fallthrough), conditionals (including
  computed initializers and `else`), `for`, and `do … while` constructs.

### Measured

- The checked-in corpus now contains **724 differential rows**: **707 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.117] — 2026-10-26

### Added

- Added five callable statement witnesses for shadow-computed assignment
  transfers: `while` return, `do … while` continue/break/return, and `switch`
  return paths.

### Measured

- The checked-in corpus now contains **716 differential rows**: **699 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.116] — 2026-10-26

### Added

- Added five callable statement witnesses for shadow-computed assignment paths
  in `for` and `while` loops, covering `continue`, `break`, and `return`
  transfer behavior.

### Measured

- The checked-in corpus now contains **711 differential rows**: **694 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.115] — 2026-10-26

### Added

- Added eight callable statement witnesses for single-iteration and transfer
  paths in shadow-computed `while`, `do … while`, and `for` loops, including
  nested scope cleanup and assignment behavior.

### Measured

- The checked-in corpus now contains **706 differential rows**: **689 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.114] — 2026-10-26

### Added

- Added six callable statement witnesses for nested shadow-computed local
  initialization across `for`, `switch`, and conditional assignment paths,
  including false and zero-iteration branches.

### Measured

- The checked-in corpus now contains **697 differential rows**: **680 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.113] — 2026-10-26

### Added

- Added five callable statement witnesses for shadow-computed local
  initialization across conditional false paths and `for` loops, including
  assignment and zero-iteration behavior.

### Measured

- The checked-in corpus now contains **691 differential rows**: **674 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.112] — 2026-10-26

### Added

- Added five callable statement witnesses for `switch` shadow-computed
  assignment and return paths, including case/default selection and false
  paths.

### Measured

- The checked-in corpus now contains **686 differential rows**: **669 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.111] — 2026-10-26

### Added

- Added five callable statement witnesses for shadow-computed assignment in
  `do … while`, `switch`, and conditional branches, including a conditional
  false path.

### Measured

- The checked-in corpus now contains **681 differential rows**: **664 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.110] — 2026-10-26

### Added

- Added eighteen object-frame witnesses for nested shadow-computed local
  initialization across conditional and switch-default paths, including
  assignment, `return`, and false-branch transfers, plus direct `while`
  initialization and shadow-computed assignment/zero-iteration paths.

### Measured

- The checked-in corpus now contains **676 differential rows**: **659 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.109] — 2026-10-26

### Added

- Added five object-frame witnesses for nested shadow-computed local
  initialization across `switch` and conditional branches, including switch
  fallthrough and `return` transfer.

### Measured

- The checked-in corpus now contains **658 differential rows**: **641 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.108] — 2026-10-26

### Added

- Added five object-frame witnesses for nested shadow-computed local
  initialization through `do … while` and `for` loops, including `continue`
  and `break` transfers.

### Measured

- The checked-in corpus now contains **651 differential rows**: **634 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.107] — 2026-10-26

### Added

- Added five object-frame witnesses for nested computed local initialization,
  including nested shadowing, assignment, return, and inner-loop `continue`
  and `break` transfers.

### Measured

- The checked-in corpus now contains **646 differential rows**: **629 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.106] — 2026-10-26

### Added

- Added five object-frame witnesses for switch-default and switch-fallthrough
  shadow-computed initialization, conditional and loop return cleanup, and
  switch-case return cleanup.

### Measured

- The checked-in corpus now contains **640 differential rows**: **623 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.105] — 2026-10-26

### Added

- Added five object-frame witnesses for shadow-computed local initialization
  with `switch` and conditional scopes, plus `for`/`while` transfer through
  `continue` and `break`.

### Measured

- The checked-in corpus now contains **629 differential rows**: **612 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.104] — 2026-10-26

### Added

- Added fifteen object-frame witnesses for computed local initialization across
  conditional branches, `switch` defaults, zero- and single-iteration loops,
  loop `continue`/`break`, and shadowed locals in `for`, `while`, and
  `do … while`.

### Measured

- The checked-in corpus now contains **624 differential rows**: **607 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

This is the catch-up release for the three five-construct release points that
followed `v0.1.101`; the metadata records their complete 609→624 batch.

## [0.1.101] — 2026-10-26

### Added

- Added object-frame witnesses for computed local initialization in `for`,
  `switch`, `while`, `do … while`, and conditional blocks.

### Measured

- The checked-in corpus now contains **609 differential rows**: **592 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.100] — 2026-10-26

### Added

- Added object-frame witnesses for `do … while` local initialization with
  `break`, `for`/`while`/`do … while`/`switch` shadowed local initialization,
  and conditional shadowed local initialization.

### Measured

- The checked-in corpus now contains **604 differential rows**: **587 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.99] — 2026-10-26

### Added

- Added object-frame witnesses for `for` local initialization with `continue`
  and `break`, `while` local initialization with `continue` and `break`, and
  `do … while` local initialization with `continue`.

### Measured

- The checked-in corpus now contains **598 differential rows**: **581 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.98] — 2026-10-25

### Added

- Added object-frame witnesses for conditional-`else` local initialization,
  `switch`-default local initialization, zero-iteration `for` local
  initialization, zero-iteration `while` local initialization, and
  single-iteration `do … while` local initialization.

### Measured

- The checked-in corpus now contains **593 differential rows**: **576 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.97] — 2026-10-25

### Added

- Added object-frame witnesses for conditional false-branch local
  initialization, `while`-body local initialization, `for`-body local
  initialization, `do … while`-body local initialization, and `switch`-case
  local initialization.

### Measured

- The checked-in corpus now contains **588 differential rows**: **571 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.96] — 2026-10-25

### Added

- Added object-frame witnesses for nested prefix and postfix decrement, nested
  computed and plain local initialization, and conditional-block local
  initialization.

### Measured

- The checked-in corpus now contains **583 differential rows**: **566 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.95] — 2026-10-25

### Added

- Added object-frame witnesses for nested-block shadowing, assignment,
  compound assignment, prefix increment, and postfix increment of outer locals.

### Measured

- The checked-in corpus now contains **578 differential rows**: **561 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.94] — 2026-10-25

### Added

- Added object-frame witnesses for local prefix and postfix decrement,
  parameter-based initialization, computed initialization, and chained local
  initialization.

### Measured

- The checked-in corpus now contains **573 differential rows**: **556 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.93] — 2026-10-25

### Added

- Added object-frame witnesses for automatic local declaration, prefix and
  postfix increment, direct assignment, and compound assignment.

### Measured

- The checked-in corpus now contains **568 differential rows**: **551 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.92] — 2026-10-25

### Added

- Added object-frame statement witnesses for complete `for` initialization and
  body execution, `for` `continue` and `break`, and `continue` in `do … while`
  and `while` loops.

### Measured

- The checked-in corpus now contains **563 differential rows**: **546 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.91] — 2026-10-25

### Added

- Added object-frame statement witnesses for nested block scope, `void` return,
  conditional without `else`, switch fallthrough, and zero-iteration `while`.

### Measured

- The checked-in corpus now contains **558 differential rows**: **541 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.90] — 2026-10-25

### Added

- Added object-frame statement witnesses for `goto`/labels, null statements,
  explicit returns, `do … while`, and compound assignment.

### Measured

- The checked-in corpus now contains **553 differential rows**: **536 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.89] — 2026-10-25

### Added

- Added object-frame statement witnesses for conditional, `while`, `switch`,
  `for`, and `break`/`continue` control flow.

### Measured

- The checked-in corpus now contains **548 differential rows**: **531 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.88] — 2026-10-25

### Added

- Added object-frame witnesses for Boolean, signed and unsigned integer
  literals, plus null-pointer equality and inequality.

### Measured

- The checked-in corpus now contains **543 differential rows**: **526 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.87] — 2026-10-25

### Added

- Added object-frame witnesses for `alignof`, widening and narrowing integral
  casts, and `noexcept` expressions.

### Measured

- The checked-in corpus now contains **538 differential rows**: **521 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.86] — 2026-10-25

### Added

- Added object-frame witnesses for integral equality and inequality,
  greater-than and greater-equal comparisons, and `sizeof`.

### Measured

- The checked-in corpus now contains **534 differential rows**: **517 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.85] — 2026-10-25

### Added

- Added object-frame witnesses for binary bitwise XOR, left and right shifts,
  and relational less-than and less-equal comparisons.

### Measured

- The checked-in corpus now contains **529 differential rows**: **512 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.84] — 2026-10-25

### Added

- Added object-frame witnesses for binary subtraction, multiplication,
  division, remainder, and bitwise AND.

### Measured

- The checked-in corpus now contains **523 differential rows**: **506 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.83] — 2026-10-25

### Added

- Added object-frame witnesses for unary plus, unary minus, bitwise
  complement, logical negation, and binary addition.

### Measured

- The checked-in corpus now contains **518 differential rows**: **501 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.82] — 2026-10-25

### Added

- Added object-frame witnesses for logical `&&`/`||` short-circuiting,
  conditional selection, comma sequencing, and direct parameter assignment.

### Measured

- The checked-in corpus now contains **513 differential rows**: **496 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.81] — 2026-10-25

### Added

- Added narrow integral compound arithmetic witnesses for unsigned-`short`,
  unsigned-`char`, and signed-`char` addition, subtraction, division, and
  modulo, using defined mid-range values and preserving the existing wrap cases.

### Measured

- The checked-in corpus now contains **508 differential rows**: **491 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.80] — 2026-10-25

### Added

- Added unsigned-`long` compound bitwise AND/OR/XOR and left- and right-shift
  witnesses for defined mid-range values.

### Measured

- The checked-in corpus now contains **501 differential rows**: **484 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.79] — 2026-10-25

### Added

- Added unsigned-`long` compound addition, subtraction, multiplication,
  division, and modulo witnesses for defined mid-range values.

### Measured

- The checked-in corpus now contains **496 differential rows**: **479 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.78] — 2026-10-25

### Added

- Added signed-`long` compound bitwise AND/OR/XOR and left- and right-shift
  witnesses for defined mid-range values.

### Measured

- The checked-in corpus now contains **491 differential rows**: **474 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.77] — 2026-10-25

### Added

- Added signed-`long` compound addition, subtraction, multiplication, division,
  and modulo witnesses for defined mid-range values.

### Measured

- The checked-in corpus now contains **486 differential rows**: **469 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.76] — 2026-10-25

### Added

- Added signed-long-long compound bitwise AND/OR/XOR and left- and right-shift
  witnesses for defined mid-range values.

### Measured

- The checked-in corpus now contains **480 differential rows**: **463 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.75] — 2026-10-25

### Added

- Added signed-long-long compound addition, subtraction, multiplication,
  division, and modulo witnesses for defined mid-range values.

### Measured

- The checked-in corpus now contains **475 differential rows**: **458 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.74] — 2026-10-25

### Added

- Added unsigned-long-long compound modulo, bitwise AND/OR/XOR, and left-shift
  witnesses for defined mid-range values.

### Measured

- The checked-in corpus now contains **470 differential rows**: **453 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.


## [0.1.73] — 2026-10-25

### Added

- Added unsigned-`int` compound shifts and unsigned-long-long compound
  addition, subtraction, multiplication, and division witnesses for defined
  mid-range values.

### Measured

- The checked-in corpus now contains **465 differential rows**: **448 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.


## [0.1.72] — 2026-10-25

### Added

- Added unsigned-`int` compound addition, subtraction, multiplication,
  division, modulo, and bitwise AND/OR/XOR witnesses for defined mid-range
  values.

### Measured

- The checked-in corpus now contains **459 differential rows**: **442 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.


## [0.1.71] — 2026-10-25

### Added

- Added canonical signed-`int` compound addition, subtraction, multiplication,
  division, and modulo witnesses for defined mid-range values.

### Measured

- The checked-in corpus now contains **451 differential rows**: **434 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.


## [0.1.70] — 2026-10-25

### Added

- Added signed and unsigned narrow-type compound shifts, canonical `int`
  compound shifts, and canonical `int` compound bitwise AND/OR/XOR witnesses
  for defined mid-range values.

### Measured

- The checked-in corpus now contains **446 differential rows**: **429 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.69] — 2026-10-25

### Added

- Added signed-char and unsigned-char compound bitwise AND/OR/XOR witnesses
  for defined mid-range values.

### Measured

- The checked-in corpus now contains **433 differential rows**: **416 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.68] — 2026-10-24

### Added

- Added signed-short compound XOR, unsigned-short compound AND/OR/XOR, and
  signed-char compound AND witnesses for defined mid-range values.

### Measured

- The checked-in corpus now contains **428 differential rows**: **411 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.67] — 2026-10-24

### Added

- Added signed-short and unsigned-short compound modulo witnesses, an
  unsigned-char compound modulo witness, and signed-short compound bitwise AND
  and OR witnesses for defined mid-range values.

### Measured

- The checked-in corpus now contains **423 differential rows**: **406 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.66] — 2026-10-24

### Added

- Added narrow signed and unsigned `*=` witnesses plus signed-short `/=`
  compound-assignment coverage for defined mid-range values.

### Measured

- The checked-in corpus now contains **418 differential rows**: **401 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.65] — 2026-10-24

### Added

- Added narrow signed and unsigned compound-assignment witnesses for `+=` and
  `-=`, including defined mid-range results and unsigned wrap boundaries.

### Measured

- The checked-in corpus now contains **413 differential rows**: **396 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.64] — 2026-10-24

### Added

- Added signed-char postfix decrement, unsigned-char postfix decrement,
  unsigned-short mid-range postfix increment, and signed-short mid-range
  prefix increment/decrement witnesses.

### Measured

- The checked-in corpus now contains **406 differential rows**: **389 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.63] — 2026-10-24

### Added

- Added signed-char and unsigned-char callable frame increment/decrement wrap
  and postfix-return witnesses across the 8-bit integral boundary.

### Measured

- The checked-in corpus now contains **400 differential rows**: **383 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.62] — 2026-10-24

### Added

- Added signed-char and unsigned-short callable frame increment/decrement
  wrap and postfix-return witnesses across the narrow integral boundary.

### Measured

- The checked-in corpus now contains **395 differential rows**: **378 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.61] — 2026-10-24

### Added

- Added callable frame fuel-exhaustion and self-initializer lifetime-failure
  witnesses, plus signed-short and unsigned-short frame increment/decrement
  wrap witnesses.

### Measured

- The checked-in corpus now contains **390 differential rows**: **373 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.60] — 2026-10-24

### Added

- Added signed increment/decrement overflow-retention witnesses for prefix and
  postfix forms, with safe native controls documenting the undefined-operation
  boundary.

### Measured

- The checked-in corpus now contains **385 differential rows**: **368 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.59] — 2026-10-24

### Added

- Added frame-level unsigned increment/decrement, discarded postfix storage,
  and compound-assignment wrap witnesses with native `uint32_t` controls.

### Measured

- The checked-in corpus now contains **380 differential rows**: **363 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.58] — 2026-10-24

### Added

- Recorded the unknown binary-operator and increment-precedence refusals.
- Added discarded-postfix storage and combined frame do-while and
  frame for-switch execution witnesses.

### Measured

- The checked-in corpus now contains **375 differential rows**: **358 MATCH**,
  **0 DIVERGE**, **7 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.57] — 2026-10-24

### Added

- Recorded rung-5 by-value callable refusal and rung-3 loud refusals for
  unknown increment, logical, compound-assignment, and unary operators.

### Measured

- The checked-in corpus now contains **370 differential rows**: **355 MATCH**,
  **0 DIVERGE**, **5 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.56] — 2026-10-24

### Added

- Rung-4 loop-body, return-expression, `for`-initializer, and switch-scope
  failure-retention witnesses, plus callable parameter-read coverage.

### Measured

- The checked-in corpus now contains **365 differential rows**: **355 MATCH**,
  **0 DIVERGE**, **0 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.55] — 2026-10-24

### Added

- Rung-4 frame `break`/`continue`, block-scope, return-cleanup, and
  failure-retained-scope witnesses, plus parser admission for automatic local
  declarations.

### Measured

- The checked-in corpus now contains **360 differential rows**: **350 MATCH**,
  **0 DIVERGE**, **0 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.54] — 2026-10-24

### Added

- Rung-1 statement-level temporary-reference, dynamic-local, static-local,
  and thread-local execution witnesses, plus a rung-4 frame-`for` scope
  witness.

### Measured

- The checked-in corpus now contains **355 differential rows**: **345 MATCH**,
  **0 DIVERGE**, **0 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.53] — 2026-10-24

### Added

- Rung-1 reverse-scope cleanup, default-then-assign initialization, fresh
  loop-object lifetimes, nested automatic shadowing, and sequential local
  initialization witnesses.

### Measured

- The checked-in corpus now contains **350 differential rows**: **340 MATCH**,
  **0 DIVERGE**, **0 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.52] — 2026-10-24

### Added

- Rung-5 const and uninitialized-reference binding, rung-1 callable
  static-local and thread-local persistence, and a rung-4 returned-local
  frame-cleanup witness.

### Measured

- The checked-in corpus now contains **345 differential rows**: **335 MATCH**,
  **0 DIVERGE**, **0 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.51] — 2026-10-24

### Added

- Rung-4 loop-local and automatic-local increment witnesses, rung-5
  value-parameter isolation, and a rung-7 integral-record alias/lifetime
  witness.

### Measured

- The checked-in corpus now contains **340 differential rows**: **330 MATCH**,
  **0 DIVERGE**, **0 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.50] — 2026-10-24

### Added

- Rung-7 protected and friend-mediated base access, const repeated-base
  reads, and mutable-member reads through const base subobjects.

### Measured

- The checked-in corpus now contains **334 differential rows**: **324 MATCH**,
  **0 DIVERGE**, **0 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.49] — 2026-10-24

### Added

- Rung-7 unsigned-char getter conversion, derived-to-base static casts,
  repeated nonvirtual base subobject selection, and private base access
  witnesses.

### Measured

- The checked-in corpus now contains **330 differential rows**: **320 MATCH**,
  **0 DIVERGE**, **0 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.48] — 2026-10-24

### Added

- Rung-7 enum getter, canonical out-of-line getter, lvalue-cast getter, and
  string-handle getter coverage, with source-faithful arrow receiver witnesses.

### Measured

- The checked-in corpus now contains **325 differential rows**: **315 MATCH**,
  **0 DIVERGE**, **0 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.47] — 2026-10-24

### Added

- Rung-7 enum member setter coverage, extending the arrow, dot,
  derived-to-base, and explicit-cast member getter receiver paths.

### Measured

- The checked-in corpus now contains **321 differential rows**: **311 MATCH**,
  **0 DIVERGE**, **0 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.46] — 2026-10-24

### Added

- Rung-7 member getter call coverage for arrow, dot, derived-to-base, and
  explicit-cast receiver paths, with native Clang witnesses for each form.

### Measured

- The checked-in corpus now contains **320 differential rows**: **310 MATCH**,
  **0 DIVERGE**, **0 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.45] — 2026-10-24

### Added

- Callable integral addition and subtraction, unary minus, and plain-`int`
  prefix and postfix decrement coverage for the bounded expression evaluator.

### Measured

- The checked-in corpus now contains **316 differential rows**: **306 MATCH**,
  **0 DIVERGE**, **0 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.44] — 2026-10-24

### Added

- Callable integral `<=`, `==`, `!=`, `>` and `>=` comparison coverage for the
  bounded expression evaluator.

### Measured

- The checked-in corpus now contains **311 differential rows**: **301 MATCH**,
  **0 DIVERGE**, **0 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.43] — 2026-10-24

### Added

- Callable division, remainder, left/right shifts, and less-than coverage for
  the bounded integral expression evaluator.

### Measured

- The checked-in corpus now contains **306 differential rows**: **296 MATCH**,
  **0 DIVERGE**, **0 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.42] — 2026-10-24

### Added

- Callable unary plus and bitwise AND, OR, XOR, and multiplication coverage
  over the bounded integral expression evaluator.

### Measured

- The checked-in corpus now contains **301 differential rows**: **291 MATCH**,
  **0 DIVERGE**, **0 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.41] — 2026-10-24

### Added

- Callable boolean, character, constant, unsigned-integer and null-pointer
  comparison coverage, plus integral unary complement and logical negation.
- Bounded callable `CXXNoexceptExpr` parsing and evaluation for side-effect-free
  builtin-integral operands, with exact boolean evidence and loud boundaries.

### Measured

- The checked-in corpus now contains **296 differential rows**: **286 MATCH**,
  **0 DIVERGE**, **0 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.40] — 2026-10-24

### Added

- Bounded callable `sizeof` and `alignof` for builtin integral operands on the
  LP64 profile, with pure and object-backed evaluation and loud type/trait
  boundaries.
- Typed integral `CStyleCastExpr` admission, including narrowing conversions
  and a `NoOp` type-preservation check.
- Selected direct-call parsing through explicit declaration-handle target
  tables, plus callable argument conversion coverage.

### Measured

- The checked-in corpus now contains **286 differential rows**: **276 MATCH**,
  **0 DIVERGE**, **0 REFUSE**, **0 TIMEOUT**, and **10 ORACLE**; the grammar
  census remains **24 witnesses** with **0 MATCH / 0 DIVERGE / 24 REFUSE**.
  Pinned Clang/LLVM 21.1.8 supplies the native witness results; the ten
  explicit ORACLE rows are the unavailable TinyXML-2 source-call inputs.

## [0.1.39] — 2026-10-23

### Added

- Rung-4 metadata gates for `OMPSimdDirective`, `OMPCriticalDirective`,
  `OMPMetaDirective`, `OMPTileDirective` and `OMPStripeDirective`, each
  checked at an exact retained AST path while SIMD, synchronization,
  metadirective selection and loop transformations remain bounded.

### Measured

- The checked-in corpus now contains 215 differential rows and 24 grammar
  witnesses. With pinned Clang/LLVM 21.1.8 unavailable, the run reports 0
  MATCH, 0 DIVERGE, 0 REFUSE, 0 TIMEOUT, and 215 ORACLE rows; grammar reports
  24 ORACLE rows.

## [0.1.38] — 2026-10-23

### Added

- Rung-4 metadata gates for `OMPTaskgroupDirective`,
  `OMPMasterTaskloopDirective`, `OMPMasterTaskloopSimdDirective`,
  `OMPParallelMasterTaskloopDirective` and
  `OMPParallelMasterTaskloopSimdDirective`, each checked at an exact retained
  AST path while task synchronization and execution remain bounded.

### Measured

- The checked-in corpus now contains 210 differential rows and 24 grammar
  witnesses. With pinned Clang/LLVM 21.1.8 unavailable, the run reports 0
  MATCH, 0 DIVERGE, 0 REFUSE, 0 TIMEOUT, and 210 ORACLE rows; grammar reports
  24 ORACLE rows.

## [0.1.37] — 2026-10-23

### Added

- Rung-4 metadata gates for `OMPTargetDirective`, `OMPTargetDataDirective`,
  `OMPTargetEnterDataDirective`, `OMPTargetExitDataDirective` and
  `OMPTargetUpdateDirective`, each checked at an exact retained AST path while
  target offload, mapping and execution remain bounded.

### Measured

- The checked-in corpus now contains 205 differential rows and 24 grammar
  witnesses. With pinned Clang/LLVM 21.1.8 unavailable, the run reports 0
  MATCH, 0 DIVERGE, 0 REFUSE, 0 TIMEOUT, and 205 ORACLE rows; grammar reports
  24 ORACLE rows.

## [0.1.36] — 2026-10-23

### Added

- Rung-4 metadata gates for `OMPSectionDirective`,
  `OMPDistributeParallelForSimdDirective`, `OMPDistributeSimdDirective`,
  `OMPForSimdDirective` and `OMPParallelForSimdDirective`, each checked at an
  exact retained AST path while OpenMP SIMD scheduling and execution remain
  bounded.

### Measured

- The checked-in corpus now contains 195 differential rows and 24 grammar
  witnesses. With pinned Clang/LLVM 21.1.8 unavailable, the run reports 0
  MATCH, 0 DIVERGE, 0 REFUSE, 0 TIMEOUT, and 195 ORACLE rows; grammar reports
  24 ORACLE rows.

## [0.1.35] — 2026-10-23

### Added

- Rung-4 metadata gates for `OMPParallelSectionsDirective`,
  `OMPParallelMasterDirective`, `OMPOrderedDirective`, `OMPAtomicDirective`,
  `OMPFlushDirective`, `OMPBarrierDirective`, `OMPTaskwaitDirective` and
  `OMPTaskyieldDirective`, each checked at an exact retained AST path while
  OpenMP scheduling, synchronization and execution remain bounded.

### Measured

- The checked-in corpus now contains 190 differential rows and 24 grammar
  witnesses. With pinned Clang/LLVM 21.1.8 unavailable, the run reports 0
  MATCH, 0 DIVERGE, 0 REFUSE, 0 TIMEOUT, and 190 ORACLE rows; grammar reports
  24 ORACLE rows.

## [0.1.34] — 2026-10-23

### Added

- Rung-4 metadata gates for `OMPTaskloopDirective`, `OMPTeamsDirective`,
  `OMPDistributeDirective`, `OMPDistributeParallelForDirective` and
  `OMPParallelForDirective`, each checked at an exact retained AST path while
  OpenMP scheduling and execution remain bounded.

### Measured

- The checked-in corpus now contains 182 differential rows and 24 grammar
  witnesses. With pinned Clang/LLVM 21.1.8 unavailable, the run reports 0
  MATCH, 0 DIVERGE, 0 REFUSE, 0 TIMEOUT, and 182 ORACLE rows; grammar reports
  24 ORACLE rows.

## [0.1.33] — 2026-10-23

### Added

- Rung-4 metadata gates for `OMPForDirective`, `OMPSectionsDirective`,
  `OMPSingleDirective`, `OMPMasterDirective` and `OMPTaskDirective`, each
  checked at an exact retained AST path while OpenMP scheduling and execution
  remain bounded.

### Measured

- The checked-in corpus now contains 177 differential rows and 24 grammar
  witnesses. With pinned Clang/LLVM 21.1.8 unavailable, the run reports 0
  MATCH, 0 DIVERGE, 0 REFUSE, 0 TIMEOUT, and 177 ORACLE rows; grammar reports
  24 ORACLE rows.

## [0.1.32] — 2026-10-23

### Added

- Rung-1 metadata for `DesignatedInitExpr`; rung-4 statement gates for
  `CoreturnStmt`, `IndirectGotoStmt`, `CapturedStmt` and
  `OMPParallelDirective`; each is checked at an exact retained AST path while
  initialization, coroutine, computed-goto, capture and OpenMP execution remain
  bounded.

### Measured

- The checked-in corpus now contains 172 differential rows and 24 grammar
  witnesses. With pinned Clang/LLVM 21.1.8 unavailable, the run reports 0
  MATCH, 0 DIVERGE, 0 REFUSE, 0 TIMEOUT, and 172 ORACLE rows; grammar reports
  24 ORACLE rows.

## [0.1.31] — 2026-10-23

### Added

- Rung-3 metadata gates for `CXXUnresolvedMemberExpr`,
  `CXXDependentScopeDeclRefExpr`, `CXXInheritedCtorInitExpr` and
  `CXXStdInitializerListExpr`, plus the rung-4 `CoroutineBodyStmt` gate;
  dependent lookup, inherited construction, initializer-list behavior and
  coroutine execution remain bounded.

### Measured

- The checked-in corpus now contains 166 differential rows and 24 grammar
  witnesses. With pinned Clang/LLVM 21.1.8 unavailable, the run reports 0
  MATCH, 0 DIVERGE, 0 REFUSE, 0 TIMEOUT, and 166 ORACLE rows; grammar reports
  24 ORACLE rows.

## [0.1.30] — 2026-10-23

### Added

- Rung-3 metadata gates for `CXXDefaultArgExpr`,
  `CXXUnresolvedConstructExpr`, `UnresolvedLookupExpr` and
  `CXXPseudoDestructorExpr`, each checked at an exact retained AST path;
  default argument substitution, dependent construction and lookup, and
  pseudo-destructor semantics remain bounded.

### Measured

- The checked-in corpus now contains 161 differential rows and 24 grammar
  witnesses. With pinned Clang/LLVM 21.1.8 unavailable, the run reports 0
  MATCH, 0 DIVERGE, 0 REFUSE, 0 TIMEOUT, and 161 ORACLE rows; grammar reports
  24 ORACLE rows.

## [0.1.29] — 2026-10-23

### Added

- Rung-3 metadata gates for `CXXCoawaitExpr`, `CStyleCastExpr`,
  `UnaryExprOrTypeTraitExpr`, `VAArgExpr` and
  `CXXDependentScopeMemberExpr`, each checked at an exact retained AST path;
  coroutine, cast, type-trait, variadic and dependent member execution remains
  bounded.

### Measured

- The checked-in corpus now contains 157 differential rows and 24 grammar
  witnesses. With pinned Clang/LLVM 21.1.8 unavailable, the run reports 0
  MATCH, 0 DIVERGE, 0 REFUSE, 0 TIMEOUT, and 157 ORACLE rows; grammar reports
  24 ORACLE rows.

## [0.1.28] — 2026-10-23

### Added

- Rung-3 metadata gates for `CXXRewrittenBinaryOperator`, `CXXNoexceptExpr`,
  `CXXTypeidExpr` and `CXXFoldExpr`, each checked at an exact retained AST
  path; expression execution remains bounded.

### Measured

- The checked-in corpus now contains 152 differential rows and 24 grammar
  witnesses. With pinned Clang/LLVM 21.1.8 unavailable, the run reports 0
  MATCH, 0 DIVERGE, 0 REFUSE, 0 TIMEOUT, and 152 ORACLE rows; grammar reports
  24 ORACLE rows.

## [0.1.27] — 2026-10-23

### Added

- Rung-8 metadata gate for `CXXOperatorCallExpr`, checked at an exact
  retained AST path; overload and conversion execution remain loud.

### Measured

- The checked-in corpus now contains 147 differential rows and 24 grammar
  witnesses. With pinned Clang/LLVM 21.1.8 unavailable, the run reports 0
  MATCH, 0 DIVERGE, 0 REFUSE, 0 TIMEOUT, and 147 ORACLE rows; grammar reports
  24 ORACLE rows.

## [0.1.26] — 2026-10-23

### Added

- Rung-7 metadata gates for `CXXConstructExpr`, `CXXBaseSpecifier`,
  `MemberExpr` and `CXXMemberCallExpr`, all checked at exact retained AST
  paths.

### Measured

- The checked-in corpus now contains 146 differential rows and 24 grammar
  witnesses. With pinned Clang/LLVM 21.1.8 unavailable, the run reports 0
  MATCH, 0 DIVERGE, 0 REFUSE, 0 TIMEOUT, and 146 ORACLE rows; grammar reports
  24 ORACLE rows.

## [0.1.25] — 2026-10-23

### Added

- Rung-4 metadata gates for `GotoStmt` and `LabelStmt`, a range-loop gate for
  `CXXForRangeStmt`, and rung-10 exception metadata gates for `CXXTryStmt` and
  `CXXCatchStmt`, all checked at exact retained AST paths.

### Measured

- The checked-in corpus now contains 141 differential rows and 24 grammar
  witnesses. With pinned Clang/LLVM 21.1.8 unavailable, the run reports 0
  MATCH, 0 DIVERGE, 0 REFUSE, 0 TIMEOUT, and 141 ORACLE rows; grammar reports
  24 ORACLE rows.

## [0.1.24] — 2026-10-23

### Added

- Rung-4 metadata gates for `DeclStmt`, `BreakStmt`, `ContinueStmt`,
  `NullStmt`, `CaseStmt`, `DefaultStmt` and `DoStmt`, all checked at exact
  retained AST paths.

### Measured

- The checked-in corpus now contains 136 differential rows and 24 grammar
  witnesses. With pinned Clang/LLVM 21.1.8 unavailable, the run reports 0
  MATCH, 0 DIVERGE, 0 REFUSE, 0 TIMEOUT, and 136 ORACLE rows; grammar reports
  24 ORACLE rows.

## [0.1.23] — 2026-10-23

### Added

- Rung-4 metadata gates for `ReturnStmt`, `IfStmt`, `WhileStmt`, `ForStmt`
  and `SwitchStmt`, all checked at exact retained AST paths.

### Measured

- The checked-in corpus now contains 129 differential rows and 24 grammar
  witnesses. With pinned Clang/LLVM 21.1.8 unavailable, the run reports 0
  MATCH, 0 DIVERGE, 0 REFUSE, 0 TIMEOUT, and 129 ORACLE rows; grammar reports
  24 ORACLE rows.

## [0.1.22] — 2026-10-23

### Added

- Rung-3 metadata gates for `CallExpr`, `CompoundAssignOperator`, `LambdaExpr`
  and `ArraySubscriptExpr`, plus the rung-4 `CompoundStmt` gate, all checked
  at exact retained AST paths.

### Measured

- The checked-in corpus now contains 124 differential rows and 24 grammar
  witnesses. With pinned Clang/LLVM 21.1.8 unavailable, the run reports 0
  MATCH, 0 DIVERGE, 0 REFUSE, 0 TIMEOUT, and 124 ORACLE rows; grammar reports
  24 ORACLE rows.

## [0.1.21] — 2026-10-23

### Added

- Rung-2 metadata for `IntegerLiteral` and rung-3 metadata for `DeclRefExpr`,
  `CXXThisExpr`, `UnaryOperator`, `BinaryOperator` and `ConditionalOperator`,
  all checked at exact retained AST paths.

### Measured

- The checked-in corpus now contains 119 differential rows and 24 grammar
  witnesses. With pinned Clang/LLVM 21.1.8 unavailable, the run reports 0
  MATCH, 0 DIVERGE, 0 REFUSE, 0 TIMEOUT, and 119 ORACLE rows; grammar reports
  24 ORACLE rows.

## [0.1.20] — 2026-10-23

### Added

- Rung-2 metadata gates for `CXXBoolLiteralExpr`,
  `CXXNullPtrLiteralExpr`, `CharacterLiteral` and `FloatingLiteral`, all
  checked at exact retained AST paths.

### Measured

- The checked-in corpus now contains 112 differential rows and 24 grammar
  witnesses. With pinned Clang/LLVM 21.1.8 unavailable, the run reports 0
  MATCH, 0 DIVERGE, 0 REFUSE, 0 TIMEOUT, and 112 ORACLE rows; grammar reports
  24 ORACLE rows.

## [0.1.19] — 2026-10-23

### Added

- Rung-2 metadata gates for `ConstantExpr`, `CXXStaticCastExpr`,
  `CXXConstCastExpr` and `CXXReinterpretCastExpr`, plus the rung-7
  `CXXDynamicCastExpr` gate, all checked at exact retained AST paths.

### Measured

- The checked-in corpus now contains 108 differential rows and 24 grammar
  witnesses. With pinned Clang/LLVM 21.1.8 unavailable, the run reports 0
  MATCH, 0 DIVERGE, 0 REFUSE, 0 TIMEOUT, and 108 ORACLE rows; grammar reports
  24 ORACLE rows.

## [0.1.18] — 2026-10-23

### Added

- Rung-1 metadata gates for `InitListExpr`, `CXXParenListInitExpr`,
  `ImplicitValueInitExpr`, `ImplicitCastExpr` and `ParenExpr`, all checked at
  exact retained AST paths.

### Measured

- The checked-in corpus now contains 103 differential rows and 24 grammar
  witnesses. With pinned Clang/LLVM 21.1.8 unavailable, the run reports 0
  MATCH, 0 DIVERGE, 0 REFUSE, 0 TIMEOUT, and 103 ORACLE rows; grammar reports
  24 ORACLE rows.

## [0.1.17] — 2026-10-23

### Added

- Rung-1 metadata gates for `CXXTemporaryObjectExpr`, `CXXNewExpr`,
  `CXXDeleteExpr`, `CXXDefaultInitExpr` and `CXXScalarValueInitExpr`, all
  checked at exact retained AST paths.

### Measured

- The checked-in corpus now contains 98 differential rows and 24 grammar
  witnesses. With pinned Clang/LLVM 21.1.8 unavailable, the run reports 0
  MATCH, 0 DIVERGE, 0 REFUSE, 0 TIMEOUT, and 98 ORACLE rows; grammar reports
  24 ORACLE rows.

## [0.1.16] — 2026-10-23

### Added

- Rung-0 and rung-1 metadata gates for `UsingEnumDecl`,
  `LifetimeExtendedTemporaryDecl`, `MaterializeTemporaryExpr`,
  `CXXBindTemporaryExpr` and `ExprWithCleanups`, all checked at exact
  retained AST paths.

### Measured

- The checked-in corpus now contains 93 differential rows and 24 grammar
  witnesses. With pinned Clang/LLVM 21.1.8 unavailable, the run reports 0
  MATCH, 0 DIVERGE, 0 REFUSE, 0 TIMEOUT, and 93 ORACLE rows; grammar reports
  24 ORACLE rows.

## [0.1.15] — 2026-10-23

### Added

- Rung-3 metadata gates for `RequiresExpr`, `TypeRequirement`,
  `SimpleRequirement`, `CompoundRequirement` and `NestedRequirement`, all
  checked at exact retained AST paths.

### Measured

- The checked-in corpus now contains 88 differential rows and 24 grammar
  witnesses. With pinned Clang/LLVM 21.1.8 unavailable, the run reports 0
  MATCH, 0 DIVERGE, 0 REFUSE, 0 TIMEOUT, and 88 ORACLE rows; grammar reports
  24 ORACLE rows.

## [0.1.14] — 2026-10-22

### Added

- Rung-0 metadata gates for `IndirectFieldDecl`,
  `ClassScopeFunctionSpecializationDecl`, `FriendTemplateDecl`,
  `TemplateParamObjectDecl` and `ImplicitConceptSpecializationDecl`, all
  checked at exact retained AST paths.

### Measured

- The checked-in corpus now contains 83 differential rows and 24 grammar
  witnesses. With pinned Clang/LLVM 21.1.8 unavailable, the run reports 0
  MATCH, 0 DIVERGE, 0 REFUSE, 0 TIMEOUT, and 83 ORACLE rows; grammar reports
  24 ORACLE rows.

## [0.1.13] — 2026-10-22

### Added

- Rung-0 metadata gates for `ConstructorUsingShadowDecl`, `UsingPackDecl`,
  `UnresolvedUsingTypenameDecl`, `UnresolvedUsingValueDecl`, `BindingDecl` and
  `DecompositionDecl`, all checked at exact retained AST paths.

### Measured

- The checked-in corpus now contains 78 differential rows and 24 grammar
  witnesses. With pinned Clang/LLVM 21.1.8 unavailable, the run reports 0
  MATCH, 0 DIVERGE, 0 REFUSE, 0 TIMEOUT, and 78 ORACLE rows; grammar reports
  24 ORACLE rows.

## [0.1.12] — 2026-10-22

### Added

- Rung-0 metadata gates for `ClassTemplatePartialSpecializationDecl`,
  `VarTemplatePartialSpecializationDecl`, `ConceptDecl`,
  `CXXDeductionGuideDecl` and `UsingShadowDecl`, all checked at exact retained
  AST paths.

### Measured

- The checked-in corpus now contains 72 differential rows and 24 grammar
  witnesses. With pinned Clang/LLVM 21.1.8 unavailable, the run reports 0
  MATCH, 0 DIVERGE, 0 REFUSE, 0 TIMEOUT, and 72 ORACLE rows; grammar reports
  24 ORACLE rows.

## [0.1.11] — 2026-10-22

### Added

- Rung-0 metadata gates for `FunctionTemplateDecl`, `VarTemplateDecl`,
  `TypeAliasTemplateDecl`, `ClassTemplateSpecializationDecl` and
  `VarTemplateSpecializationDecl`, all checked at exact retained AST paths.

### Measured

- The checked-in corpus now contains 67 differential rows and 24 grammar
  witnesses. With pinned Clang/LLVM 21.1.8 unavailable, the run reports 0
  MATCH, 0 DIVERGE, 0 REFUSE, 0 TIMEOUT, and 67 ORACLE rows; grammar reports
  24 ORACLE rows.

## [0.1.10] — 2026-10-23

### Added

- Rung-0 metadata gates for `FriendDecl`, `TemplateTypeParmDecl`,
  `NonTypeTemplateParmDecl`, `TemplateTemplateParmDecl` and
  `ClassTemplateDecl`, all checked at exact retained AST paths.

### Measured

- The checked-in corpus now contains 62 differential rows and 24 grammar
  witnesses. With pinned Clang/LLVM 21.1.8 unavailable, the run reports 0
  MATCH, 0 DIVERGE, 0 REFUSE, 0 TIMEOUT, and 62 ORACLE rows; grammar reports
  24 ORACLE rows.

## [0.1.9] — 2026-10-22

### Added

- Rung-0 metadata gates for `CXXMethodDecl`, `EnumConstantDecl`,
  `AccessSpecDecl`, `CXXConstructorDecl`, `CXXDestructorDecl` and
  `CXXConversionDecl`, all checked at exact retained AST paths.

### Measured

- The checked-in corpus now contains 57 differential rows and 24 grammar
  witnesses. With pinned Clang/LLVM 21.1.8 unavailable, the run reports 0
  MATCH, 0 DIVERGE, 0 REFUSE, 0 TIMEOUT, and 57 ORACLE rows; grammar reports
  24 ORACLE rows.

## [0.1.8] — 2026-10-22

### Added

- Rung-0 metadata gates for `LinkageSpecDecl`, `StaticAssertDecl`,
  `ParmVarDecl`, `CXXRecordDecl` and `FieldDecl`, all checked at exact
  retained AST paths.

### Measured

- The checked-in corpus now contains 51 differential rows and 24 grammar
  witnesses. With pinned Clang/LLVM 21.1.8 unavailable, the run reports 0
  MATCH, 0 DIVERGE, 0 REFUSE, 0 TIMEOUT, and 51 ORACLE rows; grammar reports
  24 ORACLE rows.

## [0.1.7] — 2026-10-22

### Added

- Rung-0 metadata gates for `TypedefDecl`, `TypeAliasDecl`,
  `NamespaceAliasDecl`, `UsingDirectiveDecl` and `UsingDecl`, all checked at
  exact retained AST paths.

### Measured

- The checked-in corpus now contains 46 differential rows and 24 grammar
  witnesses. With pinned Clang/LLVM 21.1.8 unavailable, the run reports 0
  MATCH, 0 DIVERGE, 0 REFUSE, 0 TIMEOUT, and 46 ORACLE rows; grammar reports
  24 ORACLE rows.

## [0.1.6] — 2026-10-22

### Added

- Rung-0 metadata gates for namespace, function, variable and enum
  declaration occurrences, each checked at an exact retained AST path.
- A rung-5 callable local-reference witness covering mutable and const aliases.

### Measured

- The checked-in corpus now contains 41 differential rows and 24 grammar
  witnesses. With pinned Clang/LLVM 21.1.8 unavailable, the run reports 0
  MATCH, 0 DIVERGE, 0 REFUSE, 0 TIMEOUT, and 41 ORACLE rows; grammar reports
  24 ORACLE rows.

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
