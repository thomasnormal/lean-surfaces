# Package integral singleton storage

IEEE 1800-2023 clauses 6, 10 and 26 give each package variable one static
store. Importing or reexporting a variable binds its original declaration;
it does not copy its value. The legacy extractor now compiles source-defined
packages containing scalar or packed integral storage into the existing
vector state. References and assignment targets use the bound frontend
symbol, including qualified names, explicit/wildcard imports and reexports.
Local shadowing and equal member names in different packages retain distinct
bindings. Escaped identifiers are not parsed as hierarchical paths.

Each slot has an injective internal name incorporating the package name's
length, the package name and the member name. The `Var` retains
`package_storage`, `source_package` and `source_name` provenance. Generated
slots are audited for collisions with source declarations, ports and locals.
The single-module runner allocates package storage once, before module
initializers and processes. It never creates separate package copies for
multiple modules; that shape remains loud.

Default initialization uses the existing four-state unknown and two-state
zero rules. Closed pure integral initializers use the existing expression
semantics and two-state conversion. They may refer to integral parameters
and enumeration values, whose exact elaborated values become literals.
Runtime-variable reads and calls in package initializers remain loud: their
initialization dependency/order and effects are not silently chosen. The
closed fragment makes ordering among admitted package initializers immaterial.
Integral aliases retain the existing type admission.

Every unsupported package member is retained as a design-level refusal.
Unpacked/nonintegral storage, nets, subroutines, DPI declarations, classes,
programs and unsupported types are not erased. Imports from external or
standard packages keep their boundary. Frontend errors in a source containing
a package prevent execution. Redefinition diagnostics also block execution
when the frontend labels an illegal import conflict as a warning. An
independent export-filter audit rejects explicit imports of unexported names
and wildcard imports exposing hidden relay bindings. Unreferenced wildcard
candidates remain candidates, and exporting a specific candidate acts as its
reference; transparent enum members retain their original identities. The symbolic extractor retains its separate
package surface. No evaluator, storage primitive or scheduler is added;
blocking writes, selected stores, retained continuations and captured NBA
updates use their existing rules.

Four authored sources exercise shared qualified/imported/reexported storage,
shadowing, distinct packages, initialization before module declarations,
constants/enums/aliases, defaults, two-state conversion, packed fields and
vector slices, timers and NBA visibility. Complete independent transcripts
agree under both region oracles. Three further sources preserve dependent
initialization, unpacked storage and subroutine boundaries. Four kernel
proofs certify real parsed read/write subtrees and establish current shared
reads, immediate blocking stores, NBA capture and visibility after commit.

The paired 22,035-path extraction census gains 165 clean files without losses:
3,501 to 3,666 clean, 18,468 to 18,303 partial, 66 include skips and zero
errors. Extraction admission is distinct from runtime agreement.

All 165 gains match complete independent transcripts under both region oracles.
Sixteen further initially admitted invalid sources were independently rejected;
generic conflict and export-visibility checks now keep them partial, and they
are not execution matches.
