# Program and interface hierarchy — repricing boundary

The static hierarchy rung admits concrete module instances only. A
non-module instance is reported as `Hierarchy:module-kind`, whether the
instance is a `program` or an `interface`, and whether it has ports. A
non-module top-level root uses the same boundary through module conversion.
This keeps the public surface explicit about the missing semantic contract;
it does not classify a program or interface as an ordinary module by name.

## Why the module executor is insufficient

Programs are testbench processes. Their initial and final procedures use the
reactive region and program completion rules, and `$exit` and implicit
program-drain termination observe that lifetime. Program signals and their
clocking blocks also have different race-avoidance and sampling obligations.
Flattening a portless program into a module would silently move its work into
the design regions.

Interfaces are design scopes with interface ports, modports, clocking blocks,
and signal storage shared by their users. A plain-looking interface instance
can still expose a modport or clocking view, and a connected interface needs
its own binding and propagation rules. Treating it as a module scope would
lose those views or fabricate ordinary module ports.

The current admission is therefore:

* concrete static **portless module** instances use the existing
  [module-hierarchy rung](sv-module-hierarchy.md);
* `program` and `interface` instances, at the top level or nested below a
  module, remain `Hierarchy:module-kind`;
* their ports, clocking/modport declarations, reactive/design-signal state,
  final/exit behavior, and implicit completion are not erased into module
  storage; and
* no second scheduler or guessed region mapping is introduced to make one
  program/interface shape appear module-like.

## 2026-10-21 census and decision

The fresh 22,043-path census records `Hierarchy:module-kind` in **1,248**
files: **319** are module-kind-only and **929** co-occur with another wall.
The repricer walks the frontend's concrete non-module instances in the
319-only files, including top-level non-module roots:

| definition kind | instances | files |
|---|---:|---:|
| `program` | 330 | 298 |
| `interface` | 35 | 33 |

The instance positions are 57 top-level programs (56 files), 273 nested
programs (246 files), and 35 nested interfaces (33 files). The file columns
overlap when a source has more than one instance. Of the 365 instances, 279
are portless and 86 have ports; portlessness therefore does not isolate a
module-like family. Port connection expressions include `NamedValue` (79),
`Assignment` (45), `ArbitrarySymbol` (7), conversions (4), hierarchical
values (4), one range select, and two empty connections. These are only the
front-end shapes; their runtime region and lifetime effects remain the
boundary.

No independently admissible program or interface subfamily is exposed by
this measurement. The current module-only hierarchy rule remains loud until
the surface supplies program/reactive completion and interface/modport/
clocking representations that invoke the existing scheduler rules. Reproduce
the table with:

```text
python3.9 extractors/sv/hierarchy_kind_reprice.py \
  --corpus /path/to/sv-tests-2/tests
```

The instrument reads each source in process and writes no envelope beside the
corpus. Its instance-shape counts are telemetry, not a new runtime model.
