# Procedural continuous assignments and force/release — repricing boundary

IEEE §§4.9.2, 10.6.1 and 10.6.2 give procedural `assign`/`deassign` and
`force`/`release` their own driver semantics. A procedural continuous
assignment installs a driver on a variable, reevaluates its RHS when source
elements change, and suppresses ordinary procedural writes while active.
`deassign` removes that driver while retaining the current variable value.
`force` takes priority over the resolved net or variable value; `release`
returns a net to its resolved drivers and a variable to the standard
procedural behavior. A later procedural `assign` replaces an active one.

## Why these statements remain a boundary

The envelope has ordinary blocking/nonblocking assignments, but it has no
procedural-driver identity, source sensitivity set, net-resolution input,
force priority, or release restoration state. Rewriting `assign` as a blocking
write loses subsequent RHS reevaluation and the suppression of later writes;
rewriting `force` as a write loses the priority and release transition.
Concatenation and part-select targets also need the same retained driver state.
The public tier therefore keeps `ProceduralAssignStatement` and its paired
`ProceduralDeassignStatement` loud. No driver table, recovery lowering or
second scheduler is introduced.

## 2026-10-22 census and decision

The fresh 22,043-path census records `ProceduralAssignStatement` in **112**
files: **23** are procedural-assign-only and **89** co-occur with another
wall. Repricing the sole files finds **27** spans: **16** `assign` forms and
**11** `force` forms; **13** have a nonliteral RHS, **6** carry an explicit
RHS-reevaluation or source-sensitivity scenario, **7** exercise force/assign
priority, **6** replace an active assignment, **3** are mixed-assignment
diagnostics, **3** target nets, **24** target variables, **1** has a
concatenation LHS, **1** a part-select LHS, **1** is inside an event-triggered
process and **2** are direct chapter-37 statement forms (features overlap).
The co-occurring files retain the paired deassign/release marker as well;
neither marker is reduced to a plain assignment.

Reproduce the table with:

```text
python3.9 extractors/sv/procedural_assign_reprice.py \
  --corpus /path/to/sv-tests-2/tests
```

The instrument is read-only: it classifies source spans without installing a
driver, selecting a resolution value, or advancing the scheduler.
