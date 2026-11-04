# Connected child ports — repricing boundary

The static hierarchy rung in `sv-0.1` flattens concrete **portless** module
instances. A child with a declared port remains an explicit
`Hierarchy:ports` refusal, including when a particular instance leaves that
port unconnected. Top-level ports keep their existing envelope representation;
this boundary is about ports on a module instance that would otherwise be
flattened.

## Why ports remain a boundary

A connected input is an assignment-like conversion into the child's port
type. A connected output publishes the child's value back to the parent, and
an `inout` port requires bidirectional net aliasing and resolution. These are
continuous relationships, not one-time elaboration copies: a later blocking
or nonblocking write in either scope must be visible through the connection
with the scheduler's update-region rules. The existing flattened declaration
store has neither a port alias graph nor a continuous-driver representation.

Unconnected ports do not provide a harmless shortcut. An unconnected input can
receive `z` or a declared default, an omitted named or positional connection
has its own rules, and an unconnected output can still be read through a
hierarchical reference. Empty and mixed connections therefore need the same
elaborated port mapping and value-state rules as ordinary connections. Ignoring
the port or treating a connection as a one-time assignment would fabricate
values and scheduling behavior.

The current admission is consequently narrow and explicit:

* concrete static portless child modules may use the [static hierarchy
  rung](sv-module-hierarchy.md), including parameter overrides, generated
  scopes and static instance arrays;
* child module ports, whether connected, partly omitted, or entirely
  unconnected, remain `Hierarchy:ports`;
* interface and program instances, differing timescales, invalid arrays,
  expansion overflow and frontend-invalid designs retain their independent
  hierarchy boundaries; and
* no second scheduler or implicit net/driver store is introduced to admit a
  connected-port case.

## 2026-10-21 census and decision

The fresh 22,043-path corpus census records `Hierarchy:ports` in **2,397**
files: **1,186** are port-only refusals and **1,211** co-occur with another
wall. The repricer walks the frontend's concrete child instances in the
port-only files, so an instance array contributes each elaborated element.
It finds **1,481** port-bearing child instances with **3,593** declared ports:

| connection shape | instances | files |
|---|---:|---:|
| every declared port connected | 1,423 | 1,137 |
| at least one empty/omitted connection | 43 | 41 |
| every connection empty or omitted | 15 | 10 |

The file column overlaps when one source contains instances with different
connection shapes.

The connected rows are mostly ordinary `NamedValue` inputs paired with
output assignment connections, but the same set also contains conversions,
constant and range/element selections, concatenations, hierarchical values,
and `inout` ports. Those shapes need width/sign conversion and continuous
propagation even when their source text looks like a simple scalar link. The
15 wholly unconnected instances include input-default and `z` cases as well as
unconnected outputs; they are not a single semantics-free family.

No independently admissible connected-port subfamily is exposed by this
measurement. The portless boundary remains the honest rung until the surface
has a port map, conversion and alias/driver representation that calls the
existing scheduler rules. Reproduce the table with:

```text
python3.9 extractors/sv/hierarchy_reprice.py \
  --corpus /path/to/sv-tests-2/tests
```

The instrument reads each source in process and writes no envelope beside the
corpus. Its connection-shape counts are telemetry, not a new runtime model.
