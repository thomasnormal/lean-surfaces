# Module support and envelope loaders

The SystemVerilog tier has two deliberately separate consumers. They are
compatibility layers for different envelope contracts, not duplicate
elaborators that should be collapsed by deleting one of them.

## Current loaders

`LeanModels/Sv/Json.lean` parses schema `sv-0.1` into the legacy `Design`
value used by the self-check and timed process paths. It is a single-file,
single-top-module contract. Module instances and declarations outside its
vocabulary stay as named `Unsupported` nodes. The timed loader in
`LeanModels/Sv/Load.lean` consumes this retained process representation and
uses the shared scheduler, while the legacy self-check path remains
initial-only.

`LeanModels/Sv/Ingest2.lean` parses schema `sv-0.2` from symbolic extraction
(`extract.py --top`). It defines the `load_design_sv2` command and is the
consumer for `Param2` and `Hier2`. A hierarchical envelope carries the top
module followed by the transitively instantiated module library; each library
definition is checked at its own defaults before the hierarchy is instantiated.

The current example corpus contains **1,381** committed envelopes: **852**
are `sv-0.1` and **529** are `sv-0.2`. The old loader therefore remains a
live public surface, not an unused migration artifact. `Ingest2` rejects
`sv-0.1` explicitly and `Json` rejects `sv-0.2` explicitly, so deleting either
module would remove a contract rather than simplify dispatch.

## What sv-0.2 supports

The symbolic path retains module instances at module or generate scope,
symbolic parameter overrides, lexical generate paths, and one port connection
per child port. `Hier2` evaluates overrides in the parent scope, instantiates
the child at that point, hoists declarations and processes under a structural
hierarchical prefix, and turns port connections into continuous drivers with
the checked width rules. The one-driver and clock-discipline guards run after
flattening, so a child cannot bypass the same checks applied to a top-level
design.

The phase-2 corpus currently has 26 hierarchy rows: 21 match rows and five
loud rows (`PortConn:net-width`, `Instance:clock`, and `Clock:data-read`).
The matching rows cover parameter overrides, nested modules, fill values,
unconnected inputs, intact child storage, child clocks, and a procedural child
under a top.

Interfaces, `inout`/`ref` ports, type-parameter overrides, instance arrays,
gate primitives and UDPs, child definitions without defaults, port defaults,
explicit port expressions, recursive hierarchy, and unresolved multi-driver
net forms remain loud. These require new elaboration or driver state and are
not represented by silently choosing a child or flattening away its source
structure.

## Loader policy

Keep both loaders. New symbolic multi-module work belongs in `sv-0.2`,
`Ingest2`, and `Hier2`; fixes to the legacy self-check or timed process
contracts belong in `Json`, `SelfCheck`, and `Load`. A future removal of
`sv-0.1` would require migrating all 852 envelopes and the M0 proof users,
publishing a compatibility plan, and retaining an explicit rejection path for
old files. That migration has not happened, so deletion would be a breaking
change with no semantic benefit.
