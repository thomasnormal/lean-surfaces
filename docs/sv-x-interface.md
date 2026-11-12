# X-E interface: independent per-read resolution

This note is the interface boundary between the exact four-state semantics E
and derived cycle views, contracts, and proof tools. It records the owner's
11 November rule: an x or z is a missing promise, and every read may resolve
to 0 or 1 independently until the program overwrites it. E itself remains the
IEEE 1800 semantics; this interface does not choose a simulator result or add
a second evaluator.

## Relation shape

For one E read site, define a source-shaped read observation
`ReadAt(site, run)` containing the four-state value consulted by that site and
its declared width. The per-read relation `XRead source concrete` requires
equal widths and pointwise IEEE x/z resolution: a known 0 or 1 resolves only to
itself, while x and z resolve to either 0 or 1. `XRead` is applied anew at
each read site. There is no trace-wide map from an x bit to one remembered
choice, and two reads of the same never-written storage may resolve differently.

An X-E run is an E run with a witness for every consulted site. The witness
contains the same source AST, declaration types, environment inputs, and legal
Active/NBA schedule as E, plus one `XRead` result for each resolution site.
The witness is threaded through the operation that consumes the read and is
discarded after that operation unless the program writes the resulting value
back to storage. A later read then starts from the stored four-state value and
gets a new witness. This is a per-read relation, not a second global machine.

Two-state conversion is a separate deterministic boundary. At a declaration
or assignment whose destination is two-state, `XRead` is not used: IEEE
1800-2023 §6.11 maps x/z to zero with `TwoStateBoundary`. The result is then
the value available to later reads. Startup follows the same split: a
four-state declaration starts at its IEEE x/z value and a two-state declaration
uses the §6.11 conversion rule.

## Sites covered by the interface

The first relation and its executor cover these five classes.

1. **Procedural decisions.** `if`, ternary conditions, `case` selectors and
   case-item matching in `always_comb`, plain `always @*`, and edge bodies.
   An x at a write index is included: every resolved index is considered, and
   the theorem makes no promise about bits that only some resolved index writes.
2. **x observers.** `===`, `!==`, and `$isunknown` consult the resolved read at
   their site. A theorem that observes an undefined bit must carry the
   corresponding relation witness.
3. **Two-state conversions.** The deterministic `TwoStateBoundary` above,
   including a sampled value assigned to a two-state scalar or memory element.
4. **Start state.** Power-up values are environment-independent unknowns under
   E. A theorem quantifies over the per-read resolutions of a never-written
   four-state value; it never binds one shared unknown for the run.
5. **Control values.** An x clock, set, or reset is a possible control event.
   Until the edge scheduler has an X-E rule for it, the strict default is a
   named refusal rather than a selected edge.

The same interface applies to MemE while that derived profile exists. Its
memory index, case, two-state, and startup decisions must either carry an
X-E witness or remain refused. Continuous-driver settling and process order
remain E's existing schedule choices; they are independent axes in the
product of witnesses.

## Refinement theorem

The first theorem is a known-read refinement, stated over E's observation
interface rather than a cycle implementation:

```text
XRun e runX
KnownAt e runX
  -> observeE e = observeX runX
```

`KnownAt` says that every value consulted by a decision, dynamic index,
x-observer, or assertion sample is known, and that every two-state boundary
uses the same declared destination type. The theorem is pointwise in the
observation and quantifies over the legal E schedule and environment inputs.
It establishes that the existing exact evaluator is the singleton projection
of X-E under the known premise. A second theorem lifts this equality through
the derived cycle views and contracts; it is the required refinement theorem
for every automation-facing view.

When `KnownAt` is unavailable, the consumer has two choices: state the X-E
relation in its judgment, or produce a named refusal. It may not use
`condTrue`'s historical x-optimistic branch as an unproved result. Simulator,
synthesizer, and formal-tool traces are refinement observations only.

## Current boundaries and open decisions

The strict default is active while the relation is being wired through the
executors. Unknown-sensitive decisions, dynamic indices, assertion samples,
and x control values are refused unless the relation witness is present.
The owner has not yet chosen the policy for reading the program's own x,
power-up of an unreset two-state register, or metastability. The executable
resolver keeps those as explicit switches with strict defaults; this note does
not decide them.

`LeanModels.Sv.Kernel.XResolve` now contains the kernel-facing `XRead` and
`XReadRun` relations, together with the known-read projection theorem
`xRead_eq_of_known` and its paired-list refinement `xReadRun_eq_of_known`.
The older `DecisionKnown` predicate and `TypedResolution` lemmas remain as a
compatibility scaffold for current proofs; their correlation wording is not
the X-E authority. `Core0Resolve.execBody_if_xread` is the first consumer
bridge, proving the known-read refinement without changing `execBody`. The
next implementation step lifts `XReadRun` through `Core1Edge`, `MemE`, `Sva`,
`Observe`, `Contract`, and the cycle/run bridges. No new AST constructor,
semantic fuel, run2 meaning, or MemCycle meaning is required.

The executable probe is `harness/sv_x_resolution.py` with the committed
`harness/sv_x_resolution.json` battery. It checks independent reads of x/z
vectors, if and case decisions, unknown and out-of-range memory indices,
blocking index writes, the deterministic two-state conversion, and unknown
clock/set/reset controls. Each decision and control row has a strict switch:
the lenient switch enumerates the possible outcomes, while strict mode returns
the named refusal that a proof consumer must carry until X-E is wired through
execution. Run `python3 harness/sv_x_resolution.py`; the current battery has
13 passing rows and does not consult a simulator or alter E.
