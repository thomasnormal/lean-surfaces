# Unknown-bit resolution in E

Status: **design decision; implementation pending**. Until the relation is
wired through E, the approved proof boundary is the cheap sufficient condition
that every branch, conditional select, dynamic index, and assertion decision
reads a known value. A proof that cannot establish that condition must remain
loud rather than use `condTrue`'s x-optimistic else branch.

SystemVerilog `x` and `z` represent a bit whose 0/1 value is not known (IEEE
1800-2023 §6.3.1). The exact E semantics therefore treats an unknown as a set
of possible 0/1 values, rather than choosing a simulator's x-optimistic or
x-pessimistic result. A proof about a design must hold for every resolution
allowed by this relation. This is the formal-tools reading adopted by the
SystemVerilog lane; it is not an attempt to match a particular synthesizer.

## The relation

E continues to store four-state values. Alongside a four-state run, define its
finite 0/1 concretizations. A concretization replaces every unknown source bit
with 0 or 1 and then runs the same source-shaped AST and schedule. The resolved
semantics is the relation from one E state and environment choice to the set
of those concrete runs.

The choice is correlated. An uninitialized variable or input bit gets one
0/1 value for the run and keeps that value when the variable is read again.
The semantics does not choose a fresh value at each read. A value produced by
an operation may contain unknown bits; once that value is stored, its chosen
concretization is retained. If an operation itself is nondeterministic (for
example, a division-by-zero result), its explicit result witness is part of the
run choice and is likewise correlated after storage. Scheduling, active-region
order, clock timing, and environment inputs remain the independent choices
already quantified by E.

At every operation whose result depends on an unknown, the relation includes
every 0/1 result permitted by the operation's defined four-state rule and the
chosen concretization. A known result remains known. A branch, conditional
select, case match, or dynamic index is evaluated in each concrete run; if the
unknown permits both outcomes, both paths are in the relation. An out-of-range
or unknown dynamic read is therefore checked in every concrete path, and a
write is a no-op or update according to that path's resolved index. Generate
and other elaboration constants cannot contain unknown bits: those remain
loud elaboration refusals.

A 2-state assignment is a conversion boundary, not a new resolution rule.
It maps `x`/`z` to 0 as specified by IEEE 1800 §6.11; after that conversion the
stored bit is known. A formal or simulator result that disagrees with this
conversion is a consumer boundary, never a reason to change E.

## Other open choices use the same relation

The resolution relation is also the accounting rule for the remaining choices
in the tier:

* an unspecified or implementation-dependent result contributes every result
  allowed by the LRM, with the witness retained after it is stored;
* active-region races and process order are quantified by the existing schedule
  oracle, independently of the bit concretization;
* a qualified-case violation contributes the permitted violation outcome and
  never silently becomes an ordinary case;
* an out-of-range or unknown select contributes the result of each resolved
  index (an ignored write or an unknown read where the LRM requires it).

These are separate axes of choice. A proof quantifies over their product, while
preserving correlations within each run.

## Clocks and asynchronous inputs

Multiple clocks are an environment and scheduling choice, not a preferred
clock ratio. For every admissible edge timeline—including coincident edges,
arbitrary relative rates, and a stopped clock—the E relation includes every
active-region order left open by IEEE 1800 §4.7. At a coincident edge, the
defined sampling and NBA rules remain those of E; only an order the LRM leaves
open is varied.

Asynchronous inputs are likewise quantified over every admissible arrival time
and value. A transition that arrives between clock edges, at an edge, or in the
same time slot as another transition is a distinct environment choice when the
LRM permits it. There is no metastability result in this model: if the standard
defines the sampled value, E uses it; if it leaves the outcome open, the
resolution relation retains every permitted outcome. Derived cycle views and
contracts must refine this full relation rather than select one convenient
clock or arrival schedule.

## Refinement obligations

The implementation will introduce an explicit concretization/resolution
judgment over E's source-shaped states and traces. It must prove:

1. **Soundness.** Every resolved E run is a concrete run permitted by the
   four-state AST semantics, including the same environment and schedule
   choices.
2. **Known-state agreement.** If every value consulted by a decision, select,
   index, or assertion is known, the resolved relation is a singleton and its
   projection equals today's exact evaluator.
3. **Correlation.** Repeated reads of one stored unknown use the same witness;
   a state transition and its later observations preserve that witness.
4. **Derived-view refinement.** Cycle views, contracts, and proof tactics
   quantify over the resolved E relation. They may use the known-state
   sufficient condition, but may not silently select one resolution.

The migration plan is to add a `DecisionKnown` witness to the E step
judgments, lift it through `⊨₂`/`Runs2` and the cycle observation contracts,
then replace each direct `condTrue` decision with the resolution relation. The
known-state theorem will show that the old evaluator is the singleton
projection under that witness. The current direct users are the `ifStmt` and
ternary arms in `Sem2`, the procedural and memory-cycle `if` executors, the
case-check conditional path, and the proof-layer `Models2`/`Obs_run2` bridges;
each must either carry the witness or move to the resolved relation.

The first kernel-facing fragment is now present in
`LeanModels.Sv.Kernel.XResolve`: `DecisionKnown v` states that all correlated
concretizations of a condition agree on `condTrue`, and
`decisionKnown_of_allKnown` proves the cheap sufficient case used by current
proofs; `DecisionKnown.abstract` exposes the agreement with the abstract
condition for each concretization. It is a predicate and theorem only; execution remains behind the
boundary above until the state and trace relation is connected.
`TwoStateBoundary` separately records §6.11's deterministic x/z-to-zero
conversion and proves its result is unique and width-preserving; it is not a
concretization choice.
`TypedResolution` combines the two cases at the value-set boundary: a
four-state destination receives a source concretization, while a two-state
destination receives the unique `TwoStateBoundary` result. This is the next
interface for wiring declaration conversion into E without changing the
current evaluator. `typedResolution_decision_agrees` now connects that
value-set boundary to `DecisionKnown`: a known condition has the same branch
result in the abstract and resolved states. `ResolvedDecision` packages those
two premises as the object a future E branch step will consume; its
`branch_eq` theorem lifts agreement to an arbitrary branch payload.

The first regression witnesses are the clean-room designs measured by the
universal-correctness audit:

- `band_undrv.sv`: an undriven value under a parameter guard can make an `if`
  take either branch; proving only the current else-branch result is invalid.
- `band_loop.sv`: an `always_comb` loop powered up at `x` has more than one
  stable resolved state; a single settled snapshot is not a proof.
- `clmul_div1.sv`: a zero divisor can produce an unknown that controls a
  decision. The `bit` variant is a separate 2-state conversion case.

Differential rows will record simulator behavior for these shapes, but the
simulator is not the definition when it chooses one x resolution. Formal
witnesses must cover all permitted resolutions.

## Boundaries for the implementation packet

This note adds no AST constructor, lowering, or semantic fuel. The existing
four-state evaluator remains unchanged until the concretization judgment and
its refinement lemmas are implemented. Unknown-sensitive SVA booleans use the
same relation; an assertion is proved only when it holds for every resolved
sample (or the claim explicitly requires known samples). Unbounded liveness
and constructs without an E rule remain loud.
