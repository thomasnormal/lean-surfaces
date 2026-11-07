# [unreleased] — 2026-11-04 (an Sv landing builds the comb chain above it)

## Qualified SVA signal paths

SVA expressions now preserve nested instance and generate names as a single
observation-environment key, so a property such as `u.g.flag == a` remains
qualified through the E contract. The clean-room `sem2/sva_scoped` witness and
Verilator differential row cover the form; package and unavailable paths stay
loud.

Finite SVA reduction operators now use the existing `PExpr` `Reduce` nodes,
including four-state reduction-OR. The `sem2/sva_reduce` witness and Verilator
differential row cover the admitted form; nested temporal calls, dynamic
selects, and shifts remain named boundaries.

Dynamic packed element selects in SVA now retain the existing `BitSel` and
`Expr2.index` path, using declared widths from the observation environment.
The `sem2/sva_select` witness covers the sampled selector form; nested
temporal calls and shifts remain named boundaries.

Indexed packed part-selects now retain their source-shaped `PartSel` bounds,
and sized based literals retain their declared width and four-state digits.
The `sem2/sva_indexed_part` witness and Verilator row cover both forms; the
pinned `prim_packer` census loses its four selector and four vector-literal
property walls.

Finite SVA boolean conjunction, disjunction, and negation now recurse through
structured leaves, preserving nested `$past` sampling. The
`sem2/sva_past_logic` witness and its Verilator row cover the conjunction form;
the `prim_arbiter_ppc` property-expression census falls from 9 to 6, with
system calls and a shift remaining loud.

`$isunknown(expr)` now has an explicit sampled four-state knownness predicate.
The `sem2/sva_isunknown` witness and Verilator row cover the form; `$onehot0`
and other system calls remain loud.

`$onehot0(expr)` now has an explicit finite four-state predicate with the
known-one count rule. The `sem2/sva_onehot0` witness and Verilator row cover
the form; the arbiter property-expression census falls from 3 to 2.

`$countones(expr)` now has an explicit sampled four-state known-one count;
x/z bits contribute zero. The `sem2/sva_countones` witness and Verilator row
cover the retained SVA value form. The pinned `prim_packer` property census
loses its eight `$countones` invocation walls; eight unrelated nodes remain.

Finite sampled order comparisons now retain temporal operands as
`SvaValueCmp`. The `sem2/sva_past_cmp` witness and Verilator row cover
`a > $past(b)`; the arbiter remains at two independent walls for the
parameter-sized cast and one system invocation.

Fixed-width SVA shifts now use the existing sampled value-binary route. The
`sem2/sva_shift` witness covers `a << 1`; parameter-sized casts remain loud
until their width context is represented.

The first pinned F1 target now meets its property-set bar: `prim_fifo_sync`
retains all 27 assertion properties with no `Unsupported` nodes inside their
structured property ASTs. Nine design-level loader boundaries remain outside
that property set.

## Alias-flow core split

The `always_comb` continuous-copy alias walk now lives in the lower-level
`CombAliasCore` module. Parameter instantiation can import the source-shaped
flow and path checks without importing hierarchy, while `CombAlias2` keeps
its hierarchy adapter and parameter-point reporting. Existing guard behavior
and refusal messages are unchanged; wiring the guard into every semantic
family point remains a follow-up that must carry the corresponding refinement
lemmas.

## Unknown-bit resolution design

`docs/sv-x-resolution.md` records the owner-approved E design for `x`/`z`:
unknown bits are quantified over all correlated 0/1 concretizations, with
2-state conversion remaining the IEEE-defined `x`/`z` to 0 boundary. The
concretization judgment and its refinement theorems are implementation work;
this packet changes no evaluator or AST. The first implementation packet adds
the kernel-facing `LVec.concretizations` enumeration and pointwise
`LVec.Resolves` relation. Known vectors enumerate once; each `x`/`z` bit
enumerates both 0 and 1. E execution is unchanged until its refinement route
is added.

## Parameter-sized unpacked memories on the cycle route

The memory cycle adapter now retains one-rank parameter-sized unpacked arrays
as source-shaped E memory for both `[N]` and `[0:N-1]` spellings. Constant
cell reads and writes, genvar-indexed generated writers, plain edge `always`
and `always_ff`, and active-high/active-low asynchronous reset forms stay
separate from scalar state and never expand a default-point array. Clocked
processes fire only on their declared edge; falling-clock rows therefore
leave the cell unchanged. The `seq_mem` fixtures cover the plain/FF and
reset/no-reset matrix, and `seq_mem/gen_ff` covers retained genvar writers.
Nested arrays, dynamic runtime indices, partial cell targets, and hierarchy
remain loud.

## Exact signed-32-bit `int` constants at every parameter point

`PDesign.instantiate2` and hierarchical instantiation now evaluate `int`-class
parameters and localparams through the exact signed-32-bit path for every
parameter argument, rather than using the unbounded constant path by default.
`int32Agrees` remains the diagnostic comparing that path with the unbounded
proof route. The `add_int32` fixture checks both the default `N=16` and the
non-default `N=5`, where `1073741824 * 2` wraps to `-2147483648` and selects
the other generate arm.

## Signed dynamic select indices

Dynamic packed and unpacked element selects now retain the source expression's
signedness through ingestion and evaluation. A signed declaration, explicit
`$signed` cast, or signed literal is evaluated as a two's-complement `Int`;
negative reads produce all `x` and negative writes are no-ops, while unsigned
indices keep the existing `toNat?` behavior. The `sem2/signed_index` fixtures
pin both read and write outcomes. The comb and sequential observation proofs
now use the same signed/unsigned index split.

## Qualified-case checks at execution time

`unique`, `unique0`, and `priority` claims are now checked in reset, edge, and
combinational process execution, before any NBA commit. The old post-trace
validation could inspect the wrong state for an edge process. The
`qualified_case_timing` rows cover a pre-edge violation and a violation
created by one edge and observed on the next.

## Exact multi-clock E instants

The E semantics now has a source-shaped `ClockInstant`/`runMulti` route for
designs with several input clocks. Each instant names the rising clocks and
its settled inputs; selected edge processes evaluate against the common
pre-instant state and commit NBAs together, so coincident edges sample old
values. Clock ratios, drift, stopped clocks, and coincident edges are supplied
by the instant list, while the schedule oracle still covers active-process
order. No metastability or resolution approximation is part of E. The legacy
one-clock `runner2` transport remains loud for `Clock:multiple` until it gains
an instant-list stimulus encoding.

## Guarded generate and non-affine genvar obligations

The comb recognizer now names the two Sklansky-shaped proof walls explicitly:
a conditional generate inside a generate loop reports a `GuardEval` obligation
for selecting the reached arm, and a dynamic or nonlinear genvar index reports
a `non-affine genvar-index` obligation because its driven window is not known.
The clean-room `sklansky_guards` fixture pins the conditional-generate message;
the ripple-adder negative rows pin the index message. The clean-room
`sklansky_guards/nonaffine` fixture now pins the same named obligation for a
non-affine read. Neither shape is silently flattened or assigned a fabricated
window.
Verification on 2026-11-06 rebuilt `LeanModels.Sv.CombViewMain` and both
clean-room fixtures; the named obligations remain stable on the green chain.

The third Sklansky wall is pinned by the clean-room
`sklansky_guards/clog2_int` fixture: a `localparam int L = $clog2(N + 1)`
loads through the same 32-bit signed constant class as an `integer` localparam,
with `int32Agrees` at `N = 16` and `N = 1`. Guarded-family retention itself
remains behind the named guard-totality obligation; a branch that cannot be
shown to evaluate at every reached genvar value stays loud rather than being
dropped from the family.

The SRT clean-room forms are also parsed by the proc-aware summary: its
`always_comb case` table is retained as a case tree, and a shift by the
`XS` localparam reaches the shift reader. Generic `sv_structure` proofs of
the parameterized rows currently stop earlier at the named environment-value
obligation; the corresponding `CombViewTactic` parameter-environment slice
is owned by the integration lane.

## Straight-line automatic functions with local case

Pure automatic input-only functions may now contain local declarations, a
blocking plain `case` with a `default`, and a return of the local temporary.
The symbolic extractor preserves the case as nested case-equality ternaries;
the `function_case_eval` fixture and Icarus differential row cover the form.
Stateful functions, loops, recursion, static storage, and output/ref formals
remain loud. Qualified `unique`, `unique0`, and `priority` cases are admitted
when labels are distinct concrete integral literals and a `default` arm is
present, which proves that the claim cannot be violated for any input.
Dynamic, overlapping, or incomplete qualified cases remain loud rather than
falling through to plain-case behavior; `function_unique_case_eval` pins the
admitted shape.

The `function_case_return_name` clean-room witness also admits a qualified
case whose default arm assigns the function name while an explicit `return`
publishes the local temporary. The inliner preserves the temporary's
uninitialized `x` result on that path instead of substituting the unrelated
function-name assignment.

## Mixed combinational and asynchronous-reset cycles

The sequential reset profile now admits continuous assignments and comb
processes next to a shared asynchronous-reset `always_ff`. `firstResetKey?`
finds the clock/reset pair in source order, and `CombPhaseAcyclic` plus
`cycleStep2_mixedProfile` provide the refinement boundary for the comb settle
before reset, edge/NBA, and final settle. The `async_reset_comb_profile`
witness and its Icarus differential row cover a continuous next-state signal
feeding the reset flop. The no-reset `ffMixedProfileB` companion accepts the
same comb-plus-edge source shape. Hierarchy, initial ROM loading, and comb
cycles without an acyclic settle contract remain loud.

## F4: one-rank sequential unpacked memories

The symbolic extractor now retains the shorthand `mem [N]` as a source-shaped
`UnpackedDecl` with the `[0:N-1]` bound, and retains `mem[i]` as an `ArraySel`
path rather than a default-point cell. `Kernel/MemCycle` connects that form to
the fuel-free `MemState` storage through a provisional cycle view: scalar
conditions, direct cell reads, scalar or cell NBAs, asynchronous reset, and a
continuous scalar read are covered by the `async_mem_fifo` clean-room fixture.
Nested ranks, partial targets, loops, and compound memory expressions remain
loud. The fixture matches Icarus over three reset/write/read cycles.

The same source-shaped route now admits run-time indices for a
parameter-sized one-rank register memory. `ArraySel` reads and NBA targets are
resolved at issue time against the scalar state; known indices update one
`MemState` cell, unknown reads return all-x, and unknown or out-of-range writes
are no-ops. `sem2/unpacked_register_memory` and its Icarus row cover the
three-cycle read-after-write trace; nested and compound memory forms remain
loud.
The R2 memory route now also executes a source-shaped `always_comb` blocking
read after sequential memory commits. The `sem2/unpacked_memory_comb` witness
and direct Icarus row cover this form; NBA in `always_comb` remains loud.
Undriven four-state wires remain source-shaped `pdesign.others` metadata, and
the memory route keeps its named unsupported-member refusal until net
resolution is represented. The `sem2/unpacked_memory_netz` guard covers the
boundary.
The item-2 clean-room PicoRV32 wall pair is pinned under
`Examples/system-verilog/cores/picorv32/walls`; its probe checks the exact
ordinary unpacked-memory and memory-route net-z refusals without adapting
PicoRV32.
Referenced empty input-only tasks are now retained as
`SubroutineSymbol:empty-task` metadata in the memory route, and their calls
execute as the existing empty statement. The `task_memory` wall proves the
source-shaped no-op; stateful, timed, output, defaulted, and nonempty tasks
remain loud.

The Sem2 `run2`, `run2ExecChecks`, and observation runner now apply a
`Clock:multiple`/`Clock:implicit` guard before the one-clock edge pass. The
ordinary `clk_two` route therefore refuses, while the exact `runMulti` instant
route remains available; `clk_implicit` records the data-driven event-control
refusal.

The x-resolution ruling is now recorded as an active proof boundary: until E
quantifies correlated 0/1 concretizations, decisions and dynamic selects must
carry a known-value witness or remain loud. Existing `condTrue` x-optimism is
not a proof rule; the migration plan and its current call sites are listed in
`docs/sv-x-resolution.md`.
The kernel now exposes `DecisionKnown` over correlated concretizations and a
known-state theorem, without changing execution until the refinement relation
is connected to E.

The x-resolution note now defines the differential testing levels: H is the
nondeterministic relation, E the deterministic IEEE execution, and S/J
downstream refinements. Known-value rows remain equality tests; rows that read
unknowns use membership in H, classifying a simulator's selected x behavior
without changing E.

## Initial `$readmemh` remains a named F4 boundary

The clean-room `sem2/readmemh_rom` fixture now records an initial
`$readmemh("rom.hex", rom)` process as `ProceduralBlockSymbol:Initial` in the
symbolic envelope and in the instantiated `Design2`. The ROM declaration and
its dynamic read assignment remain visible. Initial-process scheduling and
file-loading semantics are still required before this shape can enter E, so
the differential row is a loud refusal rather than a fabricated time-zero
memory image.

## Plain edge-triggered `always` joins the NBA cycle profile

`Design2.ffOnlyProfileB` and its kernel-checked cycle theorem now accept a
plain `always @(posedge clk)` when its body satisfies the same NBA-only,
static-target, single-clock conditions as the existing `always_ff` profile.
The retained `Process2.alwaysPlain` constructor is preserved, so this is a
profile admission rather than a source-kind rewrite. The `seq_plain` witness
and `plain_always_profile` differential row match Icarus over four cycles;
blocking plain processes, asynchronous reset, mixed clocks, and overlapping
windows remain loud boundaries.

## Active-low asynchronous reset joins the sequential profile

`Design2.ffResetProfileB` now recognizes retained `always_ff @(posedge clk or
negedge rstn)` processes with a shared clock/reset pair, NBA-only bodies, and
static targets. `resetPass2_ffResetOnly` records the reset-event bridge: the
selected reset processes preserve state and append their source-shaped NBA
updates. The `seq_async_reset` guards cover reset assertion and release, and
the `async_reset_ff_profile` differential row matches Icarus over five cycles;
other reset controls and blocking bodies remain loud.

## Pure automatic function calls inline in combinational expressions

The existing symbolic extractor path now has a clean-room receipt for a
side-effect-free automatic function with input-only formals:
`step(a)` is retained as the exact `a + 4'd1` expression, so run2 evaluates
it without adding a call node or a new AST constructor. The
`user_function_eval` differential row matches Icarus over four cycles.
Recursive, static, task, output/ref, stateful, and otherwise unsupported calls
remain loud at the named `CallExpression` boundary.

## F1: audit retained SVA forms against downstream clean-room repros

`SvaContract.parseSimple` now admits a finite `$past(signal, depth)` operand
and handles a nested closing parenthesis in a `disable iff` body without
truncating the consequent. Kernel guards cover a finite assertion with
`disable iff`, a bounded assertion, and an assumption using `$rose`, finite
`$past`, and `disable iff (!rst)` with `$stable`.

The clean-room audit records the current target walls in
`docs/sv-frontier.md`: plain `always`, async-reset `always_ff`, sequential
unpacked memories, hierarchy, user-function calls, and initial `$readmemh`
remain named boundaries. Finite assertions, bounded ranges, and assumptions
with `disable iff` retain metadata and connect to the E contract. A bare cover
sequence remains loud because the current contract requires an implication;
immediate assertions and unbounded `s_eventually` remain outside F1 by design.

## `Lib/Prefix.lean`: parallel-prefix carry arithmetic

A new library module (imports nothing; indexed in `Lib.lean`) with the facts any
prefix-adder proof uses: the (generate, propagate) carry operator `pgOp` with
associativity, an empty-block unit and idempotence; group generate/propagate of
a block `pgBlock f j k` and the combination of adjacent or overlapping blocks;
the adder's positions `addPos` (position 0 carries the carry in), the carry into
bit `k` as the group generate of positions `[0, k]` (`pgBlock_addPos_zero`), and
its agreement with core's `BitVec.carry` (`rippleCarry_bv`). Nothing in it is
specific to one adder: svGolf's Sklansky proof keeps its aligned-block
recurrence in its own reference, by the rule of the Newton move below.

## `Lib/XFVal.lean`: a carry-save row and an XOR with the top bit

Two general `XF.val` facts, from svGolf's radix-4 SRT divider reference
(`fdivp_srt`): `val_csa`, a carry-save adder row (the XOR sum plus twice the
majority is the sum of the three rows, at every width), and `val_xor_top`, an
XOR with the one-hot constant of the top bit (`+ 2^n` modulo `2^(n+1)`). They
hold for any design that uses those shapes, so they stay in the library; the
SRT model itself (the selection table, the stage invariant, on-the-fly
conversion) is that reference's own section `SrCore`, by the rule of the
Newton move below. Nothing is renamed; the `Lib.lean` index names the two
lemmas.

## `Lib/Newton.lean` moves into the fdivp_newton reference

`LeanModels/Sv/Lib/Newton.lean` leaves the library, and with it
`Lib.correct_quot_of_rem_lt_three_mul` (`Lib/NatArith.lean`, the correction
stage of the same core): both model the Newton-Raphson core of one svGolf
reference, `fdivp_newton`, and nothing else uses them. They are now that
reference's section `NwCore` (`svgolf/tasks/fdivp/reference/fdivp_newton.lean`,
namespace `SvGolf.FdivParam`), statements and proofs unchanged, compiled in its
solution stage like a golfer's own proof of their own core (decided 11/04:
code the library prebuilds is time a golfer's equivalent code would not get,
so the library keeps only results that any proof of a class of designs would
use). All 21 declarations of `Newton.lean` lie on the proof paths of the three
the reference cites (`nwR0_hw`, `newton_rest`, `nwNI_spec`), so none is
deleted. `Lib.lean` drops the import; nothing else imported the module
(`tools/check_sv_chain.sh --dependents` is empty for `Lib.lean`,
`Lib/Newton.lean` and `Lib/NatArith.lean`).

The audit of the rest of `Lib/` by the same rule moves nothing else.
`two_mul_le_mul_self_add_mul_self` and `mod_add_sub_mod_of_eq_add` are now used
by that section alone but are plain `Nat` facts; `BitVecArith`'s lemmas are used
by `matmul_g1` alone but hold at every width; the scaled comparisons, powers
and remainders of `NatArith`, the `XF.val` facts, `RowMajor` and `Restoring`
(the model the shared math layer of every fdivp reference reads) serve two or
more references.

Measured (`check.py --no-score`, a fresh stage each, one run at a time,
`LEAN_NUM_THREADS=2`, nice 19): the solution stage of `fdivp_newton` took
46.9 s just before the move (load average 9.5) and 49.9, 48.6, 52.7 s after it
(6.1, 9.9, 6.6; a fourth run, the load rising from 7.4 to 11.2: 58.1 s), of its
120 s; elaborated single-threaded, the whole file goes
from 1,627,676 to 1,677,866 thousand heartbeats, `NwCore` taking 49,233
thousand. `fdivp`, whose file is unchanged, is accepted (69.7 s at load 9.1;
one run took 114.5 s while the load rose from 6.5 to 9.6). `lake build
LeanModels.Sv.Lib LeanModels.Sv.SeqFamily LeanModels.Sv.SeqProfile` and svGolf's
`lake build SvGolf tasks svgolf-eval` are green.

## Stable symbolic replication simplification

`sv2_inst_simp` now unfolds the constant-context classifier and its structural
workers by default, including signal-operand detection, select roots, and
constant operation classes. A guard covers the parameterized sign-extension
replication shape used by downstream proofs, so a free replication count is
classified as a signal-context refusal without requiring private helper names.

## F4: procedural memory NBA adapter

The E kernel now has a source-shaped one-rank memory process adapter. Memory
NBA entries retain their declaration and `PLhs.arrayElem` target, enqueue
without flattening, and commit through `MemState`. Scalar RHS values use the
existing expression evaluator; direct memory-cell reads are explicit, while
compound memory expressions remain loud until their source-shaped evaluator is
defined.

## F1: parse the first retained SVA implication form

`SvaContract.parseSimple` now turns retained source text of the form
`assert/assume/cover property (@(posedge clk) a |-> b);` into a checked E
contract. Signal names, the retained clock, and assertion kind are validated;
the non-overlapped `|=>` form is covered as well. Delays, expressions, reset
guards, and other SVA forms remain loud.

The same parser now admits an exact `##n` delay in either implication arm,
mapping it to the finite `SvaSeq.delay` evaluator. Bounded ranges and dynamic
delays are now distinguished: finite `##[m:n]` maps to `SvaSeq.range`, while
dynamic delays remain loud. Simple `$past(signal)` operands now map to the
sampled `SvaBool.past` form, and `$rose(signal)` maps to `SvaBool.rose`.
`$fell(signal)` now maps to `SvaBool.fell` as well.
`$stable(signal)` now maps to `SvaBool.stable`.
The retained `disable iff (reset)` wrapper now maps to `SvaProp.disable` for
simple signal guards.
The first boolean conjunction/disjunction forms (`a && b`, `a || b`) now map
to `SvaBool.and` and `SvaBool.or`.
Simple case equality (`a === b`) now maps to `SvaBool.caseEq`.
Simple boolean negation (`!a`) now maps to `SvaBool.not`.
The retained `cover property` spelling now has a direct parser guard, checking
that the source kind and constructed E check are both `cover`.
The corresponding `assume property` spelling is guarded as `.assume` as well.

The retained SVA expression adapter now carries unbased unsized literals as
four-state fills (`'0`, `'1`, `'x`, and `'z`) at the self-determined operand
width. `sem2/sva_unbased_literal` proves the `'0` assertion on both a passing
and a failing sampled trace, and the source is accepted by Verilator's SVA
front end. Other unsupported assertion expressions remain named boundaries.
Re-running the pinned OpenTitan `prim_fifo_sync` assertion VIP retains all 27
properties and reduces its unsupported-node census from 56 to 29 by removing
the 27 unbased-literal nodes; the remaining nodes are independent loader
walls.

The SVA source adapter also unwraps `ParenthesizedPropertyExpr` before it
classifies implications and delayed sequences. The same pinned VIP now has 18
residual unsupported nodes, with all 27 assertion properties still retained.

Finite SVA logical implication (`->`) and equivalence (`<->`) expressions now
lower to the existing sampled boolean operators. The clean-room
`sem2/sva_logical_ops` witness and Verilator row cover both forms. The pinned
`prim_fifo_sync` VIP retains all 27 properties with 15 residual unsupported
nodes; nested `$past` expressions remain a named boundary.

Finite sampled value expressions now retain `$past` through equality and
arithmetic trees. `sem2/sva_past_value` checks both a previous-value equality
and a previous-value increment against the E trace, with a Verilator row. The
pinned `prim_fifo_sync` assertion VIP retains all 27 properties and has 11
residual unsupported nodes; the remaining nodes are outside this value
fragment.

Finite SVA `inside` sets of literal items now lower to case-equality
disjunctions, preserving four-state sampled behavior and width-directed
literal fills. The `sem2/sva_inside` witness and Verilator row cover the
source form; the pinned VIP census retains all 27 properties with 10 residual
unsupported nodes.

## F1: prove the SVA sampling refinement

The finite SVA evaluator now has kernel-checked `clockSamples_final_irrel` and
`evalRegion_final_irrel` facts. Replacing every slot's post-NBA/final state
with an arbitrary value leaves assertion results unchanged, pinning the
Preponed-only sampling rule that the E property contract consumes.

## F1: connect retained SVA properties to observation contracts

`LeanModels.Sv.SvaContract` now carries a retained `PProperty` beside its
structured `SvaCheck`, checks the source kind and clock, and evaluates the
property through the backend-generic observation `Safe` judgment over trusted
port samples. The original source text remains attached; unsupported source
forms stay loud until a structured F1 parser rule exists.

## F1: retain SVA generate paths

Retained concurrent assertions now carry their lexical generate labels in the
symbolic envelope's `SvaProperty.path` field. Module-level assertions use an
empty path; generated instance indices remain structural hierarchy metadata
and are not flattened into the property. The property remains out of
`Stmt2` and executable process lists.

## Active-high asynchronous reset now retained in E

The retained `alwaysFFR` process now carries reset polarity through the
parametric and semantic envelopes. `always_ff @(posedge clk or posedge rst)`
fires its reset phase on a `0 -> 1` edge, while reset release does not wake the
process. The clean `clk_arst_high` witness and six-cycle Icarus row match the
active-high LRM behavior. `areset_n` remains the active-low form; negative-edge
clocks and `iff` guards remain named loader refusals.

## Loader loudness for discarded edge-control fields

`Ingest2` refuses negative-edge `edge` and `iff` fields rather than silently
changing them into plain positive-edge `alwaysFF`. The active-high `areset`
case has since moved into the retained E process path above. The clean-room
`loader_refuse_negedge` and `loader_refuse_iff` fixtures remain recorded
refusals.

## E edge selector for negative clocks

The E-core edge primitive now carries an explicit `ClockEdge` selector. Existing
edge profiles default to `posedge`; a retained negative-edge process uses the
same four-state IEEE edge predicate, with kernel guards for falling-edge firing
and release non-firing. Loader admission and source-shaped clocked-process
wiring remain a separate boundary.

## F1: asynchronous-reset edge table in E

The E-core-1 edge witness now checks the complete asynchronous active-low
reset boundary used by the OpenTitan targets: assertion with the clock held
low, release without a wakeup, `1 -> x` and `x -> 0` reset edges, and a clock
edge while reset is asserted. The kernel-checked `Core1Smoke` guards exercise
the shared IEEE 1800 §9.4.2 edge table and the whole-body execution rule. The
`clk_arst_reset_edges` row matches Icarus over seven cycles; the existing
`clk_arst` Xcelium golden row remains unchanged. Verilator's startup and
unknown-value behavior is not treated as an oracle for this row.

## F1: retained SVA safety envelope over E samples

The first F1 slice adds `LeanModels.Sv.Sva`, a retained property envelope that
does not alter frozen `Stmt2` or lower an assertion into procedural code. It
selects Preponed samples at positive clock edges and evaluates boolean signals,
four-state case equality, `|->`, `|=>`, finite `##n` and `##[m:n]`, `$past`,
`$rose`, `$fell`, `$stable`, `disable iff`, and assert/assume/cover outcomes
without semantic fuel. Kernel-reducible witnesses cover both passing and
failing checks, a finite delayed sequence, and a positive-edge cover.

Unbounded and liveness operators remain loud. The OpenTitan FPV source census
still reaches `ProceduralBlockSymbol:NoEventControl` until the extractor and
loader retain those source assertions; that is the next F1 integration step.

## F1: concurrent assertion members retained in sv-0.2 envelopes

Symbolic extraction now recognizes slang's `ConcurrentAssertionMemberSyntax`
and records each assert, assume, or cover property under the module's retained
`properties` metadata: its kind, clock spelling, source span, and source text.
It is no longer emitted as a runnable `ProceduralBlockSymbol:NoEventControl`.
The `sva_property_retained` witness loads its ordinary async-reset process and
keeps all three property members. Its three-cycle stimulus passes Verilator
5.052 with assertions enabled; Icarus 12 cannot parse concurrent SVA and is
recorded as unavailable for this row. The E predicate guards cover the finite
safety meaning.

Assertions in constant generate scopes use the same retained metadata route;
they no longer become `NoEventControl` process refusals. The source generate
body stays structural and empty of executable processes until property paths
are part of the hierarchy contract.

## Parameter-dependent unpacked arrays: source retention

The `unpacked_generate_array` clean-room witness records the current boundary
for a declaration such as `logic [W-1:0] stage [0:S-1]`: slang emits
`VariableSymbol:default-point-array`, and the symbolic extractor now retains
the source-shaped declaration rather than sampling slang's default-point
cells. Flattening those cells would give parameter changes the wrong layout.
The legacy `Design2` runner still records `UnpackedDecl:memory` as a loud
refusal; the memory cycle route below handles the admitted one-rank shape.

The symbolic envelope now retains that declaration as `UnpackedDecl`, carrying
the packed element type and each parameter-dependent unpacked bound. The
current flat E store still does not fabricate default-point cells. This is the
source-shape packet for the array-valued memory rung; the admitted one-rank
process path is described above.

## Native E memory state

`LeanModels.Sv.Kernel.CoreMem` adds the first array-valued E primitive. It
keeps source bounds and element width, supports named memory lookup and
functional cell writes, and proves same-cell, other-cell, out-of-range, and
unknown-memory laws without fuel or default-point expansion. Retained
`UnpackedDecl` nodes now have a one-rank elaboration bridge in
`Kernel/MemElab`, while nested ranks and process lowering remain loud until
array targets are wired to this state.

The memory bridge now also resolves one-rank `PLhs.arrayElem` targets by their
source labels and delegates read/write behavior to `MemState`. Out-of-range
accesses retain E's all-x/no-op behavior; dynamic and partial targets remain
loud.

## Known constant replications

Replications of known constant operands now evaluate in typed parameter and
localparam contexts. `constant_replication` matches Lean and Icarus at E = 4,
8, and 12, with multi-point checks agreeing at every point. Signals,
unknown operands, negative counts, and empty replications remain loud.

## Typed packed parameter fills

Typed packed parameter and localparam defaults using `'0` or `'1` now use the
declared assignment width in the constant evaluator. `unsized_param_literal`
matches Lean and Icarus at W = 4, 8, and 12, with the multi-point checks
agreeing at each point. x/z fills remain loud in constant contexts.

## Signed packed localparam initializers

The symbolic extractor now retains a signed INT-class initializer such as
`localparam signed [11:0] DOUBLE_BIAS = 2 * BIAS` as its source expression.
The loader evaluates that tree through the declared-width assignment context
at each parameter point instead of refusing the implicit width conversion
(`ConversionExpression:width`). The new `signed_localparam_cast` fixture is
covered at E = 4, 8, and 12; all three rows agree with Icarus, including the
multi-point cross-check.

## The shared proof library, made general: names, homes, docstrings

The design-independent lemmas that the clocked svGolf references (matmul, sorter) moved into
`SeqFamily.lean`/`SeqProfile.lean`, and the word-level `Lib/*` that the fdivp references use, are
brought to one standard: every name says what the lemma states, every public declaration has a
docstring, statements carry no task's widths or shapes, duplicates of core or of other
`LeanModels.Sv` lemmas are gone, and each fact sits in the module whose concept it is. No statement
of a trusted file changes.

* **Core instead of copies.** `mullt` is `Nat.mul_lt_mul_of_pos_left`, `divmod_unique` is
  `Nat.div_mod_unique`, `frac_split` is `Nat.mod_mul`, `kinc` is `BitVec.ofNat_add_ofNat`, `cast3`
  is two `Int.natCast_mul`; `XF.val_low_in`, `XF.val_zext_eta`, `XF.val_ztr` are `val_of_testBit`,
  `XF.val_zext`, `val_zext_trunc`; `insertAt_full` (SeqFamily's and `Loop2.insertAt_full`) is
  `LVec.insertAt_zero_of_width_eq` (`Comb2Base`); `flatMap_congr'` is `CombView.flatMap_congr'`;
  `mul_add_le` is `rowMajor_le` (`Hier2Gen`); `n_bound` is `evalInt_paramRef_of`/`isInt_paramRef_of`
  with `vals_lookup_bindVal_ne`.
* **General statements.** `keq`, `c32_nat`, `sh_step` had width 32 baked in, `win_le` a square
  array, `n_bound` the parameter name `"N"`, `mul_pow2`/`mul_pow3` base 2, `mac` the accumulator
  shape `AccW + W`, `val_shl1` the shift width 32: now `Lib.ofNat_eq_ofNat_sub_one_iff` (any width,
  and any `N ≤ 2^w`, so a full-range counter too), `LVec.ofInt_eq_ofBitVec` (any width and value),
  `LVec.shr_ofBitVec` plus core rewrites, `Lib.rowMajor_window_le` (`M×N`), `mul_pow_mul_pow` (any
  base), `Lib.setWidth_add_mul_signExtend` (any wider width), `XF.val_shlBits_one` (any shift width
  `wr ≥ 1`). Hypotheses implied by the others are gone: `mod_cases_of_lt_three_mul` (was `mod3`) drops
  its unused `0 < Z`, `div_mod_two_eq_zero_iff_lt`, `mod_add_sub_mod_of_eq_add` and
  `correct_quot_of_rem_lt_three_mul` their positivity hypotheses (`0 < H`, `0 < M`, `0 < mb`),
  `foldl_range_ofBitVec_packBV` its `m ≤ N`; `nbaFold_flatMap`/`_eq_self` take any index type.
  `XF.val_const` becomes `XF.val_constBit` (any constant width `W ≥ w`), with `val_constBit_one`
  its instance at `1`. `sum_packed` becomes the public `packBV_eq_ofNat` (the packed vector is
  `Σ_r (v r)·2^(r·W)`), so matmul's `product_eq` is one line.
* **Homes.** `Lib/NatArith.lean` takes the row-major window arithmetic and its `Int` labels
  (`mul_add_mem_window_iff`, `rowMajor_window_le`, `window_bounds_of_natCast`,
  `min/max_add_sub_one_self`, `add_sub_one_sub_add_one`, `natAbs_sub_one_add_one`) and Newton's
  generic steps (`two_mul_le_mul_self_add_mul_self`, which no longer clashes with Mathlib's
  `two_mul_le_add_sq`, `mod_add_sub_mod_of_eq_add`, `correct_quot_of_rem_lt_three_mul`). The new
  import-free `Lib/BitVecArith.lean` takes the datapath `BitVec` facts. `Known2.lean` takes
  `knownBit` (the known 1-bit vector, was `bit`), `condTrue_knownBit`, `LVec.resizeU_one_l0/_l1`,
  `LVec.ofBitVec_replicate_append_eq_signExtend` and `@[simp] LVec.shr_ofBitVec` (the `>>` of the
  `sv2_known` set). `Gen2.lean` takes `Gen2.except_pure` and `vals_lookup_bindVal_self/_ne`
  (from `Loop2`, now in the root namespace). `Hier2Gen.lean` takes `DrvWin.overlaps_comm`,
  `NbaCommit.lean` takes `commitNba2_nil`, `nbaFold` with its lemmas and `width_foldl_insertAt`,
  `Seq2Cycle.lean` takes `CycleModel` (from svGolf's `Seq.lean`: it is SV semantics),
  `CombViewArith.lean` takes `flatMap_range_eq` (next to `flatMap_congr'`).
* **Unused, deleted.** `insFold_eq_packBV`, `newton_NI`.
* **Private.** `indexWin?_some`, Newton's `nw_pows`, `nw_err_sq`, `nw_first`, `nw_next`.

Renames, for readers of the old names:

| Old | New |
|---|---|
| `Lib.log2_mul_pow`, `mod_wrap`, `ydec_eq`, `mod3`, `bit_top` | `log2_mul_two_pow`, `add_two_pow_sub_mod_two_pow`, `add_sub_one_mod_of_lt`, `mod_cases_of_lt_three_mul`, `div_mod_two_eq_zero_iff_lt` |
| `Lib.mul_pow2`, `mul_pow3` | `mul_pow_mul_pow`, `mul_pow_mul_pow_mul_pow` |
| `Lib.two_mul_le_add_sq`, `mod_sub_of_lt`, `nw_correct` | `two_mul_le_mul_self_add_mul_self`, `mod_add_sub_mod_of_eq_add`, `correct_quot_of_rem_lt_three_mul` |
| `Lib.rmN_cell` | `rmN_last_col` |
| `XF.val_bits`, `val_win`, `val_win_in` | `val_of_testBit`, `val_window`, `val_window_of_testBit` |
| `XF.any_eq`, `all_eq`, `eqv_val`, `bit_eq` | `any_eq_decide_val`, `all_eq_decide_val`, `eqv_eq_decide_val`, `bit_eq_of_val` |
| `XF.val_const`, `val_constBit1`, `val_constBit0`, `constBit0_false` | `val_constBit`, `val_constBit_one`, `val_constBit_zero`, `constBit_zero` |
| `XF.val_shl_var`, `val_shr_var`, `val_shl1`, `val_shl0` | `val_shlBits_zext`, `val_shrBits`, `val_shlBits_one`, `val_cons_false` |
| `XF.top_bit`, `top_bit'` | `top_bit_iff`, `top_bit_succ_iff` |
| `insFold`, `insFold_succ`, `getLsbD_insFold` | `bvInsertEntries`, `bvInsertEntries_succ`, `getLsbD_bvInsertEntries` |
| `lfold`, `lfold_succ`, `width_lfold`, `lfold_ofBitVec`, `lfold_insertAt`, `lfold_last` | `LVec.insertEntries`, `_succ`, `LVec.width_insertEntries` (`@[simp]`), `LVec.insertEntries_ofBitVec`, `LVec.insertEntries_insertAt`, `LVec.foldl_range_insertAt_last` |
| `packBV_upd`, `extract_packBV`, `packBV_family` | `bvInsertAt_packBV`, `extract_ofBitVec_packBV`, `foldl_range_ofBitVec_packBV` |
| `mul_add_le`, `unit_win_iff`, `win_le`, `win_facts`, `win_min`, `win_max`, `win_wid`, `natAbs_pred` | `rowMajor_le` (`Hier2Gen`, existing), `Lib.mul_add_mem_window_iff`, `Lib.rowMajor_window_le`, `Lib.window_bounds_of_natCast`, `Lib.min_add_sub_one_self`, `Lib.max_add_sub_one_self`, `Lib.add_sub_one_sub_add_one`, `Lib.natAbs_sub_one_add_one` |
| `setWidth_sext`, `mac`, `ext_shr`, `keq` | `Lib.setWidth_signExtend_of_le`, `Lib.setWidth_add_mul_signExtend`, `Lib.extractLsb'_ushiftRight`, `Lib.ofNat_eq_ofNat_sub_one_iff` |
| `bit`, `cond_bit`, `l0_bit`, `l1_bit`, `sx_eq`, `shr_ofBitVec` | `knownBit`, `condTrue_knownBit`, `LVec.resizeU_one_l0`, `LVec.resizeU_one_l1`, `LVec.ofBitVec_replicate_append_eq_signExtend`, `LVec.shr_ofBitVec` |
| `commit_nil`, `width_foldl`, `nbaFold_flatMap_id`, `overlaps_comm`, `except_pure` | `commitNba2_nil`, `width_foldl_insertAt`, `nbaFold_flatMap_eq_self`, `DrvWin.overlaps_comm`, `Gen2.except_pure` |
| `clockStep_wellFormed`, `negFlop`, `negPre` | `clockStep_eq_of_wellFormed`, `OmittedProcess.flop`, `OmittedProcess.pre` |
| `Loop2.vals_lookup_bindVal_self/_ne` | `vals_lookup_bindVal_self/_ne` (in `Gen2`) |
| `flatMap_range_eq` (SeqFamily) | `CombView.flatMap_range_eq` (`CombViewArith`) |
| svGolf `SvGolf.CycleModel`, `StreamTask.PhaseModel.pend` | `LeanModels.Sv.CycleModel`, `StreamTask.PhaseModel.out_eq_false_of_emitted` |

Measured: one root `lake build` of 142 targets is green (217 jobs, 176 built): the `LeanModels.Sv`
imports of `LeanModels.lean`, `SeqFamily`, `SeqProfile`, `Seq2Cycle`, `Loop2`, `Loop2E`, `Loop2Sem`, the
103 chain modules `tools/check_sv_chain.sh --dependents` names for the changed files, and the Examples
`seq_neg/check`, `loop_edges/schema`, `loop_nested_clmul/schema`, `mul2d/gen`, `partsel/gen`,
`ripple_add/gen`, `ripple_fa/gen`, `shifts/proof` (the ones whose text uses `bindVal` lookups or `>>`,
which meet the two global simp lemmas that changed module). svGolf's `lake build SvGolf tests` is green
(102 jobs); `check.py --no-score` accepts `matmul_g1` (solution stage 28.5 s), `sorter_ins` (21.4 s),
the seq_counter fixture (12.9 s), `fdivp` (73.2 s) and `fdivp_newton` (91.4 s), and
`tests/fdivp/shared_sections.py` holds. Every `#print axioms` of `SeqFamily`, `SeqProfile`, `Seq2Cycle`
and svGolf's `Seq.lean` shows at most `propext`, `Classical.choice`, `Quot.sound`; no `sorry`, `admit`,
`native_decide` or `bv_decide`. The reducibility probe passes. Not rebuilt: the other SV Examples that
import a changed module only for its old content (no `bindVal`/`>>` in their text). The fdivp timings
are not stable on this host: at load average 9 to 12 the same trees measured 93.8, 116.3 and 120.4 s
(`fdivp`, the last one over the 120 s limit) and 58.5, 191.6 and 91.4 s (`fdivp_newton`), with the
kernel replay (`leanchecker`) steady, so the 120 s limit wants a quiet machine to judge.

Review pass (one duplicate, hypotheses the others imply, two widths, every `PhaseModel` field documented,
module docs listing what each file offers). Measured: one root `lake build` of 143 targets is green (212
jobs, 166 built): the `LeanModels.Sv` imports of `LeanModels.lean`, the changed modules, `Lib`, `Seq2Cycle`,
`Loop2`, `Loop2E`, `Loop2Sem`, the 104 chain modules `--dependents` names, and `seq_neg/check`; no new
warning in a changed file. `lake build SvGolf tests` is green (102 jobs). `check.py --no-score` (limit 600 s)
accepts `matmul_g1` (solution stage 8.5 s), `sorter_ins` (7.3 s), the seq_counter fixture (2.3 s), `fdivp`
(55.4 s) and `fdivp_newton` (53.6 s), each with axioms `propext`, `Classical.choice`, `Quot.sound` only;
`tests/fdivp/shared_sections.py` holds and the reducibility probe passes.

## Static local NBA targets inside `always_ff` remain loud

The timed loop corpus now pins a static block-local variable used as an NBA
target inside a procedural `for` in `always_ff`. The envelope retains the
`LocalDecl` source node and the loop's two NBA updates, while `run2` refuses
the shape by name; this avoids treating Yosys's per-iteration copy as IEEE's
single static variable. `always_ff_static_local_nba_refuse` is a recorded loud
row, with no simulator execution claimed. The phase-2 corpus grows **934 →
935** rows.

## Literal procedural loops inside `always_ff`

The existing literal-bound loop lowering now has a timed sequential witness:
`always_ff_loop` expands the two loop iterations into two nonblocking bit
updates inside the retained `AlwaysPosedge` process. `run2` and Icarus agree
over four clock cycles; parameter-bound and nonliteral loop boundaries remain
on their existing retained or loud paths. The phase-2 corpus grows **933 →
934** rows.

## `Lib/Newton.lean`: Newton-Raphson division, and two `XF.val` lemmas

Two prep commits land unchanged, byte-identical to `svgolf-prep` at
`e0756982`. `d397f120` (2026-11-03) adds `LeanModels/Sv/Lib/Newton.lean`, the
error analysis behind the second fdivp reference: the divider core as the `Nat`
values the hardware computes (`nwR0`, `nwStep`, `nwIter`, `nwQf`, `nwRm`,
`nwQQ`, `nwRnz`), the per-step error bound (`nw_step`, `nw_base`,
`nw_iter_inv`), and `newton_div`: after `K ≥ 1` steps with
`P + 2 ≤ 2^(K+2)`, the corrected quotient is `⌊2^(P+1)·ma / mb⌋` and the
sticky is `2^(P+1)·ma mod mb ≠ 0`, for every `P ≥ 2`. `newton_rest` states the
same against restoring division (`restQuo`, `restRem`), and `nwNI_spec` shows
that `K = $clog2((P + 9) / 8) + 1` qualifies. The commit also adds the import
and a docstring entry to `Lib.lean`. `3d1c1f81` (2026-11-04) adds `XF.val_not`
(the complement `~x` is `2^n - 1 - x`) and `XF.val_shl0` (`{x, 1'b0}` is
`2·x`) to `Lib/XFVal.lean`. Newton's outside imports (`Lib.Restoring`, and
`Param` for `clog2`) are on master, and `Param` is identical to prep. The
build anchor is the root's existing `import LeanModels.Sv.Lib`.

Measured: `XFVal`, `Newton` and `Lib` build in 20 jobs, green (0.6 s, 2.0 s
and 0.3 s). `--dependents` on `Lib.lean` and `Lib/XFVal.lean` is empty: no
chain module imports the library. The root's import set (with
`LeanModels.Python` replaced by its imports minus the five broken on master)
builds in 215 jobs and loads together. `#print axioms` over all 156 theorem
constants of `Newton` (17 in the source, the rest generated equation lemmas):
38 use `propext`, `Classical.choice` and `Quot.sound`, and 118 use `propext`
and `Quot.sound`. `newton_div`, `newton_rest` and `newton_NI` use all three,
and `nwNI_spec`, `val_not` and `val_shl0` use `propext` and `Quot.sound`. No
`sorry`, `admit`, `native_decide` or `bv_decide`. The reducibility probe
passes.

## `sv_exhaustive`: a flat comb netlist by exhaustive kernel evaluation

Three modules land unchanged from the verified prep commits `50f9d4de` to
`5a9c0f9c` (2026-11-03), 7 commits, byte-identical to `svgolf-prep` at
`e0756982`. `CombExhaustive.lean`: a flat summary's sites compiled once, at a
fixed valuation, into a gate program over the bits of one `Nat` (`GE`,
`GSite`, `runG`, `compileNet`, `layout`), with a `case` over literals compiled
to a word-level table lookup. `CombExhaustiveSound.lean`: the compiler and the
run are sound (`Sk.compile_sound`, `runG_sound` under the decided order check
`topoG`), layout disjointness and knownness proved from the construction
(`layout_inj`, `known_of_prog`), input packing (`packIns_spec`) and one output
read off the run (`exh_out`). `CombExhaustiveTactic.lean`: the tactic, which
ranks the sites by depth, compiles once and closes each output by one
`decide +kernel` over all inputs in its own auxiliary theorem, reporting the
first failing input and bit. Every outside import (`CombEqTactic`,
`CombProcEq`, `CombProcTactic`, `ProcNoQualified`) is already on master,
byte-identical to prep.

The tactic's goal is svGolf's task statement: it refines
`SvGolf.CombTask.satisfiedAt_of_comb` (or `_of_lowered`) and unfolds
`SvGolf.HoldAll_cons`, names resolved when it runs, and svGolf is not on
master. So no example on master can run it, and the build anchor is one new
import in the root `LeanModels.lean`, `LeanModels.Sv.CombExhaustiveTactic`,
which pulls in the other two.

Measured: the three modules build in 56 jobs, green (5.1 s, 1.5 s and 2.8 s).
They match the `LeanModels/Sv/Comb*.lean` glob, so they join
`tools/check_sv_chain.sh`'s library group: the full chain build is green, 80
library jobs and 145 Examples jobs. `--dependents` on the three files names
only `CombExhaustiveSound` and `CombExhaustiveTactic`. The root's import set
(with `LeanModels.Python` replaced by its imports minus the five broken on
master) builds in 214 jobs and loads together with the new import.
`#print axioms` over all 123 theorem constants of the three modules (24 in the
source, the rest generated equation lemmas): 13 use `propext`,
`Classical.choice` and `Quot.sound`, 13 use `propext` and `Quot.sound`, 55 use
`propext` only, and 42 use none; `exh_out` and `runG_sound` use all three. No
`sorry`, `admit`, `native_decide` or `bv_decide`. The reducibility probe
passes. No master `LeanModels/Sv` file changed.

## The E route for loop and ordinary `always_comb` bodies

Five modules and one example file land unchanged from the verified prep
commits `f9c39f07` (2026-11-02) to `29643ac1` (2026-11-03), 15 commits. The
files are byte-identical to `svgolf-prep` at `e0756982`. `Loop2E.lean`: the
loop seam over E-core-0, `DenotesE` (one fuel-free `Kernel.execBody` from every
typed store) with its five primitives proved from E's own arms, the fragment
transport `Stmt2.frag_denE`, and `Denotes.toE`, which carries `run2`'s
`Denotes` over to E. `Loop2Slot.lean`: a design whose only process is one
`always_comb`, in E-core-0's slots at a symbolic bound (`SingleE`, `slot`,
`exists_behaves`), with no lowering or rank certificate. `CombFragE.lean`:
ordinary `always_comb` bodies (several writes, defaults, `if`/`else`, plain,
`inside` and qualified `case`) as a state function `Stmt2.sem` under
`Stmt2.combOk`, and `Stmt2.sem_run`, one E activation computes it.
`CombSlotE.lean`: the decidable written-before-read check `combWbr` (a
latch-style body is refused), locality `Stmt2.sem_rel`, idempotence, and
`singleE_comb` and `slot_claimed`. `Loop2Clmul.lean`: the nested clmul body,
declarations and double XOR sum. Every outside import (`Loop2Frag`,
`Kernel.Core0Proc`, `Kernel.Core0Obs`, `XorSum`) is already on master,
byte-identical to prep.

The build anchors are `Examples/system-verilog/loop_nested_clmul/rows_hint.lean`
(the printed `sv_loop_rows` recurrence of the nested clmul, pinned by
`#guard_msgs`), which imports `Loop2Clmul`, and one new import in the root
`LeanModels.lean`, `LeanModels.Sv.CombSlotE`, which pulls in the other three.
The root's comment on `Kernel`/`ObsLib`/`XorSum`/`XMono` drops "Nothing else
imports them": `Loop2Clmul` imports `XorSum`. Two headers keep prep's wording
and name files that are not on master: `Loop2Slot` cites `singleE_frag` in
`LoopTaskE`, and `Loop2Clmul` says the clmul proof is
`svgolf/design/loop/g1/ClmulNested.lean`.

Measured: the five modules build in 42 jobs, green, in 7.5 s, and the anchor
in 0.7 s (44 jobs with `schema.lean`). `CombFragE` and `CombSlotE` match the
`LeanModels/Sv/Comb*.lean` glob, so they join `tools/check_sv_chain.sh`'s
library group: the full chain build is green, 76 library jobs and 145 Examples
jobs, in 254 s. The root's import set (with `LeanModels.Python` replaced by its
imports minus the five broken on master) builds in 185 jobs and loads together
with the new import. `#print axioms` over all 193 theorem constants of the
five modules: 39 use `propext`, `Classical.choice` and `Quot.sound`, 38 use
`propext` and `Quot.sound`, 99 use `propext` only, and 17 use none. No
`sorry`, `admit`, `native_decide` or `bv_decide`. The reducibility probe
passes. No master `LeanModels/Sv` file changed.

## E, the exact semantics: E-core-0/1, the observation interface, and contracts

Twenty-two modules land unchanged from the verified prep history: 39 prep
commits, `0e4aa7a0` (2026-11-02) to `e4a51fbe`. The files are byte-identical to
`svgolf-prep` at `e0756982`. Under `LeanModels/Sv/Kernel/` (root
`Kernel.lean`): E-core-0 for assigns and `always_comb` (`Core0`, `Core0Comb`,
`Core0Proc`), its observation backend and the R-DESIGN2 inclusion into `run2`
(`Core0Obs`, `included_E0_run2`), the window rank (`Core0Win`) with
termination of `combSettle2` on window-acyclic designs (`Core0WinTerm`,
`combSettle2_terminates_win`) and the inclusion over it (`Core0ObsWin`,
`included_E0_run2_win`). It also holds E-core-1's edge fragment (`Core1Edge`,
`exec1_sound`), the clocking discipline (`Core1Disc`,
`clockExpand_disciplined`) and the counter's E-core-1 behaviours (`Core1Obs`).
Under the `ObsLib.lean` root: the observation interface over `run2` (`Observe`,
`ObserveFrame`, `ObserveRedrive`), the cycle machine (`CycleMachine`), the
closed-form clock cycle (`REdgeRun2`), the flat-memory bridge (`FlatMemRun2`)
and module contracts (`Contract`, `compose_safe`, `compose_safe_inv`; the full
adder's in `ContractFA`). Two standalone libraries come with them: the XOR-sum
calculus (`XorSum`) and the width-parametric monotonicity of the 4-state
operator tables (`XMono`). Every outside import (among them `Adequacy`,
`Spec2`, `Mono2`, `Comb2Sound`, `Comb2Proc`, `Comb2Fuel`, `PinAxioms`,
`Core.Outcome`) is already on master, byte-identical to prep.

There is no example to anchor them, so the root `LeanModels.lean` imports
`LeanModels.Sv.Kernel`, `LeanModels.Sv.ObsLib`, `LeanModels.Sv.XorSum` and
`LeanModels.Sv.XMono`. The headers of `Kernel`, `ObsLib`, `XorSum` and `XMono`
keep prep's wording: they say nothing imports them, and `Kernel` and `ObsLib`
say `tools/check_sv_chain.sh`'s library group lists them. On master the root
imports them, and that `check_sv_chain.sh` change is still on prep.

The register gains `sv-div-5` (`docs/sv-declared-divergences.json`), the
declared departure drafted in X1-NOTE §13. E-core-0 refuses a violated
`unique`/`unique0`/`priority` claim inside the activation. IEEE 1800-2023
§12.4.2.1 defers the report and clears it on re-trigger. Its guards
`sv_div_5_still_divergent` and `sv_div_5_has_not_widened` are in
`harness/sv_divergence_probe.py`. `sv-div-4`'s site no longer says E is off
master, and `docs/sv-kernel.md` lists the departure in the declared profile.

Measured: the 22 modules build in 54 jobs, green, in 57 s. `Kernel.Core0`
takes 45 s and every other module under 5 s. The root's import set (with
`LeanModels.Python` replaced by its imports minus the five broken on master:
`PayloadBlind`, `VCTests`, and `VCGen`, `DictCalc`, `GenBound` above them) builds
in 181 jobs and loads together with the four new imports. `#print axioms` over
all 922 theorem constants of the 22 modules: 206 use `propext`,
`Classical.choice` and `Quot.sound`, 268 use `propext` and `Quot.sound`, 245
use `propext` only, and 203 use none. No `sorry`, `admit`, `native_decide` or
`bv_decide`. The reducibility probe passes. No master `LeanModels/Sv` file
changed, so `check_sv_chain.sh --dependents` has nothing to list. The probe
passes with the new guards. Six mutations of a copy of `Kernel/` each turn a
`sv-div-5` guard not-held or unverified: a field added to `Config`, the
refusal deleted, the refusal left only in a comment, a second `12.5.3` refusal
in `Core1Edge`, a stricter `unique0` rule, and the directory removed.

## Loop rows: trip schemas, `sem N`, and `always_comb` statement fuel

Five modules land unchanged from the verified prep commits `b47a2cab`,
`a03c6bb5` and `96ffce9f`, with prep's change to `Comb2Base.lean` from
`b47a2cab`. `Comb2Base.lean`: `Process2.rhsSize` now counts an `always_comb`
body's statement fuel (`Stmt2.combFuelB`, a structural mutual block; the arm
was `0`), so `Design2.combFuel` bounds those bodies too
(`Design2.combFuelB_lt_combFuel`). `Comb2Fuel.lean`: the bound is `Comb2Proc`'s
`Stmt2.fuelB` (`Stmt2.combFuelB_eq_fuelB`) and it is sufficient
(`runCombProcess2_alwaysComb_of_combFuelB`, `_of_combFuel`). `Loop2.lean`: a
procedural `for` as a fold over its `TripSchema`, computed from the header
without fuel, with 32-bit header agreement, `Denotes`, the guard and Bridge S.
`Loop2Rows.lean`: the expression view `valE` and `Denotes.assignSliceE`.
`Loop2Sem.lean`: `sem_single`. `Loop2Frag.lean`: the recursive body recognizer
(`Stmt2.frag_den`, `frag_guard`, `frag_writes`) and the tactics `sv_loop_rows`
and `sv_loop_sem`. Every outside import is already on master, byte-identical
to prep. All of it is provisional over `run2`.

The build anchors are `Examples/system-verilog/loop_edges` (the endpoint
headers) and `Examples/system-verilog/loop_nested_clmul/schema.lean` (the
nested clmul header), and the root `LeanModels.lean` imports
`LeanModels.Sv.Comb2Fuel` and `LeanModels.Sv.Loop2Frag`. That directory's
`rows_hint.lean` needs `XorSum` and lands later. Master's extractor regenerates
both envelopes byte for byte.

Measured: the six modules build in 30 jobs, each in under two seconds, and the
two anchors in 37 jobs, 5.4 s each. Because `Comb2Base.lean` changed, every
module that imports it transitively was rebuilt: 129 modules, the 94 that
`tools/check_sv_chain.sh --dependents LeanModels/Sv/Comb2Base.lean` prints and
35 outside the comb chain (among them `Hier2Gen`, `Lib`, the `Seq*` modules,
`seq_neg` and the `sem2` agreement files). They build in 176 jobs, green, in
282 s. `#print axioms` on 160 theorems (every theorem of the five modules and
the two anchors, plus `Design2.combFuelB_lt_combFuel` and
`combPass2_ok_of_combFuel`) shows only `propext`, `Classical.choice` and
`Quot.sound`. The reducibility probe passes, and `rfl`
computes `Stmt2.combFuelB`. The root's import set loads together with the two
new imports.

## The FF-only clock step, its decidable profile, and negative fixtures

Four modules land unchanged from the verified prep commits `e70c38c0` and
`7c5a536a`. `NbaCommit.lean` holds the NBA commit facts (`nbaStep_comm`,
`commitNba2_perm`). `Seq2Cycle.lean` holds `cycleStep2_ffOnly`: one `run2`
cycle of an FF-only design applies the inputs, runs every process's updates on
that state, and commits once. `SeqFamily.lean` holds the `always_ff` driver
rule (`driversOk_of_ff`) and the packed view (`insFold_eq_packBV`).
`SeqProfile.lean` holds the schedule class `WellFormedClockStep`
(`wellFormed_choose`), `omitted_process` (no conclusion without that class),
the decidable `Design2.ffOnlyProfileB` with its soundness (`FFOnly.ofProfile`,
`upd_covered`, `ffUpd_disj`), and `cycleStep2_profile`. Every import is
already on master. The prep change to `Comb2Base.lean` is not needed and is
not part of this landing.

The build anchor is `Examples/system-verilog/seq_neg/check.lean`. It has five
designs outside the profile, and each one is pinned for its stated reason by
`#guard`: a blocking self-read, an overlap that the loader refuses (pinned by
`#guard_msgs`), a blocking assignment in `always_ff`, an asynchronous reset,
and a cycle through blocking temporaries whose result depends on the schedule.
Master's extractor regenerates all five envelopes byte for byte.

Measured: the four modules and the anchor build in 32 jobs, each module in
under one second and the anchor in 4.4 s. `#print axioms` on all 31 theorems
shows only `propext`, `Classical.choice` and `Quot.sound`. The reducibility
probe passes. The root's 29 Sv imports load together with
`LeanModels.Sv.SeqProfile`. No master Lean file is modified.

## `LeanModels.Sv.Lib`: a word-level proof library

`LeanModels/Sv/Lib.lean` and its four parts land from the verified prep commit
`3c28103a`: `Lib/NatArith.lean` (`Nat` facts: scaled comparisons, products of
powers of two, modular decrements, remainder bands, the top bit of a bounded
value; imports nothing), `Lib/XFVal.lean` (the `Nat` value of the `CombWord`
helpers, in `LeanModels.Sv.XF`), `Lib/RowMajor.lean` (`CombView.rmN` at natural
coordinates) and `Lib/Restoring.lean` (restoring division, `restore_spec`,
`val_restQuo`). 58 declarations, no Mathlib, unchanged from prep. The root
`LeanModels.lean` imports `LeanModels.Sv.Lib`, which is the build anchor.
Measured: the five modules build in 18 jobs, each in under one second.
`#print axioms` on all 56 theorems shows only `propext`, `Classical.choice`
and `Quot.sound`. The reducibility probe passes, and the root's import set
loads together with `LeanModels.Sv.Lib` without name clashes. `lake build
LeanModels` builds 158 of 160 jobs. The two that fail are
`LeanModels.Python.PayloadBlind` and `LeanModels.Python.VCTests`, which
already fail on master CI and do not import this library.
## Partial fixed output wire-array ports

Fixed one-dimensional `output wire` unpacked ports now admit a plain driver on
only some cells. Driven cells retain the existing flat output ports and
undriven cells carry an explicit `z` initializer; duplicate, timed,
strengthened, parameter-dependent, and aggregate forms remain loud.
`partial_output_net_port_array` matches Lean and Icarus over four cycles. The
phase-2 corpus grows **932 → 933** rows.

## Partial fixed unpacked wire arrays

Fixed one-dimensional internal wire arrays may now have a plain continuous
driver on only some cells. Driven cells keep the existing flat net-as-variable
representation; undriven cells are explicit nets initialized to `z`. Duplicate,
timed, strengthened, multi-driver, parameter-dependent, and aggregate forms
remain loud. `partial_unpacked_net_array` matches Lean and Icarus over four
cycles. The phase-2 corpus grows **931 → 932** rows.

## Named structural generate wrappers

Named unconditional wrappers containing only structural generate or instance
items now flatten into the existing `GenerateFor`, `GenerateIf`, and `Instance`
envelope vocabulary. The wrapper path is retained on generated instances, while
wrappers containing declarations, processes, or case-generate arms remain loud.
`named_generate_wrapper_loop` matches Lean and Icarus at `N = 2` and its
cross-check point `N = 3`. The phase-2 corpus grows **930 → 931** rows.

## Instances in loop-dependent generate-if blocks

Generate-for templates now retain a live instance body when the default
genvar iteration takes the generate-if's other branch. The symbolic envelope
keeps the `GenerateIf` condition and the child's `GenvarRef` port connections;
`generate_if_instance_fixed` matches Lean and Icarus at `N = 2` and its
cross-check point `N = 3`. The phase-2 corpus grows **929 → 930** rows.

## Unsized `b0`/`b1` port connections

The instance corpus now pins unbased unsized based literals in input-port
connections. `'b0` and `'b1` widen to the child port's declared width while
retaining their source-shaped `Resize`/`Literal` envelope nodes;
`unsized_port_conn_bits` matches Lean and Icarus for both child instances.
The phase-2 corpus grows **928 → 929** rows.

## Nested dynamic targets in fixed unpacked arrays

Finite one- and two-dimensional integral unpacked-array targets now expand
run-time selectors into mutually exclusive `===` branches over flattened
cells. Constant selectors constrain the selected dimension; unknown and
out-of-range selectors leave the destination unchanged. Dynamic,
parameter-dependent, and aggregate storage remains loud.
`nested_unpacked_dynamic_target` and `nested_unpacked_mixed_target` match Lean
and Icarus over five and three cycles. The phase-2 corpus grows **926 → 928**
rows.

## Nested dynamic reads from fixed unpacked arrays

Finite one- and two-dimensional integral unpacked-array reads now expand all
run-time selectors into mutually exclusive case-equality conditions over the
flattened cells. Mixed constant and dynamic selectors constrain the selected
dimension, while unknown and out-of-range selectors yield `x`. Dynamic,
parameter-dependent, and aggregate storage remains loud.
`nested_unpacked_dynamic_read` and `nested_unpacked_mixed_read` match Lean and
Icarus over six and three cycles. The phase-2 corpus grows **924 → 926** rows.

## Dynamic reads from fixed unpacked arrays

One-dimensional fixed integral unpacked-array reads with a run-time index now
expand to mutually exclusive case-equality conditionals over the flattened
cells. Known indices select one cell; unknown and out-of-range indices yield
the four-state `x` result. Parameter-dependent layouts and nested or dynamic
arrays remain loud. `unpacked_dynamic_read` matches Lean and Icarus over six
cycles. The phase-2 corpus grows **923 → 924** rows.

## Untyped package parameters

The symbolic envelope now retains untyped package parameters and localparams
as qualified 32-bit integer constants. `Param2` already binds this class in
package declaration order; `package_param_untyped` matches Lean and Icarus at
`N = 0`, `1`, and `3`, including X/Z inputs and point cross-checks. Typed
non-integral, parameter-dependent, and package-local storage forms remain
loud. The phase-2 corpus grows **922 → 923** rows.

## Fixed internal wire arrays with complete single drivers

One-dimensional fixed integral internal wire arrays now flatten to
net-as-variable cells when every cell has exactly one plain continuous
driver. Partial, multi-driver, signed, generated, and other net shapes remain
loud. `unpacked_internal_net_fixed` matches Lean and Icarus over three cycles.
The phase-2 corpus grows **921 → 922** rows.

## Fixed output wire-array ports with complete single drivers

One-dimensional fixed integral `output wire` unpacked ports now flatten when
each cell has exactly one untimed, strength-free continuous driver. Partial or
multi-driver output arrays remain loud because they need net resolution.
`unpacked_output_net_port_fixed` matches Lean and Icarus over three cycles.
The phase-2 corpus grows **920 → 921** rows.

## Fixed unpacked input net ports

One-dimensional fixed integral `input wire` unpacked ports now flatten to the
existing scalar cells and reconnect as one source-level array in generated
testbenches. They carry connection values and do not introduce a driver or
resolution rule; output and internal net arrays remain loud.
`unpacked_input_net_port_fixed` matches Lean and Icarus over three cycles. The
phase-2 corpus grows **919 → 920** rows.

## Typed procedural loop iterators

The symbolic loop path now refuses header iterators other than signed 32-bit
`int`/`integer`. Narrow `bit` and `byte` iterators wrap at their declared
widths and can wrap forever, so treating them as unbounded Python integers was
unsound. `loop_typed_iterator_refuse` records the loud boundary. The phase-2
corpus grows **918 → 919** rows.

## Iterator name capture through functions

Retained parameter-bound loops now refuse a user-function call when the
function reads a module or local parameter with the same name as the loop
iterator. This prevents `Param2`'s name-bound iterator from changing a
function's `ParamRef` meaning. `loop_name_capture_refuse` records the loud
boundary. The phase-2 corpus grows **917 → 918** rows.

## Mixed signedness in procedural loop conditions

Procedural symbolic loops now refuse a comparison unless the iterator and
bound are both signed `int`-class expressions. SystemVerilog treats an
unsigned packed bound as an unsigned comparison, so Python-style signed
unrolling was unsound for negative initializers. The literal and parameter
refusal rows match the measured simulator behavior by staying loud. The
phase-2 corpus grows **915 → 917** rows.

## Nested fixed unpacked array ports

Finite one- and multi-dimensional unpacked integral ports now flatten to the
existing scalar port cells, preserving signedness and reconstructing the
source array ranges in generated simulator testbenches. Parameter-dependent,
dynamic, aggregate, and net port shapes remain loud.
`nested_unpacked_port_fixed` matches Lean and Icarus over three cycles. The
phase-2 corpus grows **914 → 915** rows.

## Runtime-indexed fixed unpacked array targets

Procedural writes through a run-time index of a one-dimensional fixed unpacked
integral array now expand to mutually exclusive `===` branches over the
existing flattened cells. Unknown and out-of-range indices perform no write,
matching the four-state target rule; continuous assignments, parameter or
generate-dependent indices, nested arrays, and aggregate shapes remain loud.
`unpacked_dynamic_target` matches Lean and Icarus over four cycles. The
phase-2 corpus grows **913 → 914** rows.

## Fixed signed unpacked array ports

One-dimensional fixed-range unpacked ports of signed packed vectors now
flatten to signed scalar port cells and reconnect as a signed source-level
array in the differential testbench. `signed_unpacked_port_fixed` matches
Lean and Icarus over three cycles; unsupported net, nested, dynamic,
parameter-dependent, and aggregate shapes remain loud. The phase-2 corpus
grows **911 → 912** rows.

## Fixed signed unpacked array variables

Fixed one-dimensional unpacked variables of signed packed elements now flatten
to existing scalar cells with signedness metadata. `signed_unpacked_var_fixed`
matches Lean and Icarus over four cycles; signed unpacked ports, unsupported
nets, and parameter-dependent or aggregate layouts remain loud. The phase-2
corpus grows **910 → 911** rows.

## Fixed integral unpacked array ports

One-dimensional fixed-range unpacked ports of unsigned integral packed vectors
now flatten to existing scalar port cells and reconnect as one source-level SV
array in the differential testbench. `unpacked_port_fixed` matches Lean and
Icarus over three cycles; nested, signed, dynamic, parameter-dependent, and
aggregate port shapes remain loud. The phase-2 corpus grows **909 → 910** rows.

## Fixed concatenations in constant contexts

The symbolic constant evaluator now handles fixed packed concatenations in
parameter and localparam contexts using the existing width-aware constant
representation. `constant_concat` matches Lean and Icarus over two cycles;
signals, x/z literals, replications and reductions remain loud. The phase-2
corpus grows **908 → 909** rows.

## Ref USERFN formal boundary

Added `symbolic_ref_formal_function_refuse`, pinning `ref` formal calls as
loud `CallExpression` refusals. Reference aliasing and copyback ordering remain
outside pure input-only SSA inlining. The phase-2 corpus grows **907 → 908**
rows.

## Non-input USERFN formal boundary

Added `symbolic_output_formal_function_refuse`, pinning output-formal calls as
loud `CallExpression` refusals. Output/inout/ref formals require runtime frame
and copyback semantics; pure input-only SSA inlining remains unchanged. The
phase-2 corpus grows **906 → 907** rows.

## Stateful USERFN call boundary

Added `symbolic_stateful_function_refuse`, which pins a stateful,
multiply-written function as a loud `CallExpression` refusal. The pure SSA
inliner remains source-pure and input-only; runtime call frames and stateful
copyback remain outside the tier. The phase-2 corpus grows **905 → 906** rows.

## Mixed pure-local USERFN chains

The symbolic USERFN path now inlines functions whose source-pure locals mix
declaration initializers with one blocking assignment before the final return.
`symbolic_mixed_local_function` matches Lean/Icarus over four cycles; stateful,
multiply-written, and general call-frame functions remain loud. The phase-2
corpus grows **904 → 905** rows.

## Runtime signal-bound procedural loops remain loud

Added `symbolic_for_signal_bound_refuse`, a phase-2 refusal row for a `for`
condition that reads a runtime signal. The source remains a named
`ForLoopStatement` boundary; parameter-only headers continue through the
retained exact-trip path. The phase-2 corpus grows **903 → 904** rows.

## Reaching parameter-bound `!=` loops

Added `symbolic_parameter_for_ne`, which retains a parameter-bound `for`
header with a reaching `!=` condition and matches Lean/Icarus at `N = 4` with
the parameter cross-check. Non-reaching and effectful forms remain loud. The
phase-2 corpus grows **902 → 903** rows.

## Fixed-width numeric enum methods

The symbolic extractor now lowers enum `first`, `last`, `num`, `next`, and
`prev` calls for fixed-width enums using the existing declaration-order case
tree. `enum_methods_fixed` matches Lean and explicit Verilator over four known
values; Icarus cannot elaborate enum-method system calls, so the row is
`verilator_only` and no Xcelium result is claimed. Point-dependent or unsized
enum members, `name()`, and array methods remain loud. The phase-2 corpus grows
**901 → 902** rows.

## Fixed keyed/default packed assignment patterns

Fixed packed struct assignment patterns with keyed fields or a default field
now reuse the existing `Concat` lowering. `pattern_keyed_fixed` covers both
forms over four known cycles with the explicit opt-in Verilator backend;
Icarus cannot parse keyed/default pattern syntax, so no Icarus or Xcelium result
is claimed. Parameter-dependent, unpacked and effectful patterns remain loud.
The phase-2 corpus grows **900 → 901** rows.

## Fixed packed all-bit 2-state structs

Fixed packed structs made entirely of `bit` fields now reuse the existing
flat-vector storage and `Squash2` assignment boundary. `two_state_struct_fixed`
matches Lean/Icarus over six cycles, including X/Z inputs. Nets, unpacked or
mixed-state aggregates, and parameter-dependent layouts remain loud. The
phase-2 corpus grows **899 → 900** rows.

## Width-changing fixed signed/type casts

Fixed-width scalar and packed typedef casts now reuse the existing signedness
resize nodes. `signed_cast_widen` casts a signed four-bit input to a fixed
signed eight-bit typedef and matches Lean/Icarus over six cycles, including X.
Parameter-named, aggregate, and other unsupported cast shapes remain loud. The
phase-2 corpus grows **898 → 899** rows.

## Width-changing fixed 2-state casts

Fixed-width casts from a four-state integral expression to a 2-state
predefined type now reuse the existing resize and `Squash2` nodes at the
target width. `two_state_cast_widen` covers `byte'(a)` from four bits to eight
over five cycles, including X/Z inputs; Lean and Icarus match. Parameter-named,
aggregate, and other width-changing signed/type casts remain loud. The phase-2
corpus grows **897 → 898** rows.

## Fixed-width symbolic `inside` expressions

The symbolic extractor now lowers fixed-width, non-parameterized `inside`
membership through the existing wildcard-equality and inclusive-range nodes.
The `inside_fixed` phase-2 row covers two scalar items and a range over seven
known cycles. Icarus rejects this source syntax, so the row is verified only
with the explicit opt-in Verilator host backend; `--sim auto` remains the
Xcelium/Icarus path and no Xcelium result is claimed. Parameter-dependent
widths and effectful or unsupported membership forms remain loud. The phase-2
corpus grows **896 → 897** rows.

## Qualified-control Xcelium witness

Added the `xcelium_qualified_ops` phase-2 witness for qualified case/if,
`full_case`/`parallel_case` attributes, and an explicit four-state `2'bxx`
default. It is retained as an `xrun_only` row because Icarus cannot parse
qualified-if syntax. Its Xcelium pin remains pending: the internal Xcelium host was not
reachable and the 26.09 fallback host had no license, so no golden trace
was invented or mixed into the 24.03 pin.

## Module support and loader policy

Added `docs/sv-module-support.md`, documenting the two active envelope
contracts, the current 1,381-envelope split (852 `sv-0.1`, 529 `sv-0.2`), the
supported hierarchy shapes, and the remaining loud module boundaries. The
legacy `sv-0.1` loader remains supported because it is still used by the M0
and timed paths; no deletion or schema rewrite is implied.

## Fixed packed dimension queries

Added the `dim_query_fixed` phase-2 witness for all fixed `[7:4]` packed
dimension queries (`$left`, `$right`, `$low`, `$high`, `$increment`, and
`$size`), including X/Z stimuli. Lean and Icarus match for all three cycles;
moving ranges remain loud.
The phase-2 corpus grows from 870 to 871 rows.

## Fixed-width 2-state declaration

Added the `two_state_fixed` phase-2 witness for a four-bit `bit` input. X/Z
stimulus is squashed to zero at the boundary, including selected reads; Lean
and Icarus match over four cycles. Other 2-state declaration forms remain
loud. The phase-2 corpus grows from 871 to 872 rows.

## Fixed-width signed 2-state declaration

Added `signed_two_state_fixed`, covering a four-bit signed `bit` input, raw
copy, and absolute-value expression with X/Z boundary squashing. Lean and
Icarus match over four cycles; parameter-dependent and aggregate signed forms
remain loud. The phase-2 corpus grows from 872 to 873 rows.

## Scalar logical equivalence

Added `logical_equivalence`, lowering scalar `<->` through existing four-state
logical nodes. Known equal/unequal values and X/Z uncertainty match Lean and
Icarus over six cycles; constant-tier and wider forms remain loud. The phase-2
corpus grows from 873 to 874 rows. Xcelium 24.03 rejects this source syntax at
parse time; its exact diagnostic is recorded as a source-bound unavailable
oracle, so the row remains independently verified by Icarus.

## Symbolic four-state case equality

Fixed the symbolic `!==` instantiation bug and added `case_equality_fixed`.
Exact `===`/`!==` now match Lean and Icarus over six scalar X/Z cycles; other
operators without a `Param2` arm remain loud. The phase-2 corpus grows from
874 to 875 rows.

## Fixed-width unsigned explicit cast

Added `cast_fixed`, admitting literal unsigned sized casts such as `8'(a)`
through the existing symbolic `Resize` node. Parameter-named, signed/type, and
nonintegral casts remain loud. The phase-2 corpus grows from 875 to 876 rows.

## Parameter-dependent packed 2-state port

Added `bit_param_fixed`, covering a parameter-dependent packed `bit` input at
`N = 1`, `4`, and `8`; X/Z boundary squashing and the default-point Icarus
trace agree, with the multi-point cross-check passing. Other 2-state
declaration shapes remain loud. The phase-2 corpus grows from 876 to 877 rows.

## Parameter-dependent signed four-state ports

Added `signed_param_fixed`, `signed_param_fixed_n1`, and
`signed_param_fixed_n8` for signed `logic [N-1:0]` input and output ports.
The symbolic envelope retains declaration signedness, same-width copies, and
signed comparisons; Lean and Icarus match at `N = 1`, `4`, and `8`, with the
point cross-check agreeing. Signed variables and nets, aggregate ports, and
width-changing signed conversions remain loud. The phase-2 corpus grows from
877 to 880 rows.

## Flat signed module variables

Flat scalar and packed four-state `logic signed` variables now use the same
retained signedness metadata as signed ports. `signed_var_fixed` copies a
signed variable and performs a same-width signed comparison; Lean and Icarus
match over four cycles, including X input. Signed nets, aggregate storage, and
width-changing signed conversions remain loud.

## Single-driver signed nets

A flat four-state `wire signed` whose one whole-net continuous driver covers
every bit now reuses the existing N2 variable-equivalent representation while
retaining signedness. The `signed_net_fixed` witness copies the driven net and
performs a same-width signed comparison; Lean and Icarus match over four X/Z
cycles. Undriven, partial, multiple, delayed, strength-qualified and other
signed net shapes remain loud, as do aggregate storage and width-changing
signed conversions.

## Fixed-width four-state signed casts

An equal-width `signed'(a)` cast now preserves the existing expression bits
and carries the target signedness metadata. The `signed_cast_fixed` witness
copies an 8-bit input and performs a signed comparison; Lean and Icarus match
over four X/Z cycles. Parameter-named widths, 2-state casts, and
width-changing signed/type casts remain loud.

## Fixed root-signed packed structs

A fixed, untagged packed struct declared with root signedness now reuses the
existing flat-vector storage and retains that signedness. The
`signed_struct_fixed` witness copies the struct, compares it as a signed
8-bit value, and matches Lean/Icarus over four X/Z cycles. Unpacked or
member-level signed aggregates and width-changing conversions remain loud.

## Fixed flat packed 2-state variables

Fixed scalar and packed `bit` module variables now reuse the existing
`PDecl.twoState` representation. The `two_state_var_fixed` witness copies an
8-bit `logic` input through a `bit [7:0]` temporary; X/Z inputs squash at that
boundary, and Lean/Icarus match over four cycles. Nets, integer and aggregate
2-state declarations, and parameter-dependent locals remain loud.

## Fixed predefined 2-state integer variables

Fixed `int`, `byte`, `shortint`, and `longint` module variables now carry
explicit packed bounds in the symbolic envelope, preserving their declared
width at the Lean boundary. The `int_var_fixed` witness copies a 32-bit logic
input through an `int` temporary; X/Z inputs squash, and Lean/Icarus match over
four cycles. `integer`, 2-state nets, aggregates, and parameter-dependent
integer declarations remain loud.

## Fixed-width 2-state casts

Equal-width casts to predefined 2-state types, such as `byte'(a)`, now use
the existing `Squash2` expression path. The `two_state_cast_fixed` witness
copies an 8-bit logic input through a byte cast; X/Z inputs squash, and
Lean/Icarus match over four cycles. Parameter-named and width-changing casts
remain loud.

## Fixed packed-struct signed members

Signed members of fixed packed structs now retain their member type through
the existing `PartSel` window path. The `signed_member_fixed` witness assigns
an 8-bit signed member and compares it with a signed literal; Lean and Icarus
match over four X/Z cycles. Unpacked or parameter-dependent aggregates and
width-changing signed conversions remain loud.

## Fixed packed assignment patterns

Pure fixed-width packed positional and replicated assignment patterns now use
the existing `Concat` expression path. The `pattern_fixed` witness constructs
an output from input bits and X/Z literals; Lean and Icarus match over four
cycles. Parameter-dependent, keyed/default aggregate, unpacked and effectful
patterns remain loud.

## Scalar package parameters in the symbolic tier

Added `package_param_fixed` and point rows at `N = 1`, `2`, `3`, and `5`.
The sv-0.2 envelope retains scalar `int` package parameters in a qualified
`package_params` table; `Param2` binds those constants before module
parameters, so package references remain source-shaped in packed ranges and
selected bounds. Lean and Icarus match over four X/Z cycles at every point;
package enums, typed non-INT package parameters, and package local state remain
loud. The phase-2 corpus grows from 880 to 884 rows.

## Package enum defaults in the symbolic tier

Added `package_enum_param_fixed`, whose parameter is typed by a package enum
and defaults to a qualified package member. The envelope keeps both the
`TypeRef` and `EnumRef` qualified; Lean binds fixed package enum widths and
members before module parameter defaults, then reuses the same table for
parameterized instantiation. The witness matches Icarus over five four-state
input cycles at the default enum value; typed non-INT package parameters and
package local state remain loud. The phase-2 corpus grows from 884 to 885
rows.

## Fixed-width packed package parameters

The symbolic envelope now retains fixed-width packed integral package
parameters, including `logic [3:0]`, when every bound is a literal. `IEnv`
keeps the package value's width and signedness separately from the existing
32-bit `int` table, so qualified `ParamRef` nodes keep their source identity
through `Param2` expression sizing. `package_param_packed` matches Icarus over
four four-state cycles. Parameter-dependent package widths, package enum
parameters, real/string parameters, and package local state remain loud. The
phase-2 corpus grows from 885 to 886 rows.

## Huge integer literals fail loudly in the extractor

The symbolic extractor now catches Python's decimal digit guard while
materializing an `SVInt`. Very wide constants retain their source bits when
the envelope can represent them; a conversion that requires a decimal Python
integer becomes the recorded `IntegerLiteral:too-large` refusal instead of
raising `ValueError: Exceeds the limit (4300 digits ...)` and aborting the
whole extraction. The regression covers a 20,000-bit literal and the guard
helper.

## Retained procedural local-declaration boundary

The sv-0.2 loader now parses residual `LocalDecl` statements into the existing
`PStmt.unsupported` form. Automatic and other scoped locals therefore load as
source-shaped loud boundaries instead of rejecting the entire envelope with an
unknown JSON statement kind. Static flat locals in module-level `always_comb`
remain covered by the existing hoisting path; `proc_local_automatic` records
the retained refusal.

Tooling only. `tools/triad.sh --classify` built just the touched module for
an Sv file: the tier has no root module to bring its dependents along, so a
core-file change built nothing that imports it, and that is how `CombProc.lean`
broke twice on 2026-11-01. `tools/check_sv_chain.sh --dependents PATH...` now
prints the chain modules that transitively import the given `LeanModels/Sv`
files, from the import lines and with no Lean, through non-Comb modules, other
tiers and `sem2/`. `triad.sh` adds them to the landing's one `lake build`, where
`Param.lean` reaches **79** of the **98** chain modules and `Semantics.lean`
**93**. It reads the classified tree, runs once per landing and not at all when
the landing is already a full build; a probe with no answer widens to the full
build. Other landings build exactly what they did. A dependent that is neither
in the chain nor imported by it is still built only by hosted CI. No build has
run with this yet.
# [unreleased] — 2026-11-03 (sv_comb: word-level `*`; `$clog2` localparams)

Proof tactics: the PRODUCT `*` is read in the `assign` chain and in the leaves of an `always_comb` tree, at the
context-determined positions, exactly as `+` (register `tl-sv-structure-fragment`): `*` joins `ctxOpW`, the factors are
read by `rdsOfW?` (bare, under slang's `Resize` marker, operations of the fragment), extended to the CONTEXT width before
the product, and a marker around a product is a truncation (`.rsz true`). One difference with `+`: `instExpr2` lowers `*`
only after `evalInt` of the product FAILS (a product of constants is folded), so the recognizer asks for one factor that
is a signal access, bare or under the `Resize` marker (`sigOpd`, `mulOk`; otherwise the refusal `a product neither of whose
factors is a signal access`), and `evalAt_sigOpd` / `evalInt_mul_sig` prove the evaluation fails on such a product at every
type, which gives the `+`-shaped instance lemmas `ie_mul_cases`, `instExpr2_mul`, `ie_mul_none`. Signed factors are refused
as before (a signed declaration by `declOf?`, a `SignedResize` marker by the leaf reader). Skeleton: `Sk.mul l r`, the
arms of `Sk.add` copied (bit `XF.mulBits tw … tw …`, the evaluator's `LVec.mul`), one new arm in each of `skT_shapeC`,
`low_xf_genC`, `inst_rdW`, `inst_idxFreeW`. Glue (`CombWord`): `XF.bv_mulBits` (the equation is `BitVec` `*`),
`XF.val_mulBits` (the value of a product in `Nat`: `val fa wa * val fb wb % 2 ^ w`), `XF.mulBits_congr`. `sv_equations`
prints a product as `XF.mulBits W f W g k`, the form `+` prints.

LOCALPARAMS: `$clog2(e)` is a localparam constructor (`CE.clog2`, `CE.eval` = `LeanModels.Sv.clog2` of the argument's
`toNat`, the elaborator's own operation), so `localparam integer NI = $clog2((P + 9) / 8) + 1;` is read; `hag` and `h1`
still close by `rfl` at symbolic parameters (the argument is an `Int.ofNat` there, so `evalInt`'s negativity test reduces).
Downstream the value is an opaque atom of the obligations (`↑(clog2 n)`), a non-negative unknown for `omega`, which is
enough for widths, generate bounds and the linear obligations; the one fact the generate-fuel obligation `auto_k` of a loop
it bounds needs is `clog2_le` (`clog2 n ≤ n`), with `le_two_pow_clog2` (`n ≤ 2 ^ clog2 n`). A `$clog2` under a 2-state
`int` (`Squash2`) stays refused, now with its own message (`paramEnv2` does not evaluate the squash at a symbolic
parameter). Examples `comb_word/mul_word` (`mul_word_correct`: `p = x * y` into `N` bits, `q` the exact `2N`-bit product,
`mul_full`), `comb_word/sq_chain` (`sq_chain_correct`: `L = $clog2(N) + 1` squarings, `y = x ^ (2 ^ L) mod 2 ^ N`, a
generate loop bounded by a `$clog2` localparam), the negative `neg_mul_op`; `neg_mul` is accepted; the `mul_word`
equations pinned verbatim in `comb_hint`. The 80 `LeanModels.Sv` modules and the 546 SV Example modules build (all of
them re-elaborate: the new envelopes change the `svEnvelopes` trace; 16 minutes on two threads); `mul_proof` 19 s. A
design with the run-time `*` of a Newton-Raphson divider and its `$clog2` step count (`NI = $clog2((P + 9) / 8) + 1`, a
loop of four sites over `k < NI`) is read whole: `sv_structure?` and `sv_equations?` print its 45 sites at symbolic
parameters with no refusal.

# [unreleased] — 2026-11-02 (WP-B2, gate 4c: replication `{N{x}}`)

Proof tactics: a REPLICATION of a sized literal or of ONE bit select or part select (never a whole signal), with a count that is
affine in the parameters and genvars, is read in the `assign` chain, as a part of a concatenation (zero padding
`{ {K{1'b0}}, x }`) or as a whole right-hand side or an operand of a word-level operator (the AND mask `a & {N{b[i]}}`,
`{4{x[1:0]}}`); register `tl-sv-structure-fragment`. slang writes the braces of `{K{1'b0}}` as a ONE-PART `Concat`
(`Repl{count, operand: Concat[Literal]}`), which the recognizer reads through (`repArgRd?`: `.concat [.lit _]` or
`.concat [e]` with `e` one access; several parts, a whole signal (`notWhole`), a non-affine count and an operation are
refused, each with its own message). Skeleton: `Part.replit (c : Aff) (v : LVec)` and `Part.reprd (c : Aff) (a : Acc)` as
parts of a concatenation (width `c * w`, bit `k % w`, expression `.repl n (.concat #[…])`) and `Sk.rep (p : Part)` as an operand
(the arms of `.cat`, copied by a script); `partsT`/`skT` build them (`repAff c`, the count's `Aff`), `pcnt`/`cnt` count a
replicated literal as 0 reads and a replicated access as 1, and `partKnown` checks that a replicated access is not a whole
signal (the x-free layer reads the access's own window width). The v1 part recognizers `partRd?`/`partsRd?` are untouched
(a replication in a self-determined position, `|{4{a[0]}}`, keeps its v1 refusal): `rdsOfW?` uses new `partRdW?`/`partsRdW?`,
and `partsT_of_ne` gained a hypothesis. The count is a constant of the instance like a genvar shift amount (gate 4b): its
names are in `PExpr.cnames` (the fourth `StructOk` conjunct, unchanged) and its NON-NEGATIVITY is a new conjunct of
`InRangeObl`, guarded like `more` (`if ∀ b ∈ s.lsites, b.site.rcounts = [] then True else …`); `TSite` has two new fields
`cnames`/`rcounts` (stored by the recognizer, read by projection like `more`); `ConstOK σ ns v` (names in scope, counts non-negative)
replaces the hypothesis `hcn` of the gate 4b theorems; `site_co`/`SiteCtx.cn` deliver it per located site; `InRangeObl.rc_all`
extracts the counts; `inRangeObl_of_plain`'s premise `hp` (the one traversal of the sites it already makes) also says `rcounts = []` (a flat netlist with a replication takes the normalization route). The proc chain refuses a replication in an `always_comb` leaf (`fragOkL v = fragOk v && noConst v`, one traversal: `noConst_spec` gives `cnames = []` and `rcounts = []`;
the readers' index-freedom lemmas gained the replication arms `inst_repRd_idxFree`, `inst_parts_idxFreeW`). The replication vocabulary (`PExpr.rcounts`, `repCount`, `repAff`, `affOf?`, `affBin`, `affMul`, `List.isEmpty_nil/cons`) is passed to `simp`
only for a design that contains a replication (`Summary.hasRepl`; `replSimpLemmas`, `withRepl` in the three tactic files), NOT named in the six simp
lists: naming it there measured +2 % to +3.5 % on every proof (a name costs about 21 thousand heartbeats per `simp only` call, a proof makes about a
hundred calls). `LVec.width_mk_toArray` was not added to the equation lists (it changes the pinned `cat_add` hint), so a replicated multi-bit literal
prints its width unevaluated. Examples `comb_word/repl_pad` (`repl_pad_correct`: `y = x.setWidth (N + K)` for every `N ≥ 1` and every `K ≥ 0`),
`repl_mask` (`repl_mask_correct`: row `i` of `a & {N{b[i]}}` is `if b.getLsbD i then a else 0#N`, bit by bit and known),
`repl_bits` (`repl_bits_correct`: `{4{x[1:0]}}` is `BitVec.replicate 4 (x.extractLsb' 0 2)`), the equations pinned verbatim in
`comb_hint`, and the negatives `neg_repl_whole`, `neg_repl_nonaffine`, `neg_repl_op`, `neg_repl_selfdet`, `neg_repl_leaf`.
Rows `wl_repl_n1k0/n1k2/n2k1/n3k3/n4k3/n8k5` (736 cycles: `{ {K{1'b0}}, a }` with K = 0 (the empty replication) and K > 0, `a & {N{b[i]}}`, `{4{x[1:0]}}`,
`{x[0], {4{2'b10}}, x[3:2]}`, `{N{b[0]}}`, x/z in every position) pinned on Xcelium 24.03-s004: 6 of 6 XREF-MATCH.
Heartbeats against the gate 4b table: every measured theorem between -0.1 % and +0.5 %, except `sbox_bp` `bp_struct` (+1.5 %), `ps_rot_correct`
(+1.3 %) and `sbox_bp` `bp_interface` (+0.8 %); `sbox_table` `tbl_struct` 45 880 (+1.3 % over the gate 3b base 45 297), `solution` 190 866
(margin 4.6 % under the default limit); `repl_pad_correct` 95 840, `repl_mask_correct` 124 736, `repl_bits_correct` 58 662. (The first build, which named the
replication vocabulary in the simp lists and traversed every leaf twice, was +2 % to +3.5 % everywhere: see the G26 note, section 14b.) The 24 goal
dumps are identical to those of gates 3b to 4b. The 51 Example modules that import the comb tactics build. The clmul styles of
`svgolf/tests/clmul/attacks`, first wall of each after this gate: `gen_mask_replication` is read by `sv_structure` and `sv_equations` (only the
proof is missing); `gen_word_pp_chain`: the fill `'0` as an arm of `?:`; `gen_pp_zerofill` and `gen_always_step`: the generate-for header (start `N`,
bound `<=`); `gen_size_cast`: a size cast as the left operand of a shift. Axiom pins that moved with the proofs (standard axioms): `siteOf?_proc'`,
`siteOfP?_proc`, `siteOfP?_proc'` (+`Quot.sound`), `coverObl_of_plain` (+`propext`).

# [unreleased] — 2026-11-01 (WP-B2, gate 4b: a genvar as the amount of a shift; constants of the instance)

Proof tactics: `a << i` and `a >> i` with a bare GENVAR as the amount are read in the `assign` chain (register
`tl-sv-structure-fragment`). The amount is a constant of the instance: `instDivOperand2` lowers it like an unsized constant,
to the 32-bit literal of its value, so the skeleton gets one new node `Sk.cref (a : Aff)` (32 bits wide, reads nothing, value
`a.eval σ`; `skT (.genvarRef g) = .cref (Aff.var g)`, `cnt (.genvarRef _) = 0`), a twin of `Sk.const` whose arms were copied
mechanically (the x-free layer reuses `xf_lit_ofInt`); the recognizer reads it through `shAmtRd?` (a genvar, else `shOpdRd?`),
used for the AMOUNT only, so the left-operand machinery is untouched. Prerequisite R (the scope of a constant, design delta 12.3):
a constant is not an access, so nothing said it is bound where the site is instantiated. `PExpr.cnames` collects the genvars
named as shift amounts, `TSite.cnames` is the plain site's (derived from `proc`, no new field) and is APPENDED to `TSite.affNames`:
the fourth conjunct of `StructOk` and its message (`an index or a shift amount mentions n, which is neither a parameter nor an
enclosing loop variable`) cover it, with no new conjunct; `site_cn` and the `SiteCtx` field `cn` deliver it per located site; the
word-level theorems take the hypothesis `hcn : ∀ n ∈ v.cnames, n ∈ ns` (`inst_rdW`, `rhs_ok`, `site_desc`, `skT_shapeC`, `gate_shapeC`,
`rhs_shapeC`, `proc_shapeC`; the amount lemmas `rd_shAmt`, `shAmt_shape`, `shAmt_len`, `shAmt_leaves`, `idxFree_shAmt`). No v1 theorem
statement changed; the two proofs that unfold `TSite.affNames` (`siteCtx_of_reach`, `site_ok`) gained one `Or.inl`. The always_comb chain keeps its fragment: a
leaf that names a constant of the instance is refused (`fragOkL`: `fragOk` and no `cnames`), so `PTR.Ok`/`PLfR.Ok` carry it and the
proc theorems discharge `hcn` from it. Merge fix: the new `PStmt.forLoop` of the off-prem lane gets refusal arms in `treeStmt?`,
`armLeaf?`, `ovrStmt?` and their inversions. Example `comb_word/shl_gen` (`pp[i] = aw << i` over `2N`-bit rows: structure, the
equation `… XF.shlBits (XF.zext W …) 32 (fun x => XF.constBit ↑i 32 x) k` pinned verbatim, `shl_gen_correct`: row `i` is `x <<< i` bit by
bit and known, for `N ≤ 2^32` (the amount is 32 bits wide, a genvar of `2^32` or more wraps), glue `toNat_ofInt32_nat`) and the negative
`neg_shift_gv` (`a << (i + 1)`, stage 4d). Rows `wl_shl_gen_n1/n2/n3/n4/n8` (680 cycles: `aw << i`, a narrower operand zero-extended before the
shift, `aw >> i`, x/z in every position) pinned on Xcelium 24.03-s004: 5 of 5 XREF-MATCH. Not read: an expression amount (`i + 1`, `N - 1`:
`Sk.cbin`, stage 4d), a parameter or localparam amount (its width is a fact about the declared type that the summary does not carry), a
genvar amount in an `always_comb` leaf. The clmul styles of `svgolf/tests/clmul/attacks`, first wall of each: replication
(`gen_word_pp_chain`, `gen_mask_replication`, `gen_always_step`; stage 4c), a size cast as the left operand of a shift (`gen_size_cast`),
a generate-for starting at `N` (`gen_pp_zerofill`). Heartbeats against the gate 4a table: every measured theorem between -0.2 % and +0.7 %,
except `sbox_table` `tbl_struct` (+1.4 %, +614 heartbeats of 45 297) whose `solution` is 190 807 (+0.4 %, margin 4.6 % under the default
limit); `shl_gen_correct` 84 388. The 24 goal dumps are identical to those of gates 3b and 4a. The 51 Example modules that import the comb tactics build.

# [unreleased] — 2026-11-02 (WP-LIN: the sv_comb tactics on a design with many sites)

Proof tactics: `sv_structure` and `sv_equations` no longer cost a quadratic number of heartbeats in the number of sites on a
design that is not a flat netlist (a parameter or a generate loop). Diagnosis (synthetic chains of 11 / 21 / 41 plain sites,
`design/fdiv-param/h3/chain`, `set_option sv_comb.profile true` per obligation, thousands of heartbeats): `auto`, `inRange`, `width`,
`bitRead`, `inputsKnown` are linear (about 0.9 million per site per obligation); `driverDisjoint` 16 187 / 45 372 / 161 430 and
`rankDecreases` 35 726 / 112 829 / 403 666 are quadratic (`DisjObl` states `DisjOne` for every PAIR of sites and normalizes each; `RankObl'`
filters ALL sites for the writers of every read), and `cover` (`SrcS`: for every bit a read observes, a source among ALL sites) 52 400 /
146 153 / 257 619, the last point already out of `simp` steps with the goals in the site-witness form. Only sites that write the SAME
signal can fail to be disjoint, be ranked, or be a source (two windows of different signals never overlap). Fix: the three obligations are
first restricted to the related sites. The tactic lists them natively, from the names, without `simp` (`groupStructureGoal`,
`groupCoverGoal`, `rdWritersExpr`, in `CombViewTactic.lean`/`CombEqTactic.lean`), and assigns a lemma whose hypothesis `rdWriters s.lsites = RW`
(`sameNamePairs s.lsites = P`) is checked once by the kernel with `rfl`: `Summary.disjObl_of_groups`, `Summary.rankObl'_of_groups`
(`CombViewGroup.lean`), `Summary.coverObl_of_groups` (`CombEqGroup.lean`), each the ORIGINAL obligation asked on the listed sites only, with the
original quantifier nesting (a flat list of triples was three times cheaper for the rank but kept a duplicate conjunct where a site reads
one bit twice, and changed `ripple_add/neg`'s goal list). The goals that come out are the same ones in the same order; if the listing fails, or the
design has fewer than four sites (a design of one site paid 1.6 to 4.4 million heartbeats for nothing), the original goal is normalized as before.
No simp list gained a name; the flat fast path (`closeByDecide`) is untouched. `set_option sv_comb.profile true` logs the heartbeats of each
obligation. Measured: chains of 11 / 21 / 41 sites, structure 78 346 / 206 063 / 670 702 to 50 745 / 87 952 / 174 056 thousand heartbeats, equations 112 577 / 245 160 /
437 995 to 86 639 / 144 398 / 284 163 (cover 52 400 / 146 153 / 257 619 to 27 534 / 49 479 / 102 774); the 90-site divider candidate `fdivp2.sv`, which did not finish
structure at 4M or equations at 3M, finishes both (625 653 and 792 333 thousand). Against a fresh tip baseline: the 24 dumps are byte-identical to the WP-COV run's, `sbox_bp` and `sbox_table`
are unchanged to the thousand (`tbl_struct` 45 325 to 45 326), and `add_*`, `mul_*` and the examples of four or more sites are 11% to 35% cheaper (`mul_tree` struct 797 221 to 310 506).
Examples that exercise the route, the Karatsuba cover pin included, build (every module of `tools/check_sv_chain.sh --list`). Follow-up: the cover of a body of several windows (`CoverOblM`, `CombProcGroup.lean`) is grouped too (13-site multi-target design: `sv_equations` 398 335 to 254 647 thousand heartbeats, 66 558 lines of output to 49; the guarded conjuncts of the structure stay quadratic), `set_option sv_comb.group_report true` reports the size of each grouped list, and `Examples/system-verilog/comb_lin` (nine plain sites, two windows per vector, plus `add_proc_m`) pins those reports at default heartbeats, so a drift of a grouping lemma fails the build. Retraction: the earlier note that `comb_case`, `comb_word`, `comb_proc` fail at the tip was stale oleans of the build tree (they build; the dumps are identical to the WP-COV ones).
Examples: `comb_lin/chain.lean` (the chains of the diagnosis are `svgolf/design/fdiv-param/h3`); `G25-NOTE` section 14.
# [0.1.423] — 2026-11-02 (symbolic `casez` and `casex`)

The symbolic envelope now retains unqualified integral `casez` and `casex`
matching modes on its `Case` node. Instantiation uses the shared symmetric
four-state matcher: `casez` ignores Z on either operand, while `casex` ignores
X and Z. `symbolic_casez_casex` MATCHes Icarus over six X/Z input cycles;
qualified, range/pattern and effectful case forms remain loud. The phase-2
corpus grows **815 → 816** rows.

# [0.1.424] — 2026-11-02 (symbolic qualified cases)

The symbolic case path now has a simulator-backed witness for `unique`,
`unique0`, and `priority` qualifiers. `CaseCheck` remains retained metadata;
the structure-preserving evaluator keeps source-order first-match behavior,
and the public `run2` path returns a named loud `CaseCheck:*` result whenever
the settled state violates the qualifier. The phase-2 corpus grows **816 →
818** rows, including the paired violation refusal.

# [0.1.425] — 2026-11-02 (initial-process parser loudness)

sv-0.2 envelopes now retain `Initial` as the named unsupported process
`ProceduralBlockSymbol:Initial`, so parser errors no longer hide the semantic
boundary. Initial execution remains loud and outside the current tier.

# [0.1.420] — 2026-11-02 (nested parameter-bound procedural loops)

The symbolic extractor now retains an admitted parameter-bound `for` nested
inside another retained loop when its condition reads the outer iterator. The
inner condition carries that iterator as a `GenvarRef`, so `Param2` derives its
trip list per outer trip after parameter binding; the source `LocalDecl` is
erased with the header. `symbolic_nested_parameter_for` MATCHes Icarus at
`N = 5` with an agreeing point cross-check, and the phase-2 corpus grows
**807 → 808** rows.

# [0.1.421] — 2026-11-02 (parameter-loop boundary matrix)

The loop differential corpus now exercises `N = 0`, `1`, `126`, and `127` on
the 200-trip parameter family, plus nested iterator shadowing in default and
retained forms. All six rows MATCH Icarus; the four parameter rows pass their
point cross-checks. The Xcelium backend is present but its local license
checkout failed during this run, so no Xcelium agreement is claimed here.
The phase-2 corpus grows **808 → 814** rows.

# [0.1.422] — 2026-11-02 (parameter-loop header shapes)

`symbolic_parameter_for_header_shapes` adds a simulator-backed parameter-loop
witness for inclusive `<=`, descending `>=` with `-=`, and positive `+=`
stride headers. It MATCHes Icarus at `N = 5` with an agreeing cross-check at
`N = 3`, `5`, and `8`; the Xcelium command was unavailable because of local
license checkout failure. The phase-2 corpus grows **814 → 815** rows.

# [0.1.419] — 2026-11-02 (selected continuous bit targets)

The timed scheduler now admits a continuous assignment to one literal packed
bit. Its driver contributes `z` on unselected bits, so it composes with the
existing per-bit net resolver instead of becoming a procedural whole-net
write. Dynamic and ranged continuous targets remain loud. The new
`assign_selected_target_accept` witness matches Icarus (`Y=z0`, `Y=z1`), while
the dynamic-target refusal remains recorded.

# [0.1.418] — 2026-11-02 (fuel-free parameter loops)

`Param2.forValues2` now derives exact structural fuel from the instantiated
linear comparison and step instead of passing the fixed 128 budget. Retained
and parameter-bound loops with 200 trips now instantiate and run; malformed,
non-monotone, and non-reaching `!=` headers remain loud. The new
`symbolic_parameter_for_large` row MATCHes Icarus with `xcheck:agree`, and the
phase-2 corpus grows **806 → 807** rows.

# [0.1.417] — 2026-11-02 (retained literal procedural loops)

`extract.py --retain-loops` now keeps an admitted literal-bound procedural
`for` as the same symbolic `For` node used for parameter-bound loops. The
default remains unrolled, and `proc_loop_forms_retained` differentially matches
the unrolled source over four cycles. The phase-2 corpus grows **805 → 806**;
the parameter-point loop fuel is derived structurally in `Param2.forValues2`.

# [0.1.416] — 2026-11-02 (fixed-width one-hot predicates)

The symbolic tier now lowers fixed-width four-state `$onehot` and `$onehot0`
queries by counting definite one bits with case equality. X/Z bits are ignored
as in the existing bit-query semantics; parameter-varying widths and aggregate
arguments remain loud. `onehot_fixed` MATCHes Icarus over six X/Z stimulus
cycles, and the phase-2 corpus grows **804 → 805** rows.

# [0.1.415] — 2026-11-02 (regression guards)

Elaborated let expressions that expose an unmodelled subroutine formal now
retain the `CallExpression` refusal instead of leaking a
`NamedValueExpression:FormalArgument` implementation detail. The unavailable
Icarus-oracle regression guard now tracks all **25** recorded cases.

# [0.1.414] — 2026-11-02 (fixed-width `$countones`)

`$countones` now lowers for fixed-width four-state packed signals by summing
case-equality tests of their bits; X/Z bits contribute zero. Parameter-varying
widths, `$onehot` variants, and aggregate methods remain loud.
`countones_fixed` MATCHes Icarus over four cycles with X/Z stimulus. The
phase-2 corpus grows **803 → 804** rows.

# [0.1.413] — 2026-11-02 (WP-PROC X1: parameter-bound external iterators)

The symbolic loop lowering now retains a source-pure Verilog-2001 `for` with
an external `integer` iterator and a parameter-valued bound. The iterator is
erased when its references are confined to the loop, and `Param2` expands the
header at each parameter point. `symbolic_parameter_for_external` MATCHes
Icarus over four cycles with an agreeing point cross-check. The phase-2 corpus
grows **802 → 803** rows.

# [0.1.412] — 2026-11-02 (WP-PROC L1: closed block-local initializers)

Static block-local declarations in module-level `always_comb` bodies now keep
a closed literal, fill, parameter, or enum initializer when the declaration is
hoisted to module storage. The initializer therefore runs with the ordinary
startup width and four-state conversion; runtime reads, calls, timing,
automatic locals, aggregates, and generate-scope locals remain loud. The
`proc_local_initializer` and `proc_local_initializer_param` witnesses add
four-cycle Icarus MATCHes; the latter exercises the parameter-point
cross-check. The phase-2 corpus grows **800 → 802** rows.

# [0.1.411] — 2026-11-01 (WP-COV: coverage goals left in the site-witness form)

Proof tactics: `sv_equations` no longer leaves the coverage goals of a design with generate loops in the site-witness form
`∃ b, (b = site₀ ∨ …) ∧ Q b`. Diagnosis (staged one-level Karatsuba clmul, 19 sites, 26 operand reads): the whole coverage
obligation is normalized by ONE `repeat (sv_eq_norm; try sv_simp)` before it is split into goals, and on the larger design that
`sv_simp` fails with `simp failed: maximum number of steps exceeded` (100000), `try` swallows it, and the loop stops (the next
`sv_eq_norm` has nothing to do), so the goals keep the form `sv_eq_norm`'s own list leaves; the form depends on reads times sites of the
whole obligation (13 and 16 sites with 20 reads came out explicit, 26 reads did not). `omega` on a goal that contains `∃ b : LSite`
logs `failed to synthesize OfNat LSite 0` instead of failing, so `first | (intros; omega) | sv_cover` never reached `sv_cover`, and
`sv_cover`'s own last alternative is `omega`. Fix: after the split, a coverage goal that still has an existential over `LSite` is
renormalized on its own (`sv_cover_renorm`, `svL_cover_renorm`, `svL_cover_renorm_multi`: `sv_simp` first, then the loop); the
goals then come out explicit and the existing 2-D rule closes them (all 17 of the Karatsuba design, no case split). Only a design with
a generate loop takes it: a flat design with a parameter (`flat_net_p`) keeps the site form and the site route. No simp list gained a
name. The 24 dumps are byte-identical, heartbeats within +0.1% of the tip before the change (`sbox_bp` `solution` exact).
Examples: `comb_karatsuba/cover.lean` (`k1u_covers`). svGolf: `design/tasks-week2/clmul/karatsuba/G3h.lean` compiles whole;
`G25-NOTE` section 13.

# [0.1.410] — 2026-11-01 (WP-PROC follow-up 1: a drive strength on a continuous assignment is refused)

Extractor, symbolic tier (register row `st-cont-strength`, new; principle P-SAME-PROGRAM). Found while writing N2:
`_continuous_assignment_has_strength` reads source bytes that only the M0 path loads, so `assign (strong0, highz1) y = a;` on a
`logic y` was extracted as a plain assignment. Measured 2026-11-01 (rows `cstr_highz`, `cstr_weak`): Icarus 12 applies the strength (a
highz term drives z: y = 0 z x z 0 z at a = 0 1 x z 0 1), Xcelium 24.03-s004 ignores it on a variable (`*W,CAVSTR`, y = a), Yosys 0.53
cannot read a strength on `assign` at all (syntax error: no scored netlist) and Verilator 5.042 stops on `highz` (a strength without
a high-impedance term it accepts and ignores). So the earlier statement "the model reads 1 where Icarus reads z" was half the
picture: the model's reading was Xcelium's, Icarus's differs, and the pipeline could not have scored it; what was wrong is that
the text was admitted at all. `convert_continuous_assign` now refuses every strength-qualified `assign` in symbolic mode
(`ContinuousAssignSymbol:strength`, decided from the syntax tree, `lower_proc.has_strength`, also in generate scopes); the M0 path
keeps its own handling. A net with a strength was already refused (`NetSymbol:net-z`, N2). Nothing in the surveyed corpora (216 real
files, 82 RB0 blocks, 240 probes) writes a strength. Tests `test_continuous_strength.py` (5), two loud-refusal rows, register row.

# [0.1.409] — 2026-11-01 (WP-PROC, G1 N2: nets with one continuous driver)

Extractor, symbolic tier (register `dc-net-z`; contract `docs/sv-proc-lowering.md` N2). A plain `wire`, `output wire`, implicit-type
`output` or implicit net whose every bit has EXACTLY ONE continuous driver (slang's driver table) and no strength or delay is
declared as the variable that driver assigns (`Var`, or an `out` `Port`; `net_as_variable`); a declaration assignment `wire [w] x = e;`
is the process `assign x = e;` at the declaration's position. The decision is point independent: either one driver that is the whole
net by its source text (whatever the width), or literal windows that tile a literal-width net. Undriven or partly driven nets
(z), two drivers (resolution), a driver in a generate scope, a strength or delay, nets in generate scopes, other net types and
2-state/signed nets keep `NetSymbol:net-z` / `PortSymbol:net-z`. The loud rows `net_width_outwire`, `net_width_outwire1`,
`acg_alias_wire` now reach their Lean guards (`net_width_outwire` and `net_width_outwire1`: `PortConn:net-width`, the guard their comments called intended, shown to fire; `acg_alias_wire`: `AlwaysComb:alias-read`, as its text predicted; diff_test2 run, rows and example comments updated; `net_z_*` and `vg_initn` stay refused as before). One pinned test changes (`test_sym_initializers`: `wire [39:0] w =
'hz1` is the variable and the assignment, the z literal extended with z). Rows `proc_net`, `proc_net_param_n3/n4/n8`: 4 of 4 PASS vs Icarus, 4 of 4 XREF-MATCH against Xcelium 24.03-s004.
Finding, not changed here: in symbolic mode `_continuous_assignment_has_strength` reads the source bytes only the M0 path loads, so
`assign (strong0, highz1) y = a;` on a `logic y` is an ordinary assignment in the envelope while Icarus 12 reads z where a = 1; N2
reads the strength from the syntax tree for nets.

# [0.1.408] — 2026-11-01 (WP-PROC, G1 E1: `always @*` and level-sensitive lists)

Extractor, symbolic tier (registers `pr-implicit-event`, `pr-event-list`; contract `docs/sv-proc-lowering.md` E1). `always @*`,
`always @(*)`, `always @(a or b)`, `always @(a, b)` and `always @a` are converted as `always_comb` (node `AlwaysComb`,
`always_star_lowered`) when six rules hold, decided on the converted body and on slang's symbols: R1 shape (no edge, `iff`, delay,
nonblocking, nested control), R2 an explicit list names every read (selects refused), R3 a 4-state input exists and no 2-state input
(an `@*` block does not run at time zero), R4 no called function reads a module signal it is not given, R5 every target is fully
assigned on every path and no window is read before its assignment (no latch; bit-window coverage for literal-width targets, so
the windows an unrolled loop writes count), R6 no other process writes a target (slang's driver table). A failing block keeps its
old `Unsupported` tag with the rule in the text. The register's prerequisite ("a 4-state rule for the initial x of a level-sensitive
block in score/fourstate.py") is R3, enforced in the extractor. Rows `proc_star`, `proc_star_param_n3/n4/n8` (x/z stimulus applied
at time 0 of the testbench): 4 of 4 PASS vs Icarus, 4 of 4 XREF-MATCH against Xcelium 24.03-s004 (the model equals Xcelium cycle for cycle, the time-zero stimulus included; the probe-point cross-check agrees).

# [0.1.407] — 2026-11-01 (WP-PROC, G1 L1: block-local declarations)

Extractor, symbolic tier (register `ld-localdecl`). A static block-local variable of a module-level `always_comb` body
(`always_comb begin logic [7:0] t; ... end`, named and nested blocks, locals of an unrolled loop body) is hoisted to a module `Var`
and every reference is renamed BY SYMBOL (`<block label>__<name>`, unique among the module's names), so the Lean loader, which has no
`LocalDecl` statement and refused the whole envelope, reads a design it already knew. Refused (the `LocalDecl` stays loud): an
initializer, an automatic variable, a type `convert_var_sym` does not take, a multi-dimensional or unpacked local, generate-scope
blocks, other processes. Rows `proc_local`, `proc_local_param_n3/n4/n8`: 4 of 4 PASS vs Icarus, 4 of 4 XREF-MATCH against Xcelium 24.03-s004. The WP-G refusal row `wpg_local` (`always_comb begin logic t; t = a ^ b; y = t & c; end`) is admitted and pinned too (PASS vs Icarus, XREF-MATCH): its `refusal` and `measured` fields are dropped, its example comment says why.

# [0.1.406] — 2026-11-01 (WP-PROC, G1 X1: loop header forms of Verilog-2001)

Extractor, symbolic tier (register `st-for`). Master's unroll of a source-pure counted `for` (7f7c1e02) takes a header that declares
ONE `int` iterator and compares and steps it with a literal. X1 admits the spellings real code uses for the same loops: an iterator
declared OUTSIDE the header (`integer i; ... for (i = 0; i < 8; i = i + 1)`) whenever every reference to it lies inside loops that
iterate it (`_iterator_census`; its declaration is then dead and erased), the steps `i += c` / `i -= c`, and the comparisons `<=` /
`>=` (slang's `LessThanEqual`/`GreaterThanEqual` were missing from the table, so `<=` was refused even in the declared form). A
reference outside the loops, a non-`int`/`integer` iterator, a port, a parameter bound or an effectful header keeps the loud
`ForLoopStatement`. Rows `proc_loop_forms`, `proc_loop_forms_local`, `proc_loop_forms2`: 3 of 3 PASS vs Icarus, 3 of 3 XREF-MATCH against Xcelium 24.03-s004.

# [0.1.405] — 2026-11-01 (WP-PROC, G1 C1: compound assignment in the symbolic tier)

Extractor, symbolic tier (register `st-compound`; design note item C1; contract `docs/sv-proc-lowering.md`). `x op= e` as a
blocking, untimed statement is lowered to `x = x op e` (IEEE 1800-2023 11.4.1) through slang's own bound tree: the placeholder
`LValueReferenceExpression` of the right-hand side takes the converted READ of the target (`_COMPOUND_READ`, the hook the M0 path
used; it returned `None` in symbolic mode), so operand widths, signedness and context sizing are slang's. Exact when the target and
the right-hand side are source-pure (the selectors are read twice, evaluated once); a read whose width differs from the target's is
refused (`AssignmentExpression:compound-read-width`). Operators `+ - * / % & | ^ << >> <<< >>>`; whole variables, constant and
run-time bit selects, constant part selects, fixed unpacked cells, loop bodies. Refused as before (`AssignmentExpression:compound`):
nonblocking and timed forms, effectful operands, other operators, targets the tier does not take. New module
`extractors/sv/lower_proc.py` (the logic; `extract.py` holds delegating hooks of a few lines, symbolic mode only). Two pinned tests
(`test_compound_assignments`) change from "loud" to "lowered". Rows `proc_compound`, `proc_compound_param_n3/n4/n8`: 4 of 4 PASS vs Icarus, 4 of 4 XREF-MATCH against Xcelium 24.03-s004 (probe-point cross-check agrees). The WP4 row `rbw_compound` (`y = a; y += t; t = b;`), whose own comment predicted it, now reaches the always_comb self-read guard: refusal `AlwaysComb:self-read` (diff_test2 run) instead of `AssignmentExpression:compound`; its envelope, row and the sentence in `docs/sv-oracle-disagreements.md` are updated.

# [0.1.404] — 2026-11-01 (WP-PROC, G1 N3: `--top` of an instantiated module)

Extractor CLI, symbolic tier (design note `svgolf/design/real-world-sv/PROC-NOTE.md`, item N3; RB0 finding 3). `extract.py --top T`
now compiles with `T` as the ONLY top module (`topModules`) at the default point too (it already did at a probe point), so a
module that another module of the same sources instantiates can be selected; it used to fail with "no such module among top
instances" (8 of the 82 real CPU blocks of the RB0 census). The envelope of an uninstantiated top is unchanged (563 envelopes
re-extracted, 0 admitted changed). A compile error of an unrelated module no longer counts against the top: the same per-top
reading `score/slangdriver.py` and the fourstate stage already use. Row `proc_top_child` (the top is `pt_child`, instantiated
by `pt_parent` in the same file): PASS vs Icarus, XREF-MATCH against the pinned Xcelium 24.03-s004.

# [0.1.403] — 2026-11-01 (WP-PROC, G1 N1: typeless declaration dimensions)

Extractor, symbolic tier (registers `ld-init-expr`, `dc-net-z`; design note `svgolf/design/real-world-sv/PROC-NOTE.md`, item N1;
contract `docs/sv-proc-lowering.md`). A typeless / implicit-type declaration (`input [N-1:0] a`, `output wire [7:0] y`,
`wire [N-1:0] x`, a Verilog-2001 header's `input [N-1:0] a, b;`) has the ImplicitType syntax, whose `dimensions` are the same
VariableDimension children as a `logic` declaration's: `_dtype_sym` now recovers them (one tuple), so the declaration is a
`PackedType` with symbolic dimensions instead of `packed: null`, which `load_design_sv2` refused (`unrecoverable packed
dimensions`; RB0 measured it as the top loader blocker of the Verilog-2001 CPU blocks). Typeless INPUT ports and typeless
variables load now. An implicit-type NET is still a net: its refusal moves from the loader to the extractor
(`NetSymbol:net-z`, `PortSymbol:net-z`; the net lowering is N2). Refusal rows `net_width_outwire` (now `PortSymbol:net-z`) and
`vg_initn` (unchanged kind) keep refusing; five pinned tests change accordingly (`test_symbolic_default_point`,
`test_symbolic_param_widths`, `test_sym_initializers` x3: an implicit-type port initializer is lowered like a `logic` one,
the net cases are the net refusal instead of `packed: null`). New: `harness/sv/regress_envelopes.py` (the monotonicity check:
re-extract the committed symbolic envelopes and the svGolf designs with the old and the new extractor; no envelope that had no
`Unsupported` node and no `packed: null` may change; measured on 563 envelopes: 0 changed). Rows `proc_typeless_n3/n4/n8`,
`proc_typeless_nonansi_n3/n4/n8` (typeless ANSI and non-ANSI headers at three widths, x/z stimulus): 6 of 6 PASS against Icarus,
pinned on Xcelium 24.03-s004 (6 of 6 XREF-MATCH, probe-point cross-check agrees). The extractor test suite is green except the
pre-existing `test_let_expressions` failure (master's own change).

# [0.1.402] — 2026-11-01 (WP-B2, gate 4a: whole rows of a two-dimensional array and constant part selects)

Proof tactics: the recognizer of the `sv_comb` chains reads the two LEGACY select encodings of the extractor that were refused
(register `tl-sv-structure-fragment`). (1) `r[i + 1]` over a zero-based two-dimensional declaration is a whole ROW: `leafRd?` and
`tgtOf?` return `Acc.row` (through the new `bitAcc?`, which reads the declaration; over a scalar or one-dimensional declaration the
select stays `Acc.bit`), the access the `ArraySel` encoding of the same row already had, so a loop-indexed chain of rows is an
ordinary family, in an `assign` and in an `always_comb` leaf, over literal, localparam and parameter dimensions (the structural stage
had refused every one of them with "does not match the declaration"; with a literal range even `r[0]` and `r[3]` are legacy).
(2) `x[hi:lo]` over a zero-based one-dimensional declaration is `Acc.part1` (the access of the `ArraySel` part select, `partAcc?`
with no index): as a field, as a part of a concatenation, under a `Resize` marker, as a shift operand and as a TARGET; the bounds are
literals or affine in the genvars and parameters (`y[4*i+3:4*i]` in a loop is the same node, the model's `msb.isInt` side condition comes
from `affOf?_sound`). The skeletons, the shape theorems, the x-free layer, `AccGeom` and `accGeom_of` are untouched: the new work is the
instance lemmas of the two leaves. `Ctx` gains one field `elemsG` (the element width of a declaration from its evaluated dimensions,
`elemWOfDims`; `ctxElemsRow`, `ctxElemsOne`: a row is `m2 + 1` wide, a vector's element is one bit), placed BEFORE `elems` (a field named
`elems` shadows the parameter in later fields); `inst_partSel`, `selfWidth_partSel`, `instLhs_partSel` are the three facts of a part select;
`inst_leaf`, `instLhs_acc`, `leaf_eq`, `instLhs_acc_w`, `tgtOf?_cases` gain the row and part arms; `divW_eq_selfW` now takes the context
(for an undeclared base `selfWidth2` of a part select has a constant-parameter arm that `divOperandWidth2` has not); the leaf-kind
disjunctions of the shift operands (`leafKind_of_leafRd`, `shOpdKind`, `instDiv_default`, `instDiv_resize`) gain a part-select case. `bitAcc?` returns
`Except String Acc` (not `Acc`): a bare `Acc` thunk inside `.ok` was not evaluated by the tactic and printed as `bitAcc [declarations] …`.
No tactic vocabulary changed. Not read: a part select of a row, an indexed part select `x[i +: w]`, a row select of a declaration whose first range is
not zero-based, three packed dimensions (messages pinned in `comb_word/comb_errors`). Example `comb_word`: `row_chain`, `row_chain_lp`
(rows `2N` wide), `row_chain_lit` (`y = x` for an even number of rows, `~~~x` for an odd one: ONE induction over the rows, `row_chain_gen`;
every `N ≥ 1`; the structure goals close with `sv_rowmajor; omega`, the two coverage goals by naming the writing iteration), `ps_rot`
(the rotation `{x[8:0], x[15:9]}` is `x.rotateLeft 7`, a byte swap by two part-select targets is `x.rotateLeft 8`, the field `x[14:10]`), `ps_gen`
(every `N`); hints pinned verbatim. Rows `wl_rowloop_n1/n2/n3/n4/n8` and `wl_partsel_n1/n2/n4` (1 212 cycles: exhaustive rows for `N ≤ 3`, random
words, x/z in every position of the selected windows and outside them, an `always_comb` per iteration over rows) pinned on Xcelium 24.03-s004: 8 of 8 XREF-MATCH
(the first draft of `wl_rowloop` mixed `assign s[0]` with `always_comb s[i+1]`: Icarus, the second oracle of the multi-point check, refuses to drive one
variable both ways; the row writes every row procedurally). Heartbeats against the gate 3b table: every measured theorem between -0.3 % and +0.5 %; `sbox_table`
`solution` 190 075 (margin 5.0 % under the default limit, +0.0 %); the new theorems 35 246 (`ps_rot_correct`) to 133 439 (`row_chain_lp_correct`). The 24 goal dumps are identical to
those of gate 3b. The 51 Example modules that import the comb tactics (all five of `comb_word` included) build with default heartbeats.

# [0.1.401] — 2026-11-01 (WP-T-CLMUL, G1-G3)

svGolf task `clmul` (N-bit carry-less multiplier, product of polynomials over GF(2), `p` on `2N-1` bits, bans `+ - *`), registered and READY; no ls-sv model, extractor or tactic change (`LeanModels/Sv` untouched). Statement `tasks/clmul/Spec.lean` (unchanged `CombTask`; the Spec's `coeff` is the literal double sum over `i + j = k`), `REVIEW.md` for the owner (seven questions), `oracle.py`; the reference `reference/clmul_n.{sv,lean}` is `mul_n`'s array without carries, proved for every `N ≥ 1` with `sv_structure (lexRank := …)`, `sv_interface`, `sv_equations`, `sv_cover`, `sv_bridge` (206 code lines, 143 of them plain-Lean arithmetic; `solution` stage 7.42, 7.66, 7.66 s cold, time limit 120 s; the only closer beyond `mul`'s recipe is `first | omega | (simp; omega)` for one 1-D `driverDisjoint` goal whose window comparison arrives as `0 < 0 ∨ True ∧ …`); accepted also under `import Mathlib.Tactic`. Scores (pinned flow, N = 8 / 16 / 32): array 179.649 / 772.267 (depth 6) / 3214.731; generated baselines `school_tree_*` 770.935 (depth 5) at 16, Karatsuba with a 4-bit base 166.986 / 621.959 (depth 8) / 2068.877 (-19.5 % and -35.7 % against the array at 16 and 32); A0' / A1' at 16: 3429.5 um^2, 986 ps / 2941.6 um^2, 953 ps. Eight negatives with `Refute.lean` (wrong bit, dropped term, OR for XOR, reflected orientation, `2N`-bit `p`, correct only at `N = 16`; and two CORRECT designs the banlist refuses: a one-bit `+` as XOR and Kronecker substitution through `*`, both synthesizing to exactly the reference netlist). `tests/clmul/validate/validate.py`: the oracle equals Kronecker substitution, the FIPS 197 products reduce to `{c1}` and `{fe}`, and the TRUSTED Lean spec equals the oracle on every pair at `N ≤ 7` (22 228 rows).

Real-world styles (Thomas, 2026-11-01): 23 files from 19 GitHub repositories read as untrusted data (RISC-V Zbc units, GHASH, Karatsuba over GF(2)); 18 test designs, one per style, are advisory entries of `tests/expected.json` (`tests/clmul/attacks/`), all correct for every `N` (Verilator). Measured with `check.py --unproved --tactics`: the natural procedural loop (`for (int i…) if (b[i]) p ^= a << i`, or nested `r[i+j] ^= a[i] & b[j]`; 9 of the 16 multiplier cores read) is REFUSED AT `fourstate` ("run-time index … outside the declared range": a loop counter is an `int`), before ls-sv loads it (register `st-for`, rank 1; `ex-user-call` 2, `st-compound` 17, `le-recursion` 14 behind it); a function with `return` is refused at `banlist` because the pinned scoring flow's own Yosys frontend cannot parse it; generate-for with word-level `<<`/`?:` and reductions with `+:` reach the proof stage and stop at the tactics (replication, indexed part select, a generate-for start that is not an integer literal, module instances). Scores do not depend on the style (every schoolbook form 770.9 to 775.6 GE at `N = 16`).

Survey cross-check (`svgolf/design/real-world-sv/SURVEY.md`, 2026-11-01): the clmul-shaped probes of the survey (`cl__c01` to `c12`) and the five more styles written here (explicit size cast, parameter-sized unpacked arrays, replicated-bit masks, Verilog-2001 `wire`, `always @*` per row; verdicts `design`, `design`, `unproved` (tactics refuse), `design` (`decl 'a': unrecoverable packed dimensions`), `design` (`TimedStatement:ImplicitEventControl`)) all agree; `tests/run.py --only clmul` attacks 35/0, layout 22/0, references 8/0, negatives 9/0, canon 2/0, validate 33/0.

Gate 3 (stretch, blocked, nothing in `LeanModels/Sv` changed): a one-level Karatsuba for every `N` (generate-for, `H = (N+1)/2` a localparam, three `H x H` arrays of the reference's shape) is correct (Verilator, `N = 1 .. 5, 8, 9, 16, 31, 32, 33`), inside the tactic fragment, and scores 651.950 GE depth 7 at `N = 16` (-15.6 % against the array), 2556.137 / 8 at 32. Its proof compiles up to the coverage goals: the Karatsuba identity over coefficient functions, the structure theorem (about 60 s of CPU at 19 sites), the `sv_bridge` fields and the chain to the Spec. FINDINGS for the register (`tl-sv-structure-fragment`): (1) `sv_equations` leaves the `cover_k` goals in the SITE-WITNESS form `∃ b, (b = site₀ ∨ …) ∧ Q b` instead of the explicit disjunctions once a design is larger than about 40 operand reads (13- and 16-site reductions come out explicit; the correct 16-site design with 26 reads, and the 19- and 27-site ones, do not); (2) `sv_cover`'s site route fails on a bit covered by several writer families of one signal (it picks one site by the signal's name; no `Classical.em` per writer as the 2-D rule has) and, in this localparam design, even on a single-writer bit (it ends with `failed to synthesize OfNat LSite 0`, the last alternative's error); (3) a generate-for whose iteration count is zero at the DEFAULT parameter leaves no trace in slang's tree, so the loader's multi-point cross-check refuses the design ("SILENT default-point fold"): the padding loop `for (i = 0; i < 2*H-N; i++)` needs `2*H+1-N` iterations (or an odd default `N`); (4) a generate-for start must be an integer literal (`for (i = N; …)` is refused by the tactics); (5) the `intros; sv_rowmajor; omega` closer of `mul` leaves one goal shape on 1-D windows (`0 < 0 ∨ True ∧ …`) that needs `first | omega | (simp; omega)`. Material: `svgolf/design/tasks-week2/clmul/karatsuba/`.

# [0.1.393] — 2026-11-01 (WP-B2, gate 3b: concatenations as operands)

Proof tactics: concatenations as operands in the `sv_comb` fragment (register `tl-sv-structure-fragment`). `sv_structure` /
`sv_equations` now read a concatenation of literals and signal accesses wherever the word-level recognizer reads an operand:
an operand of `+ - & | ^` or of the six comparisons, an arm of `?:`, under `~`, and under slang's `Resize` marker (a marker
around a concatenation is `Sk.rsz false (Sk.cat …)`, the zero extension or truncation of a result that does not follow the
context). It is the same skeleton node as a whole-right-hand-side concatenation, so there is no new constructor and no new
shape fact (`skT_shapeC` gains one arm that reuses `parts_shape` and `fitExpr2_concat`); the self-determined positions
(`&&`, `||`, `!`, the reductions, the conditions) keep the v1 fragment through a new predicate `fragW` (`fragG` with
concatenations accepted at the context-determined positions), which the word-level theorems take in place of `fragG`
(`rdsOfW?_len`, `skT_leavesW`, `skT_shapeC`, `fragOk`; the v1 theorems are unchanged). `cnt`/`skT` read a concatenation as `pcnt`
reads and `Sk.cat`; `pcnt` and the parts lemmas (`partsT_leaves`, `partsRd_len`, `partRd?_of_ne`, …) moved down to
`CombEqBase`. New glue in `CombWord.lean`: `XF.ite_zext`, `XF.bv_pad` (a zero pad above is `BitVec.setWidth`) and
`XF.bv_cat2` (`{hi, lo}` is `hi ++ lo`). Tactic vocabulary: `CombEq.pcnt` and the new rewrite rule `Sk.rmax_cat` (the rigid width of a
concatenation, so that the width obligation of a marker around a concatenation prints as a plain inequality) joined the
simp lists of `CombEqTactic` and `CombProcTactic`; a first attempt with `Sk.rmax` and `Sk.maxO` (25 equations) cost +1.0 % to
+1.3 % on every proof with an `sv_equations` call and was replaced by the one rule. Example `comb_word/cat_add` (`s`, `t`, `w`, `e`:
bare and marked concatenations in `+`, in `?:` arms and in `==`; structure, equations pinned verbatim, `cat_add_correct` for
every `N ≥ 1`). Rows `wl_cat_add_n1/n2/n4/n8` (905 cycles, also a subtraction with markers around both operands) pinned on Xcelium
24.03-s004: 4 of 4 XREF-MATCH. Heartbeats against the gate 3a table: every measured theorem between -0.2 % and +0.6 % (largest:
`add_wide_correct`, `add_mux_settled`); `sbox_table` `solution` 190 068 (margin 5.0 % under the default limit, +0.1 %); the
references score as before. The 24 goal dumps are identical to those of gate 3a. Not in this step: a concatenation as the left
operand of a shift, which stays refused.

# [0.1.392] — 2026-11-01 (WP-G, S1b gate d: the equations of a body that writes several windows)

Proof tactics and library: `sv_equations` (and `sv_equations?`) accepts an `always_comb` body that writes several windows
(`c[i+1] = …; s[i] = …;`) and prints ONE equation and ONE knownness fact per window: the head window under the
single-window name (`eq_<signal>_<block>_<position>`), a further window `j` under `eq_<its signal>_<block>_<position>_w<j>`
(`eq_s_g_bit_1_w1`), and the stable aliases `eq_<signal>_<k>` / `known_<signal>_<k>` counting the WINDOWS that write a signal,
so `add_proc_m` has the same aliases and statements as `add_proc`. The early refusal of gate c4 is gone (its two pins in
`comb_multi/comb_errors.lean` are replaced by `comb_multi/comb_hint.lean`). Library (`CombProcEq`): `ovrSk` stops at the
first statement that is not an override; `windowSks`/`procSks` give each window's skeleton (fuel-structural, kernel-reducible);
the multi-window siblings `EqFragM`, `WidthOblM`, `EqsM`, `KnownsM`, `SrcSM`, `CoverOblM`, `site_lowLM`, `eq_of_summaryM`,
`eq_viewLM` (per window: `CombKnown.settled` at the window's offset in the concatenation, `parts_bits`/`catBits_*` for the bits
of the lowered concatenation). The single-window statements and producers (`EqFragL`, `WidthOblL`, `EqsL`, `Knowns`, `SrcS`,
`CoverObl`, `eq_viewL`, `site_lowL`) are UNCHANGED: a first version with guards inside them cost +4.8% on `sbox_bp` `solution`
(113 sites; simp expands the guard over every site) and was replaced by the siblings. Tactic (`CombProcTactic`): the multi route
is selected only when some site has a further window, with two copies of the equation normalizers (`svL_eq_norm_multi`,
`svL_eq_norm_multi_at`) carrying the skeleton vocabulary; the facts are named by structure (heads, then one group per site),
not by flattening the conjunction (a knownness fact can itself be a conjunction). All eight literal simp-list copies carry a
COPY NOTE naming their siblings. Examples: `comb_multi/{comb_hint,comb_proof,alias_reuse}.lean` and `multi_same.sv` (two windows of
one signal). svGolf: `tasks/add/reference/add_proc_m.{sv,lean}`, a reference (accepted by `check.py`, `--postsynth full`, 112.0 GE,
depth 33 at N = 16, the same netlist as `add_proc`) whose proof is `add_proc.lean`'s character for character, pinned by
`tests/add/same_proof.py` (unit step). Measured against the merged-tree baseline: the 24 goal dumps byte-identical, `sbox_bp`
`solution` 342 565k = baseline, every `solution`/`*_struct` within +0.06%, `add_mux_settled` and `lp_correct` unchanged
(199 433k of 200 000k; its split is another agent's). New reference: `add_struct` 92 575k, `solution` 159 014k. Register: the
`tl-sv-structure-fragment` row no longer lists the several-window equations as refused.

# [0.1.391] — 2026-11-01 (WP-RB1)

Extractor, register and schema doc; no Lean change. A program slang reports illegal is rejected also when its error is not inside a construct
the extractor converts (Thomas 2026-10-31 and 2026-11-01). Before, a missing `include`, an unknown macro, an unknown package import or an error
in another module of the same sources left an envelope IDENTICAL to the legal program's (exit 0, one stderr warning, no `frontend_errors`, no
`Unsupported`) and `load_design_sv2` loaded it: a theorem about `X.sem` was about slang's error recovery of the program, not about the file.
svGolf's checker was already closed (fourstate always runs, banlist when the task bans an operator, the probe sidecar for a parametric task);
ls-sv alone (a direct `load_design_sv2`, `load_sv` without a task, multi-file verification of real cores) was not. `extract.py --top` now carries
every distinct error of `Compilation.getAllDiagnostics()` (the count behind the existing "N compilation error diagnostic(s)" warning) as an
`Unsupported` `SlangError:<slang code>` in the top module's `others` (text `file:line: message`, at most 20, then one `SlangError:more`;
`SlangError:FrontendFailed` if the list cannot be built), so the design is loud (`hasUnsupported`, no run completes). The split is the one of
`SlangAnalysis:*`: a top without parameters carries them; a top with parameters and `--probe-points` keeps its verdict per POINT (the sidecar's
`frontend_errors`, enforced by `load_design_sv2`), so its default-point envelope stays instantiable where the default point is the illegal one;
a top with parameters and NO sidecar carries them, since nothing else can vouch for it. `process_symbolic` gained the keyword `probed=False`
(set by `main` when `--probe-points` is given); the M0 single-file mode is untouched. Register: new row `sa-slang-error` (never,
`P-SAME-PROGRAM`, not proposed: the ruling covers it), the policy row "slang reports a program illegal", the hole "slang's driver: what the
analysis-pass rule still does not read" (items 3 and 6) and the notes of `ex-op-invalid-compilation` say what is implemented; `SlangError:<code>`
is in the tag table of `docs/sv-envelope-schema.md`. Side finding, corrected in the schema doc: the sidecar's `frontend_errors` DOES count an
error inside a module the top does not instantiate (slang diagnoses unused definitions; the doc said it did not; measured, pinned by a test);
what it does not count is an error that only a point's override would cause in another module (the override applies to the top only), and the
analysis-pass errors of such a module. Measured: of the 454 committed sv-0.2 envelopes 451 regenerate byte-identically (envelope and sidecar), the
other 3 (`cv32e40p_alu_div`, `ff_one`, `popcnt`) need the external cv32e40p checkout; none holds a parse or elaboration error, so no admitted row
changed; all 780 differential rows (`cases2.json`) have slang-clean DUT sources; the 17 `Examples/*_refuse` fixtures are sv-0.1 (M0) envelopes and
byte-identical before and after. Tests: `extractors/sv/test_slang_errors.py` (18: the four silent shapes, the clean control, a converted
construct carried twice, analysis-only errors, the operator markers, the per-point split with and without a sidecar, the override-only error, the
CLI, the 20-error cap, fail-closed, M0 untouched); the whole extractor suite is 2271 tests, OK (it was 2253). `cv32e40p_census.py` calls
`process_symbolic` directly, so a census over an erroneous file now lists the new tag among its blockers (the committed
`docs/cv32e40p-census.json` was not regenerated: it needs the external checkout). The Lean side, run through the slot (2 minutes): the four repros (missing include, unknown macro, unknown package import, an error in another module) loaded by `load_design_sv2` have `hasUnsupported = true` with the `SlangError:<code>` node as `firstLoud` (a parameter-free top, and a parametric top without a sidecar), the clean control and a clean parametric top with a sidecar have `hasUnsupported = false`, and a parametric illegal top WITH a sidecar is refused by the multi-point cross-check (`frontendRejects`: "slang reports 1 error(s) elaborating the top alone at the point"). `harness/sv/diff_test2.py --sim iverilog --golden` on the 15 rows nearest the rule (`sa_*`, `drv_*`, `concat_assign`, `acg_alias_bits`): every refusal row keeps its refusal kind, the four verified rows are 4 of 4 `XREF-MATCH`, 0 `XREF-DIFF`; no row's envelope is touched by the rule (all 780 DUT sources are slang-clean).

# [0.1.390] — 2026-11-01

Pure sv-0.2 user functions with input-only formals may now inline a complete
procedural conditional return. The condition is squashed to preserve
SystemVerilog's procedural X/Z-false rule, and
`sem2/symbolic_conditional_function` adds a four-cycle Icarus MATCH. Stateful
bodies and general call frames remain loud. The phase-2 corpus grows **786 →
787** rows; self-check coverage remains **638 rows / 615 agree / 0 disagree /
23 recorded refusals**.

# [0.1.389] — 2026-11-01

Discarded calls to pure input-only symbolic user functions are now erased
after source-purity checks. `sem2/symbolic_statement_function` adds a
three-cycle Icarus MATCH; tasks and general call frames remain loud. The
phase-2 corpus grows **785 → 786** rows; self-check coverage remains
**638 rows / 615 agree / 0 disagree / 23 recorded refusals**.

# [0.1.388] — 2026-11-01

Pure sv-0.2 user functions with input-only formals can now inline integral
return expressions over source-pure actuals. `sem2/symbolic_inline_function`
adds a four-cycle Icarus MATCH; stateful bodies and general call frames remain
loud. The phase-2 corpus grows **784 → 785** rows; self-check coverage remains
**638 rows / 615 agree / 0 disagree / 23 recorded refusals**.

# [0.1.387] — 2026-11-01

Pure sv-0.2 user functions may now return a module parameter or enum value,
retaining a `ParamRef` through elaboration. `sem2/symbolic_parameter_function`
passes its parameter-point cross-check and Icarus oracle. The phase-2 corpus
grows **783 → 784** rows; self-check coverage remains **638 rows / 615 agree /
0 disagree / 23 recorded refusals**.

# [0.1.386] — 2026-11-01

Pure sv-0.2 user functions now accept integral constant-expression returns
through the existing typed symbolic tree. `sem2/symbolic_constant_function`
adds a one-cycle Icarus MATCH; signal-dependent returns and general call frames
remain loud. The phase-2 corpus grows **782 → 783** rows; self-check coverage
remains **638 rows / 615 agree / 0 disagree / 23 recorded refusals**.

# [0.1.385] — 2026-11-01

The sv-0.2 symbolic extractor now materializes pure literal-return user
functions with input-only, source-pure actuals. `sem2/symbolic_literal_function`
adds a one-cycle Icarus MATCH; dynamic actuals and general call frames remain
loud. The phase-2 corpus grows **781 → 782** rows; self-check coverage remains
**638 rows / 615 agree / 0 disagree / 23 recorded refusals**.

# [0.1.384] — 2026-11-01

The sv-0.2 symbolic extractor now unrolls literal-bounded, source-pure
procedural `for` loops with one `int` iterator. `sem2/for_unroll` adds a
phase-2 differential row (four cycles, Icarus MATCH); parameter-dependent and
effectful loop headers remain loud. The self-check coverage table remains
**638 rows / 615 agree / 0 disagree / 23 recorded refusals**.

# [0.1.383] — 2026-11-01 (WP-B2, gate 3a: run-time shifts)

Proof tactics: run-time shifts in the `sv_comb` fragment (register `tl-sv-structure-fragment`). `sv_structure` /
`sv_equations` now read `a << s` and `a >> s` at the context-determined positions of a right-hand side (an `assign` or an
`always_comb` leaf). The left operand is context-determined (extended to the context BEFORE the shift: a shift into a
wider target keeps the bits shifted out of the operand), the amount is self-determined and unsigned and never widens the
result, and the result is truncated to the context; the fragment reads a signal access, a sized literal or an unsized
constant at both places (a left operand under the marker that keeps its signedness, `Resize` for an unsigned shift,
`SignedResize` for a signed one), and refuses a left operand that is an operation, an amount that is an expression or a
parameter, `<<<`, `>>>` and a signed `>>` with a message that says to write the operand into a signal first. The equations
are `XF.shlBits` / `XF.shrBits` over the bit functions of the operand and of the amount (`XF.zext W …` for an extended
operand); no new `width_k` goal appears. `1 << s` is a SIGNED shift (an unsized constant is a signed 32-bit integer): its
left operand is sign-extended (`XF.sext`) and the x-free layer gained `Expr2.resizeSigned` (`CombKnownBits.lean`:
`XF.sext`, `LVec.resizeSigned_ofBoolFn`, `evals_resizeSigned`, five rows in the executable twin). Skeleton: one
constructor `Sk.sh (dir) (sg) l r` (`CombEqBase.lean`), recognizer `shOpW`/`shOpdRd?`/`shLeftRd?` (`CombView.lean`), the
shape arm and the x-free arm (`CombEqShape.lean`: `ie_shl_some`, `shOpd_shape`, `xf_shLeft`, `xf_shCore`, `xf_shFin`), the
proc chain moved only in `CombProc.lean` (`inst_idxFreeW`: `idxFree_shOpd`, `idxFree_shLeft`); the two simp sets of the
tactics did not change. New glue in `CombWord.lean`: `XF.bv_shlBits`, `XF.bv_shrBits`, `XF.bv_shlBits_s`
(`BitVec` `<<<` / `>>>` with the amount read as a natural number: an amount of `N` or more gives `0`, as in the LRM).
Examples (`comb_word`): `shl_n`, `shr_n`, `shl_wide`, `onehot`, `shl_const` (structure, equations pinned verbatim, five
theorems for every `N ≥ 1`: `y = x <<< sv.toNat`, `x >>> sv.toNat`, `x.setWidth (N + 1) <<< sv.toNat`,
`1#N <<< sv.toNat`, `x <<< 1` and `x >>> 2`) and three negatives (`neg_shift_op`, `neg_shift_amt`, `neg_shift_par`); the
gate-1 negative `neg_shift` (`a << 1`) is now accepted (a guard). The v1 messages of `rdsOfW?` and `rdsOf?` no longer say
that shifts and ordering comparisons are missing (`neg_mul`, `neg_selfdet` pins updated). `lp_correct`
(`lp_add/comb_proof.lean`) is split into `lp_comb`, `lp_acyclic` and `lp_settled` (same statement; the `maxHeartbeats`
option and its docstring are gone: the three parts need 32 693, 50 990 and 103 873 heartbeats, 187 700 with the wrapper
against 199 433 for the old single declaration). Heartbeats against the gate 2b table: every measured theorem within
-0.1 % to +1.6 % (the largest, `sbox_bp` `solution`, carries its own option); the four references score as before
(`add_n`, `add_proc`, `add_mux` 112.0 GE depth 33 at N = 16, `sbox_table` 786.894 depth 11, `sbox_bp` 200.986 depth 21).
The 24 goal dumps are byte-identical to the previous ones except `comb_proc/comb_errors` (the intended removal of the
`neg_multi` block, identical to the dump of the `wpgs2` branch). Eleven rows added to `harness/sv/cases2.json` and pinned
on Xcelium 24.03-s004 (`wl_shl_n_n1/n2/n4/n8`, `wl_shr_n_n1/n2/n4/n8`, `wl_shl_wide`, `wl_onehot`, `wl_shl_const`: 1119
cycles, 11 of 11 XREF-MATCH, 0 XREF-DIFF; `wl_onehot` includes `1 << s` into 4 and 40 bits with amounts up to 63).

# [0.1.382] — 2026-11-01 (WP-G, S1b gate d1: library only)

Library only, no behaviour change, no statement change on the single-window route: the equations of a body that writes several windows as SIBLINGS of
the single-window statements (`EqFragM`, `WidthOblM`, `EqsM`, `KnownsM`, `SrcSM`, `CoverOblM`, `site_lowLM`, `eq_of_summaryM`, `eq_viewLM`,
`multi_lowers`, `siteCtx_of_reach`, the `ovrSk` stopping rule), not yet used by the tactics (gate d2 will select them when some site has a further
window). The 24 goal dumps and every heartbeat of the single-window route are unchanged (sbox_bp `solution` exactly 342 565).

# [0.1.381] — 2026-11-01

Added `casex_timed_accept`, a differential witness for selector wildcarding
through the timed `CaseMatch` evaluator. Symbolic `always_comb` casex remains
refused. Differential coverage is **638 rows / 615 agree / 0 disagree / 23
recorded refusals**.

# [0.1.380] — 2026-11-01

Added `casez_timed_accept`, a differential witness for timed four-state
wildcard matching through the existing `CaseMatch` lowering. Symbolic
`always_comb` casez/casex remains refused. Differential coverage is **637 rows
/ 614 agree / 0 disagree / 23 recorded refusals**.

# [0.1.379] — 2026-11-01 (WP-BV, G3)

svGolf checker and register, no ls-sv model or tactic change: `bv_decide` is NOT supported again. Thomas, after the sandbox widening
it needed was explained (`fork`, the exec of `cadical`, a writable temporary directory; a hostile file could also start copies of
`lean`): "maybe that's a bad idea. Let's not support external solvers for now." One constant in `svgolf/check.py`,
`BV_DECIDE_SUPPORTED = False` (read by no environment variable, option or task key), makes `allow_bv_decide: true` an infrastructure
error, keeps `--bv-decide` from the comparator (which now rejects a `bv_decide` axiom naming the policy) and keeps the sandbox Spec
from ever getting the solver; a failed `bv_decide` proof carries a hint at `solution` (sandbox on) or `comparator` (sandbox off). The
WP-BV work stays, dormant and tested: the comparator's re-verification of the generated axiom and the Spec grant. The five `task.json`
are back to `allow_bv_decide: false`. Register: the `bv_decide` policy row is the ruling, `sg-bv-decide` is a refused row again with its
reason, the "Proofs are symbolic" policies say "not supported for now". Enabling later: `svgolf/README.md` "`bv_decide`".

# [0.1.378] — 2026-11-01

Added `local_decl_timed_accept`, a differential witness for local declaration
state in timed initial processes. The symbolic `always_comb` `LocalDecl`
boundary remains loud. Differential coverage is **636 rows / 613 agree / 0
disagree / 23 recorded refusals**.

# [0.1.377] — 2026-11-01

Added the `for_timed_accept` differential witness for the retained timed
procedural `for` path. The symbolic `always_comb` loop boundary remains loud.
Differential coverage is **635 rows / 612 agree / 0 disagree / 23 recorded
refusals**.

# [0.1.376] — 2026-11-01

Timed `always_ff` now retains three or more sampled event members through the
same expression registration. The `always_ff_three_event_accept` witness
matches clock, reset, and alternate-event publications. Differential coverage
is **634 rows / 611 agree / 0 disagree / 23 recorded refusals**.

# [0.1.375] — 2026-11-01

Timed `always_ff` now accepts packed vector asynchronous-reset expressions
through the same sampled registration as expression clocks. The
`always_ff_vector_reset_accept` witness matches reset publication, and
differential coverage is **634 rows / 610 agree / 0 disagree / 24 recorded
refusals**.

# [0.1.374] — 2026-11-01 (WP-BV, G1-G2)

svGolf checker and register, no ls-sv model or tactic change: `bv_decide` is now ALLOWED in submissions (Thomas, 2026-11-01: "we
should remove the bitblast ban, since we have the proof time limit anyway"; "Submissions shouldn't be allowed to declare new
axioms"). A `bv_decide` proof ends in a generated axiom `<decl>._native.bv_decide.ax_* : verifyBVExpr E C = true`; the comparator
(`svgolf/check/Comparator.lean`, point 6) now evaluates that statement itself, accepting the axiom only when it is true: it decodes `E`
from its kernel value (no submission code runs), requires the toolchain's own `toExpr` of the decoded value to equal that kernel
value, and runs the toolchain's compiled `verifyBVExpr`. A forged axiom over a false certificate is rejected ("does not verify");
`native_decide`, `Lean.ofReduceBool`, `extern`, `implemented_by` and any other axiom stay rejected. `allow_bv_decide` in `task.json`
defaults to true (the five shipped tasks now say so); `false` forbids it. The solution's compile (only) gets the toolchain's `cadical`,
`fork` and one temporary directory in the sandbox, measured to be the minimum `bv_decide` needs (the one widening: a file there can
start copies of `lean`, bounded by the supervisor's group limits, pinned by the `host_spawn_bomb` sandbox attack). Measured: a 38 KB certificate
verifies in 1 ms, a 504 MB one in 22 s. Register: the `bv_decide` policy row now states the landed behaviour, `sg-bv-decide` is
re-scoped to what is still refused (a certificate that does not verify, `allow_bv_decide: false`), plan item `BVDECIDE` is done.
Design note and measurements: `svgolf/design/bv-decide/NOTE.md`.

# [0.1.373] — 2026-11-01

Refreshed the pre-expression-clock vector and selected-clock fixtures as PASS
witnesses, retiring two stale recorded-refusal envelopes. Differential
coverage is **634 rows / 609 agree / 0 disagree / 25 recorded refusals**.

# [0.1.372] — 2026-11-01

Timed `always_ff` now accepts packed expression clocks, including vector and
selected clocks, through the retained sampled-expression registration. The
`always_ff_expression_clock` witness matches both captures using the result
LSB for edge detection. Differential coverage is **634 rows / 607 agree / 0
disagree / 27 recorded refusals**.

# [0.1.371] — 2026-11-01

The generated coverage page now states the current timed boundary accurately:
statement-level expression waits and declared named-event triggers are admitted,
while other non-initial process forms remain refused. The grammar and
differential tables are unchanged.

# [0.1.370] — 2026-11-01

Named event expressions now use the retained scheduler queue: `always @(evt)`
waits on an epoch publication from `-> evt`, and the
`event_named_accept` witness matches `NAMED EVENT PASS`. Differential coverage
is **633 rows / 606 agree / 0 disagree / 27 recorded refusals**.

# [0.1.369] — 2026-11-01 (WP-R-D, gate 2)

slang's ANALYSIS-pass errors refuse like its elaboration errors (Thomas 2026-11-01: "slang reports a program illegal" means
the full slang driver). The API: `pyslang.analysis.AnalysisManager(driver.analysisOptions).analyze(comp)` on an elaborated
compilation, `getDiagnostics()` (what `Driver.runAnalysis` does). `Compilation.getAllDiagnostics()` omits it, and so does a bare
`isError()`: `MultipleAlwaysAssigns`, `MixedVarAssigns` and `MultipleContAssigns` are WARNINGS by slang's own definition and errors
only in the slang `Driver` (its engine promotes 41 codes and switches 134 off), so the classification asks the Driver's own
`DiagnosticEngine` (a `Driver` processed on the stdin placeholder `slang -`) with a NULL source location: a `pragma diagnostic
ignore` of the program, which the real CLI honours, cannot downgrade a report. Extractor (`extractors/sv/extract.py`,
`_slang_driver`, `_slang_analysis_errors`, `_slang_analysis_nodes`): a top module WITHOUT parameters carries one `Unsupported`
`SlangAnalysis:<slang code>` per error (slang's message as `text`, the diagnostic's point as `span`); a top WITH parameters gets
the verdict per point (the probe sidecar's `frontend_errors` now counts them, and `frontend_analysis` lists them when there are
any), because an analysis error can depend on the point (`sem2/drv_pw_ff` is illegal at D = 2 and legal at D = 1: a marker in the
default envelope would have refused the admitted row `drv_pw_ff_d1`). svGolf: new `score/slangdriver.py` (the same function, once more:
`extractors/sv/test_slang_analysis.py` checks they classify alike), read by the `banlist` front check and the `fourstate` stage
as `slang analysis error <code> at <file>:<line>: <message>`; `check.py`'s integrity tripwire lists the new file.
Measured before changing anything: 12 of the 1271 committed envelopes hold an analysis error (7 parameter-free symbolic tops, 2
parametric, 3 M0), 1 of the 220 svGolf designs; the full re-extraction of the 435 committed sv-0.2 envelopes (9 of them need sources that are not on this
machine, as before) differs from the committed bytes in exactly those 7 (all refusal rows, regenerated), and the 128 `--probe-points` groups of the parametric rows
differ only in the sidecars of the refusal points `drv_mix_k0`, `drv_param_ov_k0/k1`, `drv_pw_par_k0` (`frontend_errors` 0 -> 1,
informational on a refusal row); no admitted row changed. Rows: `drv_genvar_ov` and `drv_pw_lit` now refuse on
`SlangAnalysis:MultipleContAssigns` / `:MultipleAlwaysAssigns`, and their Lean `driversOk` guard stays verified by new parametric
twins `drv_genvar_ov_p`, `drv_pw_lit_p`; new refusal rows `sa_input_assign`, `sa_initial_comb` (closes the `initial` plus
`always_comb` gap of the audit, section 5, finding 2), `sa_always_notime`. Tests: `extractors/sv/test_slang_analysis.py` (10:
every shape, the Driver severity table, pragma, unrelated and instantiated modules, per-point, fail-closed; six fail on the old
extractor), `fourstate.py --selftest` (7 new rows, 6 of them fail without the rule) and `banlist.py --selftest` (7 new) with the
fixtures `score/tests/fourstate/analysis_*.sv`, and five attacks `tests/add/attacks/slang_*.sv` (`tests/expected.json`, stage
`banlist`, with slang's message; before the rule they were refused at `design` by the Lean guards or by the loader's missing
`Initial` kind, and `slang_input_assign` at `fourstate` only through Yosys `check`). Register: policy row implemented, new rows
`sa-slang-analysis` and `sg-slang-analysis`, the notes of `le-driver-*` and `pr-always-nocontrol` updated, the hole rewritten
with what is still unread (the elaboration warnings the driver promotes: 9 `IndexOOB`, 9 `RangeOOB`, 1 `DynamicNotProcedural`
envelopes are admitted Xcelium-pinned rows; the M0 mode; a task with an empty banlist; a module the design does not
instantiate). Verification: `extractors/sv` pytest 2243 passed / 8 skipped (the 8: `SV_TESTS_ROOT` unavailable, as before); svGolf
`tests/run.py` layout + unit 33 / 0 failed; steps `references`, `negatives`, `attacks` for `add` (31 + 14 + 34 checks) and `mul`
(34 + 6 + 2), 0 failed, scores unchanged (add references 112.0 GE depth 33 at N=16); the Lean steps of this gate ran under the shared
slot (the first `add` references run failed at `integrity` because `check.py` was edited while it ran, and was rerun clean).

# [0.1.368] — 2026-11-01 (WP-R-D, gate 1)

String literal escapes `\a \v \f` are ADMITTED (Thomas 2026-11-01: an Xcelium-only dissent is not a tools split; register
policy "An Xcelium-only dissent is NOT a tools split", row `lit-string`). Re-measured the same day with the audit's tools:
slang, Icarus 12.0, Verilator 5.042 and Yosys 0.53 give 7, 11 and 12 for `assign y = "\a";` (and `\v`, `\f`), Xcelium
24.03-s004 gives the plain letters 0x61, 0x76, 0x66; `\n` and `\101` agree in all five; IEEE 1800-2023 5.9.1 Table 5-1
(printed page 83) lists the three. The extractor's `_disputed_string_escape` now reads only the hex escape `\xdd`
(`StringLiteral:hex-escape`, row `lit-string-hex`, UNCHANGED), `StringLiteral:named-control-escape` is gone, and
`_convert_string_expr` emits the table's byte as an ordinary `Literal` (the Lean loader needed no change: `run2` equals
Icarus on both new rows). The other sites that shared the refusal through `_contains_disputed_string_escape` (constant
folding of a literal, `$sformatf`, `$sscanf`, `$test$plusargs` / `$value$plusargs`, the two `$sformat` forms, unpacked
string-array initializers) follow it. New rows in `harness/sv/cases2.json`:
`lit_str_ctl` (the three escapes alone, in one literal, through a localparam, as a run-time operand, in a comparison;
Xcelium declared departure `xcelium-named-control-escape-letters`, hash-bound, `XREF-DECLARED`) and `lit_str_ctl_ok` (octal
spellings, `\n`, `\t`, an escaped backslash and quote: `XREF-MATCH`); `harness/sv/xcelium_golden.json` 527 -> 529 pins
(`xcelium_batch.py prepare/run --case`, the internal Xcelium host through the license gate, own remote directory, 2 rows in 21 s). Register: the
`\a \v \f` part leaves row `lit-string` (now `StringLiteral:encoding | :width`, category `later`), the policy row records the
implementation, `departures` lists the new one. Tests: `extractors/sv/test_selected_types.py` (the refusal tests became
admission tests; four of them fail on the old extractor; the hex-escape and octal tests are unchanged and green).
`extractors/sv` pytest 2233 passed / 8 skipped (the 8: `SV_TESTS_ROOT` unavailable, as before); `pr-init-var` untouched.

# [0.1.367] — 2026-11-01 (WP-I, step I0)

Proof tactics, message only: a design that instantiates modules (`X.sem N` is `PDesign.instantiateHD2 …`, as `ripple_fa`) is now refused
by `sv_structure`, `sv_interface` and `sv_equations` (both elaborators) with `this design instantiates modules, and the `sv_comb` tactics
cannot summarize module instances yet … flatten the design in the source … or prove the structure by hand`, instead of `cannot read a
`load_design_sv2` family (`X.sem N`) off the design`, which did not mention instances. Behaviour is unchanged otherwise: the loader, the
scorer and the post-synthesis check accept such designs. The refusal is pinned in `Examples/system-verilog/ripple_fa/comb_errors.lean`.

# [0.1.366] — 2026-11-01

Mixed scalar/expression event lists such as `always @(a | b or c)` now use a
single retained registration. `always_event_mixed_expression_list` matches the
`ALWAYS EVENT MIXED LIST PASS` transcript, and expression members wake on
operand dependency publications. Differential coverage is **633 rows / 605
agree / 0 disagree / 28 recorded refusals**.

# [0.1.365] — 2026-11-01

Statement-level expression waits such as `@(a ^ b);` now retain their sampled
expression and resume the saved initial-process tail through the existing
event wake queue. The `event_wait_expression_accept` witness matches the
`PROCEDURAL EXPRESSION WAIT PASS` transcript. Differential coverage is **633
rows / 604 agree / 0 disagree / 29 recorded refusals**.

# [0.1.364] — 2026-11-01 (WP-B2, gate 2b)

Proof tactics: comparisons, truncation and unsized constants in the `sv_comb` fragment (register
`tl-sv-structure-fragment`). `sv_structure` / `sv_equations` now read, at the context-determined positions of a
right-hand side (an `assign` or an `always_comb` leaf), the six comparisons `== != < <= > >=` (one bit; the operands are
context-determined at the WIDER of their own natural widths, a narrower one under slang's `Resize` marker), unsized
integer constants (32 bits on their own, materialized at the context width: `a == 3`, `a + 1`, `a - 1`) and a width
conversion around an OPERATION (a sum into a narrower target, a comparison into a vector). The equations are the
nested form over `XF.val` / `XF.eqv` / `XF.constBit` / `XF.zext`; a marker around an operation that follows a wider
context carries the single `if w < tw` of `instExpr2`. Skeleton: `Sk.eqv`/`Sk.nev` become `Sk.cmp (op : CmpOp)`, new
`Sk.const`, `Sk.rsz (pr : Bool)` (the propagation flag of the operation under the marker, decided when the skeleton is
built), `Sk.rmax` (`rigidMax2`) beside `Sk.width` (now the natural width, `selfWidth2`: the former `Sk.nwidth` is
merged into it), and `Sk.rok`, the part of the `+ -` contract that says every rigid operand fits the context (the
shape bundle's `rigidMax2` is no longer the natural width: constants carry no x bits, which is the S/R split of
the gate-1 finding). New glue in `CombWord.lean`: `XF.constBit`, `XF.bv_constBit`, `XF.bv_zext_trunc`, `XF.lt_bv`,
`XF.le_bv`. The generic `CombView` lemmas for `==`/`!=` are generalised to `CmpOp` (`ie_cmp_cases`, `ie_cmp`,
`sw_cmp`, `rm_cmp`; the `==`/`!=` statements are kept as corollaries). The proc chain changed in `CombProc.lean` only
(`inst_idxFreeW`, the `CmpOp` and marker arms) and in the two simp sets of `CombProcTactic` (`Nat.max_self`,
`Sk.rok`); `CombProcEq.lean`, `CombProcLower.lean`, `CombProcSummary.lean` are unchanged. The 24 goal dumps of the earlier
tactic examples and references are byte-identical; `add_mux_correct` (`comb_ops/comb_proof.lean`) is split into
`add_mux_comb`, `add_mux_acyclic` and `add_mux_settled` (same statement, a budget per declaration: the whole proof had sat at
185 000 to 200 000 of the 200 000 default and crossed it with the S1b merge; the largest piece now needs less than 140 000). Four refusal pins became guards (`neg_trunc`, `neg_unsized`, `neg_lt`, `neg_cmp`, `neg_lnot_wide`: accepted
since this step). Examples: `comb_word/cmp_same`, `cmp_mixed`, `trunc_inc` (structure, equations pinned verbatim,
`cmp_same_correct` for every `N`, `trunc_inc_y1_final`). Rows `wl_cmp_same`, `wl_cmp_mixed`, `wl_trunc_inc` added to
`harness/sv/cases2.json` and pinned on Xcelium (XREF-MATCH; the gate-1 rows `wl_cmp_ctx`, `wl_unsized`, `wl_addsub_ctx`
re-checked: XREF-MATCH).

# [0.1.363] — 2026-11-01 (WP-G, S1b gate c4)

Proof tactics and library: `sv_equations` (and `sv_equations?`) on a design with an `always_comb` that writes several
windows now answers with the reason and the way out instead of a failed decision: `site `g_bit#1[i]`: an always_comb
body that writes several windows (c[i + 1], s[i]): `sv_structure` accepts it, but `sv_equations` has no equations for
such a body yet (outside the supported fragment: write one always_comb per written window)`. New theorem
`cell_lowers_site` (`Examples/system-verilog/comb_multi/cell_site.lean`): the two-window adder cell lowers to ONE assign
of both windows for every `N` and every bit `k < N`, through `lower_body_site`. The 24 goal dumps, the pins and the
four references are unchanged.

# [0.1.362] — 2026-11-01 (WP-G, S1b gate c: bodies of several windows)

Proof tactics: `sv_structure` on a design with an `always_comb` that writes SEVERAL windows (register
`tl-sv-structure-fragment`). A body such as `if (p[i]) c[i+1] = c[i]; else c[i+1] = a[i]; s[i] = p[i] ^ c[i];` (the
whole adder cell in one body) or `y = a; if (e) y = b; z = a ^ b;` is read as ONE site whose written windows are all
its targets; `sv_structure?` prints `drives c[i + 1] and s[i]`. The obligations count every window (in range, one
driver per bit against every other window and within the body, no read of any window of the body, the rank is the
site's), and the structure theorem `CombDesign ∧ Acyclic` is proved for the adder with the two-window cell for every
`N ≥ 1` (`Examples/system-verilog/comb_multi/comb_view.lean`). A window written in two separate groups of statements
(`y = a; z = b; if (e) y = b;`) is refused with its own message; `sv_equations` still refuses a body of several
windows (the equations are the next gate). Single-window designs read exactly as before: the 24 earlier goal dumps are
byte-identical, except `comb_proc/comb_errors` whose `neg_multi` pin became the accepted instance above.

# [0.1.361] — 2026-11-01

Zero-delay plain `always` procedures now have a recorded timed refusal:
`always_no_control_refuse` keeps `always y = a` loud instead of allowing a
zero-time loop to run until fuel exhaustion. Differential coverage is **633
rows / 603 agree / 0 disagree / 30 recorded refusals**.

# [0.1.360] — 2026-11-01

Timing controls inside `always_latch` now have a recorded timed refusal:
`always_latch_delay_refuse` keeps a body containing `#1` loud because latch
settling cannot suspend in the retained Active comb path. Differential coverage
is **632 rows / 603 agree / 0 disagree / 29 recorded refusals**.

# [0.1.359] — 2026-11-01

Timing controls inside `always_ff` now have a recorded timed refusal:
`always_ff_delay_refuse` keeps a body containing `#1` loud, and the timed loader
checks every clock/reset variant for the same boundary. Differential coverage
is **631 rows / 603 agree / 0 disagree / 28 recorded refusals**.

# [0.1.358] — 2026-11-01

Timing controls inside `always_comb` now have a recorded timed refusal:
`always_comb_delay_refuse` keeps a body containing `#1` loud because the comb
process cannot suspend in the retained Active settle pass. Differential
coverage is **630 rows / 603 agree / 0 disagree / 27 recorded refusals**.

# [0.1.357] — 2026-11-01

Delayed continuous assignments now have a recorded timed boundary:
`assign_delay_refuse` keeps `assign #1 y = a` loud because delayed publication
needs a timed driver queue. Differential coverage is **629 rows / 603 agree /
0 disagree / 26 recorded refusals**.

# [0.1.356] — 2026-11-01

Selected continuous-assignment targets now have a recorded timed boundary:
`assign_selected_target_refuse` remains loud because packed bit-select drivers
need per-bit driver state and resolution. Differential coverage is **628 rows /
603 agree / 0 disagree / 25 recorded refusals**.

# [0.1.355] — 2026-11-01

The timed `always_latch` path now has a multi-output capture and hold witness.
`always_latch_multi_output` checks updates while enabled and retention after the
enable falls through the existing inferred-sensitivity queue. Differential
coverage is **627 rows / 603 agree / 0 disagree / 24 recorded refusals**.

# [0.1.354] — 2026-11-01

The timed `always_comb` path now has a branching multi-output witness.
`always_comb_branch_outputs` checks both `if/else` arms and later source
updates through inferred sensitivity and the existing Active wake queue.
Differential coverage is **626 rows / 602 agree / 0 disagree / 24 recorded
refusals**.

# [0.1.353] — 2026-11-01

Dynamic whole-net continuous drivers now have a changing-source differential
witness. `assign_dynamic_resolution` observes resolved `0`, conflicting `x`,
`1`, and `0` after successive source updates through the existing per-driver
table and scheduler queue. Differential coverage is **625 rows / 601 agree / 0
disagree / 24 recorded refusals**.

# [0.1.352] — 2026-11-01

The `always_ff` three-event boundary now has a recorded refusal:
`always_ff @(posedge clk or posedge rst or negedge alt)` remains loud because
the timed process retains one direct clock plus at most one asynchronous reset.
The frontend accepts the source, while the timed tier records
`TimedStatement:EventListControl` rather than silently treating the third event
as another reset. Differential coverage is **624 rows / 600 agree / 0 disagree
/ 24 recorded refusals**.

# [0.1.349] — 2026-11-01 (WP-G, S1b gate c1)

Library only, no behaviour change: `TSite.more` (the further target accessors of an `always_comb` body that writes
several windows; every recognizer still returns `[]`), and the three summary obligations, `StructOk` and `AutoObl`
read them: `InRangeObl`, `DisjObl` and `RankObl'` each gain a conjunct guarded by "no site has a further window", which
the tactics' normalization decides first and drops, so no tactic list changed and the 24 goal dumps, the pins and the
four references (accepted, same scores) are unchanged; the flat-netlist closed forms (`*_of_plain`) take the guard in
their one `hp` premise. Heartbeats of the reference theorems move by at most +0.7%.

# [0.1.351] — 2026-11-01

The `always_ff` vector-reset boundary now has a recorded refusal:
`always_ff @(posedge clk or posedge rst)` remains loud because asynchronous reset
events require one-bit identifiers. Differential coverage is **623 rows / 600
agree / 0 disagree / 23 recorded refusals**; grammar coverage remains **216
MATCH / 25 REFUSE** in the current upstream census.

# [0.1.350] — 2026-11-01

The `always_ff` selected-clock boundary now has a recorded refusal:
`always_ff @(posedge bus[0])` remains loud because the clock contract requires a
direct one-bit identifier. Differential coverage is **622 rows / 600 agree /
0 disagree / 22 recorded refusals**; grammar coverage remains **216 MATCH / 25
REFUSE** in the current upstream census.

# [0.1.349] — 2026-11-01

The `always_ff` vector-clock boundary now has a recorded refusal:
`always_ff @(posedge bus)` remains loud because the clocked contract requires a
one-bit identifier. Differential coverage is **621 rows / 600 agree / 0
disagree / 21 recorded refusals**; grammar coverage remains **216 MATCH / 25
REFUSE** in the current upstream census.

# [0.1.348] — 2026-11-01

Descending dynamic packed part-selects now have a guarded explicit-edge witness:
`always @(edge bus[base -: 2] iff en)` uses the existing any-value-change
registration. Differential coverage is **620 rows / 600 agree / 0 disagree /
20 recorded refusals**; grammar coverage remains **216 MATCH / 25 REFUSE** in
the current upstream census.

# [0.1.347] — 2026-11-01

Library only, no behaviour change, no statement change: the shared cores of the soundness half of the always_comb
chain. `CombViewMain`: `PairFacts`, `desc_facts`, `realized_comb_core`, `realized_acyclic_core` (the lowered chain's
`realizedL_comb` / `realizedL_acyclic` and the old chain's `realized_comb` / `realized_acyclic` are one `exact`
each). `CombViewSound`: `SiteCtx`, `pairs_ctx`, `pairs_desc_site` (the shared preamble of `pairs_desc` /
`pairs_descL`), `sound_prefix` (the shared first half of `Summary.sound` / `Summary.soundL`), `fams_expand2W` (the
family expansion from the well-formedness of the families alone; `fams_expand2` / `fams_expand2P` are corollaries).
The goal dumps, the references and every pin of a kept name are unchanged.

# [0.1.347] — 2026-11-01

Dynamic packed part-select events now have an explicit-edge `iff` witness:
`always @(edge bus[base +: 2] iff en)` preserves the guard while using the
existing any-value-change registration. Differential coverage is **619 rows /
599 agree / 0 disagree / 20 recorded refusals**; grammar coverage remains
**216 MATCH / 25 REFUSE** in the current upstream census.

# [0.1.346] — 2026-11-01

Library only, no behaviour change: `LeanModels/Sv/CombProcBody.lean` (new, imported by nothing yet). The recognizer
of a body of SEVERAL windows (`multiSegs?`: consecutive statements grouped by window into segments, each a
`treeStmt?` tree plus its `if (c) …;` overrides; a window written in two separate groups of statements, e.g.
`y = a; z = b; y = c;`, is refused with its own message) and the instantiation of such a body
(`bodyP2`, `segsOf`, `instStmt2_body`, `proc_body_eq`, `lower_body_site`: the instantiated `always_comb` lowers to ONE
assign of all its windows; `drvWins_body`). `siteOfP?` and every tactic still read ONE window and refuse a body of
several with the same message as before (the summary side is gate c), so the goal dumps of the 24 earlier tactic
examples and references are byte-identical and no pin changes. Segments are `List (Acc × PTR)`: the single-tree
lemmas apply per segment unchanged and `PT`/`PTR`/`PTree` keep their signatures (the word-level `+ -` interface of
WP-B2 is untouched).

# [0.1.346] — 2026-11-01

Comma-separated event lists now retain per-member guards with explicit edges:
`always @(edge a iff en, edge b iff en)` uses the existing any-value-change
registrations. Differential coverage is **618 rows / 598 agree / 0 disagree /
20 recorded refusals**; grammar coverage remains **216 MATCH / 25 REFUSE** in
the current upstream census.

# [0.1.345] — 2026-11-01

Plain event lists now retain per-member guards with explicit edges:
`always @(edge a iff en or edge b iff en)` uses the existing any-value-change
registrations. Differential coverage is **617 rows / 597 agree / 0 disagree /
20 recorded refusals**; grammar coverage remains **216 MATCH / 25 REFUSE** in
the current upstream census.

# [0.1.344] — 2026-11-01

Dynamic packed bit-select events now have an explicit-edge `iff` witness:
`always @(edge bus[idx] iff en)` preserves the guard while using the existing
any-value-change registration. Differential coverage is **616 rows / 596 agree
/ 0 disagree / 20 recorded refusals**; grammar coverage remains **216 MATCH /
25 REFUSE** in the current upstream census.

# [0.1.343] — 2026-11-01

Packed bitwise-not event expressions now have an explicit-edge `iff` witness:
`always @(edge ~bus iff en)` preserves the guard while using the existing
any-value-change registration. Differential coverage is **615 rows / 595 agree
/ 0 disagree / 20 recorded refusals**; grammar coverage remains **216 MATCH /
25 REFUSE** in the current upstream census.

# [0.1.342] — 2026-11-01

Packed logical-not event expressions now have an explicit-edge `iff` witness:
`always @(edge !bus iff en)` preserves the guard while using the existing
any-value-change registration. Differential coverage is **614 rows / 594 agree
/ 0 disagree / 20 recorded refusals**; grammar coverage remains **216 MATCH /
25 REFUSE** in the current upstream census.

# [0.1.341] — 2026-11-01

Scalar reduction event expressions now have an explicit-edge `iff` witness:
`always @(edge |bus iff en)` preserves the guard while using the existing
any-value-change registration. Differential coverage is **613 rows / 593 agree
/ 0 disagree / 20 recorded refusals**; grammar coverage remains **216 MATCH /
25 REFUSE** in the current upstream census.

# [0.1.340] — 2026-11-01

Packed concatenation event expressions now have an explicit-edge `iff` witness:
`always @(edge {a, b} iff en)` preserves the guard while using the existing
any-value-change registration. Differential coverage is **612 rows / 592 agree
/ 0 disagree / 20 recorded refusals**; grammar coverage remains **216 MATCH /
25 REFUSE** in the current upstream census.

# [0.1.339] — 2026-11-01

Packed ternary event expressions now have an explicit-edge `iff` witness:
`always @(edge (sel ? a : b) iff en)` preserves the guard while using the
existing any-value-change registration. Differential coverage is **611 rows /
591 agree / 0 disagree / 20 recorded refusals**; grammar coverage remains
**216 MATCH / 25 REFUSE** in the current upstream census.

# [0.1.338] — 2026-11-01

Packed binary event expressions now have an explicit-edge `iff` witness:
`always @(edge (a | b) iff en)` preserves the guard while using the existing
any-value-change registration. Differential coverage is **610 rows / 590 agree
/ 0 disagree / 20 recorded refusals**; grammar coverage remains **216 MATCH /
25 REFUSE** in the current upstream census.

# [0.1.337] — 2026-11-01

Explicit edge controls now have an `iff` witness:
`always @(edge a iff en)` preserves the scalar guard while using the existing
any-value-change registration. Differential coverage is **609 rows / 589 agree
/ 0 disagree / 20 recorded refusals**; grammar coverage remains **216 MATCH /
25 REFUSE** in the current upstream census.

# [0.1.336] — 2026-11-01

Comma-separated plain event lists now have an explicit-edge witness:
`always @(edge a, edge b)` maps each member to the existing any-value-change
registration. Differential coverage is **608 rows / 588 agree / 0 disagree /
20 recorded refusals**; grammar coverage remains **216 MATCH / 25 REFUSE** in
the current upstream census.

# [0.1.335] — 2026-11-01

Plain event lists now have an explicit-edge witness:
`always @(edge a or edge b)` maps each member to the existing any-value-change
registration. Differential coverage is **607 rows / 587 agree / 0 disagree /
20 recorded refusals**; grammar coverage remains **216 MATCH / 25 REFUSE** in
the current upstream census.

# [0.1.334] — 2026-11-01

Dynamic packed part-select events now have an explicit-edge witness:
`always @(edge bus[base +: 2])` uses the existing any-value-change registration
for the selected result. Differential coverage is **606 rows / 586 agree / 0
disagree / 20 recorded refusals**; grammar coverage remains **216 MATCH / 25
REFUSE** in the current upstream census.

# [0.1.333] — 2026-11-01

Dynamic packed bit-select events now have an explicit-edge witness:
`always @(edge bus[idx])` uses the existing any-value-change registration for
the selected result. Differential coverage is **605 rows / 585 agree / 0
disagree / 20 recorded refusals**; grammar coverage remains **216 MATCH / 25
REFUSE** in the current upstream census.

# [0.1.332] — 2026-11-01

Proof tactics: `+`, `-` and the `Resize` marker in the leaves of an `always_comb` tree (register
`tl-sv-structure-fragment`). `sv_structure` / `sv_equations` on a body whose `if`/`case`/override leaves are sums
or differences (`if (c) y = a + b; else y = a - b;` into an `(N+1)`-bit `y`) now print the nested choice over
`XF.addBits` / `XF.subBits` / `XF.zext` and leave the `width` contract of gate 1 per leaf. The skeleton has ONE
reading: `PSk.bit σ dw tw rd`, `PSk.low σ dw tw`, `PSk.WidthOk σ dw tw` carry the target width, a leaf is read by
`Sk.bitC` / `Sk.WidthOkC`; `Sk.low σ dw tw` takes the declared widths (read by nothing yet; the interface a lowering
that depends on the operands' widths needs). `rhsRds?` is the word-level recognizer (`rdsOfW?`); `rdsOf?` stays
as the reader of the self-determined operands (conditions, the `case` subject, the operands of `!`, reductions,
`&&`, `||`, `==`, `!=`). Deleted without a consumer: the v1 `rhs_shape`, `proc_shape`, `gate_shape`,
`skT_selfWidth`, `skRhs_leaves`, `rhs_ok` and their word-level twins' suffixes (`rhsRdsW?`, `rhs_okW`,
`skRhs_leavesW`). New: `inst_idxFreeW`, `Sk.v1`, `Sk.WidthOkC.toV1`, `skT_v1`. `PT.low` / `PTree.low` are
unchanged; the proc chain changes only in `CombProcEq.lean` (the skeleton side) and `CombProc.lean` (the new
`inst_idxFreeW`, the re-proved `rhs_idxFree`); the 24
goal dumps of the earlier tactic examples and references are byte-identical, `add_mux_correct` needs the same
185 000 to 200 000 heartbeats (a tight spot: the simp sets swap names, they must not grow). One refusal pin
became a positive design: `comb_word/neg_proc` is now `comb_word/addp` (`sv_equations?` pinned, `addp_settles`
proved for every `N`). Row `wl_proc_addsub` added to `harness/sv/cases2.json` and pinned on Xcelium
(XREF-MATCH, 56 cycles, an x condition takes the `else` arm).

# [0.1.332] — 2026-11-01

Explicit `edge` now has a packed bitwise-not witness:
`always @(edge ~bus)` uses the existing any-value-change registration for the
sampled result. Differential coverage is **604 rows / 584 agree / 0 disagree /
20 recorded refusals**; grammar coverage remains **216 MATCH / 25 REFUSE** in
the current upstream census.

# [0.1.331] — 2026-11-01

Explicit `edge` now has a packed logical-not witness:
`always @(edge !bus)` uses the existing any-value-change registration for the
sampled result. Differential coverage is **603 rows / 583 agree / 0 disagree /
20 recorded refusals**; grammar coverage remains **216 MATCH / 25 REFUSE** in
the current upstream census.

# [0.1.330] — 2026-11-01

Explicit `edge` now has a scalar-reduction witness:
`always @(edge |bus)` uses the existing any-value-change registration for the
sampled reduction result. Differential coverage is **602 rows / 582 agree / 0
disagree / 20 recorded refusals**; grammar coverage remains **216 MATCH / 25
REFUSE** in the current upstream census.

# [0.1.329] — 2026-11-01

Proof tactics: the `sv_comb` tactics no longer depend on the ambient simp set (WP-B review finding, gate M), and the
semantic core of a body that writes several windows (WP-G S1b gate a).

* The tactics' own plain `simp` calls (`sv_structure`, `sv_equations`, `sv_interface`, `sv_norm`, `svL_norm`, the
  equation normalizers) are now `sv_simp` (`LeanModels/Sv/CombCoreSimp.lean`): `simp` with the ambient simp set minus
  every `@[simp]` tag a module of Mathlib or of one of its packages added, built from the environment for that one
  call (no environment extension is modified: theorem bodies elaborate asynchronously) and cached. With no package
  imported it is `simp` itself, so no goal the tactics print changes (the 24-file dump set is byte-identical); with
  `import Mathlib.Tactic` the seven tactic-proved references (`add_n`, `add_proc`, `mul_n`, `mul_wallace`,
  `mul_tree_h`, `mul_tree`, `sbox_bp`) are accepted with the proof unchanged and WITHOUT the player-side
  `sv_core_simp` (`SvGolf.CoreSimp`, kept for a player's own `simp`). `tests/run.py` attacks `mathlib_tactics_*` now
  run without it; `tests/imports/test_allowlist.py` keeps the package-root list of `CombCoreSimp.lean` equal to
  `check.py`'s. README and PROVING say so.
* `CombProcStmt.lean`: a body is a list of segments (`Seg`), each a tree over its own window; `symExec_treeF` runs the
  tree executor over a prefix of earlier windows (`symSubst_apartL` on a list state, `write_frame`, `join_frame`,
  `Expr2.same_self`), and `symExec_body`, `selfReadFree_body`, `combAdmits_body` (the self-read guard over a window
  set: `readsViol_none_ws`, `combViol_treeF`), `lower_body` prove that `Process2.lowerComb` of such a body is the single
  assign of all its windows. `symSubst_apart` and `combViol_tree` are corollaries of the generalized lemmas. No summary,
  template or tactic change: `sv_structure` still refuses a multi-window body (gate c). `Examples/system-verilog/
  comb_multi`: `cell_lowers` for `add_proc_m.sv`'s bit cell at every bit, plus `#guard`s on the real design at `N = 2`.

# [0.1.329] — 2026-11-01

Explicit `edge` now has a packed-concatenation witness:
`always @(edge {a, b})` uses the existing any-value-change registration for the
sampled result. Differential coverage is **601 rows / 581 agree / 0 disagree /
20 recorded refusals**; grammar coverage remains **216 MATCH / 25 REFUSE** in
the current upstream census.

# [0.1.328] — 2026-11-01

Explicit `edge` now has a packed ternary-expression witness:
`always @(edge (sel ? a : b))` uses the existing any-value-change registration
for the sampled result. Differential coverage is **600 rows / 580 agree / 0
disagree / 20 recorded refusals**; grammar coverage remains **216 MATCH / 25
REFUSE** in the current upstream census.

# [0.1.327] — 2026-11-01

Explicit `edge` now has a packed binary-expression witness:
`always @(edge (a | b))` uses the existing any-value-change registration for
the sampled result. Differential coverage is **599 rows / 579 agree / 0
disagree / 20 recorded refusals**; grammar coverage remains **216 MATCH / 25
REFUSE** in the current upstream census.

# [0.1.326] — 2026-11-01

Constant packed bit-select events now have a negedge witness:
`always @(negedge bus[2])` applies the existing sampled-result edge rule to the
selected bit. Differential coverage is **598 rows / 578 agree / 0 disagree /
20 recorded refusals**; grammar coverage remains **216 MATCH / 25 REFUSE** in
the current upstream census.

# [0.1.325] — 2026-11-01

Constant packed part-select events now have a negedge witness:
`always @(negedge bus[3:0])` applies the existing sampled-result edge rule to
the selected vector. Differential coverage is **597 rows / 577 agree / 0
disagree / 20 recorded refusals**; grammar coverage remains **216 MATCH / 25
REFUSE** in the current upstream census.

# [0.1.324] — 2026-11-01

Plain timed controls now retain the explicit `edge` spelling, using the
existing any-value-change registration for packed sampled expressions. The
`always_event_explicit_edge` witness covers four changes. Differential coverage
is **596 rows / 576 agree / 0 disagree / 20 recorded refusals**; grammar
coverage remains **216 MATCH / 25 REFUSE** in the current upstream census.

# [0.1.323] — 2026-11-01

Packed identifier event expressions now have a negedge witness:
`always @(negedge bus)` applies the existing sampled-result edge rule to the
identifier's least-significant bit. Differential coverage is **595 rows / 575
agree / 0 disagree / 20 recorded refusals**; grammar coverage remains **216
MATCH / 25 REFUSE** in the current upstream census.

# [0.1.322] — 2026-11-01

Direct dynamic packed part-select events now have an edge-qualified witness:
`always @(posedge bus[base +: 2])` applies the existing sampled-result edge
rule to the selected vector's least-significant bit. Differential coverage is
**594 rows / 574 agree / 0 disagree / 20 recorded refusals**; grammar coverage
remains **216 MATCH / 25 REFUSE** in the current upstream census.

# [0.1.321] — 2026-11-01

Dynamic packed bit-select events now have an edge-qualified witness:
`always @(negedge bus[idx])` applies the existing sampled-result edge rule to
the selected bit. Differential coverage is **593 rows / 573 agree / 0
disagree / 20 recorded refusals**; grammar coverage remains **216 MATCH / 25
REFUSE** in the current upstream census.

# [0.1.320] — 2026-11-01

Vector bitwise-not event expressions now have an edge-qualified witness:
`always @(posedge ~bus)` applies the existing sampled-result edge rule to the
inverted packed result. Differential coverage is **592 rows / 572 agree / 0
disagree / 20 recorded refusals**; grammar coverage remains **216 MATCH / 25
REFUSE** in the current upstream census.

# [0.1.319] — 2026-11-01

Vector logical-not event expressions now have an edge-qualified witness:
`always @(posedge !bus)` applies the existing sampled-result edge rule to the
scalar logical-not result. Differential coverage is **591 rows / 571 agree / 0
disagree / 20 recorded refusals**; grammar coverage remains **216 MATCH / 25
REFUSE** in the current upstream census.

# [0.1.318] — 2026-11-01

Reduction event expressions now have an edge-qualified witness:
`always @(posedge |bus)` applies the existing sampled-result edge rule to the
scalar reduction. Differential coverage is **590 rows / 570 agree / 0
disagree / 20 recorded refusals**; grammar coverage remains **216 MATCH / 25
REFUSE** in the current upstream census.

# [0.1.317] — 2026-11-01

Packed concatenation events now cover the existing negedge rule, for example
`always @(negedge {a, b})`. The `always_event_concat_negedge` witness checks a
higher-bit-only change and one result-LSB transition. Differential coverage is
**589 rows / 569 agree / 0 disagree / 20 recorded refusals**; grammar coverage
remains **241 witnesses / 210 MATCH / 31 REFUSE**.

# [0.1.316] — 2026-11-01

Chandle event expressions now have an explicit recorded refusal:
`always @(h)` is illegal under IEEE §6.14, and the flat model has no opaque
handle identity. The `event_chandle_refuse` witness pins the boundary.
Differential coverage is **588 rows / 568 agree / 0 disagree / 20 recorded
refusals**; grammar coverage remains **241 witnesses / 210 MATCH / 31 REFUSE**.

# [0.1.315] — 2026-10-31

Packed scalar-condition ternary events now support the existing sampled-result
edge rule, for example `always @(posedge (sel ? a : b))`. The
`always_event_ternary_posedge` witness covers branch selection and result-LSB
edges. Differential coverage is **587 rows / 568 agree / 0 disagree / 19
recorded refusals**; grammar coverage remains **241 witnesses / 210 MATCH / 31
REFUSE**.

# [0.1.314] — 2026-10-31

Edge-qualified packed binary events such as `always @(posedge (a | b))` now
use the sampled result's existing least-significant-bit edge rule. The
`always_event_binary_posedge` witness covers higher-bit-only changes and one
LSB transition. Differential coverage is **586 rows / 567 agree / 0 disagree
/ 19 recorded refusals**; grammar coverage remains **241 witnesses / 210 MATCH
/ 31 REFUSE**.

# [0.1.313] — 2026-10-31

Standalone procedural expression waits such as `@(a ^ b);` inside an
`initial` body now have a recorded loud refusal. The process-level sampled
event path does not yet retain statement continuations or expression wait
registrations. Differential coverage is **585 rows / 566 agree / 0 disagree /
19 recorded refusals**; grammar coverage remains **241 witnesses / 210 MATCH /
31 REFUSE**.

# [0.1.312] — 2026-10-31

Mixed sampled-expression and scalar event lists such as
`always @(a | b or c)` now have a recorded loud refusal. Their registrations
are separate in the current scheduler, and accepting the shape would
undercount wakeups. Differential coverage is **584 rows / 566 agree / 0
disagree / 18 recorded refusals**; grammar coverage remains **241 witnesses /
210 MATCH / 31 REFUSE**.

# [0.1.311] — 2026-10-31

Named-event expressions such as `always @(evt)` now have a recorded loud
boundary and differential witness. The flat scheduler has no event-object
queue or trigger identity, so the construct remains `SignalEventControl:clock`
until that machinery is represented. Differential coverage is **583 rows / 566
agree / 0 disagree / 17 recorded refusals**; grammar coverage remains **240
witnesses / 210 MATCH / 30 REFUSE**.

# [0.1.310] — 2026-10-31

The real-valued event boundary now has a differential witness:
`always @(r)` for a `real` variable is recorded as a loud
`SignalEventControl:clock` refusal because the flat `SvState` has no real
payload or event-equality representation. Differential coverage is **582 rows
/ 566 agree / 0 disagree / 16 recorded refusals**; grammar coverage remains
**240 witnesses / 210 MATCH / 30 REFUSE**.

# [0.1.309] — 2026-10-31

Logical negation of packed vectors is now retained in plain timed event
expressions as a scalar sampled result. The
`always_event_vector_logical_not` witness covers zero/nonzero transitions.
Differential coverage is **581 rows / 566 agree / 0 disagree / 15 recorded
refusals**; grammar coverage remains **240 witnesses / 210 MATCH / 30 REFUSE**.

# [0.1.308] — 2026-10-31

Scalar-condition ternaries with packed branch results are now retained in
plain timed events, with wakeups based on the complete selected vector. The
`always_event_vector_ternary` witness covers both branches. Differential
coverage is **580 rows / 565 agree / 0 disagree / 15 recorded refusals**;
grammar coverage remains **240 witnesses / 210 MATCH / 30 REFUSE**.

# [0.1.307] — 2026-10-31

Packed `&`, `|`, and `^` results are now retained in plain timed event
expressions, with wakeups based on the complete result vector. The
`always_event_vector_binary` witness covers an unchanged result and two
changed results. Differential coverage is **579 rows / 564 agree / 0 disagree
/ 15 recorded refusals**; grammar coverage remains **240 witnesses / 210 MATCH
/ 30 REFUSE**.

# [0.1.306] — 2026-10-31

Bitwise inversion over packed vectors is now retained in plain timed event
expressions (`always @(~bus)`). The sampled evaluator compares the complete
unary result; `always_event_vector_unary` covers two result changes while
logical `!` remains scalar. Differential coverage is **578 rows / 563 agree /
0 disagree / 15 recorded refusals**; grammar coverage remains **240 witnesses /
210 MATCH / 30 REFUSE**.

# [0.1.305] — 2026-10-31

Plain timed events now retain direct dynamic packed part-selects such as
`always @(bus[base +: 2])` when the base is one identifier. The existing
sampled-expression registration observes source-bit and base changes through
the selected vector; computed bases and aggregate elements remain loud. The
`always_event_dynamic_part_select` witness covers both dependencies.
Differential coverage is **577 rows / 562 agree / 0 disagree / 15 recorded
refusals**; grammar coverage remains **240 witnesses / 210 MATCH / 30 REFUSE**.

# [0.1.304] — 2026-10-31

Plain timed events now retain dynamic packed bit-selects such as
`always @(bus[idx])`. The existing sampled-expression registration compares
the selected bit before and after each publication, so bus and index updates
are observed without adding a scheduler path. The
`always_event_dynamic_bit_select` witness covers both dependencies; dynamic
part-selects and aggregate elements remain loud. Differential coverage is
**576 rows / 561 agree / 0 disagree / 15 recorded refusals**; grammar coverage
is **241 witnesses / 210 MATCH / 31 REFUSE** after the named-event syntax
witness is added.

# [0.1.303] — 2026-10-31

Plain timed events now retain packed identifiers such as `always @(bus)` and
`always @(posedge bus)`. The sampled-expression evaluator compares the complete
vector for value changes and applies the existing edge rule to the vector's
least-significant bit. The `always_event_multibit_posedge` witness checks
higher-bit-only changes and one LSB transition; `always_ff` keeps its one-bit
clock contract. Differential coverage is **575 rows / 560 agree / 0 disagree
/ 15 recorded refusals**; the sole event-expression repricer now reports **8
files / 8 spans**; grammar coverage remains **240 witnesses / 210 MATCH / 30
REFUSE**.

# [0.1.302] — 2026-10-31

Edge-qualified constant packed part-select events (`always @(posedge
bus[3:0])`) now use the retained sampled expression and the existing
least-significant-bit edge rule. The `always_event_part_select_posedge`
witness covers a selected-bit 0-to-1 transition; no new scheduler path was
introduced. Differential coverage is **574 rows / 559 agree / 0 disagree / 15
recorded refusals**; grammar coverage remains **240 witnesses / 210 MATCH / 30
REFUSE**.

# [0.1.301] — 2026-10-31

The event-expression boundary now has a differential witness for a singular
unpacked-array element event (`always @(arr[2])`). The flat `SvState` has no
unpacked aggregate element storage, so the extractor records the construct as
`SignalEventControl:clock` and the harness expects a loud refusal until the
aggregate store and sampled event value can be represented together.
Differential coverage is **573 rows / 558 agree / 0 disagree / 15 recorded
refusals**; grammar coverage remains **240 witnesses / 210 MATCH / 30 REFUSE**.

# [0.1.300] — 2026-10-31

Refusal register review, with Thomas's rulings of 2026-10-31 (no semantics change except one extractor refusal).
The string literal `"\x41"` is now a loud `StringLiteral:hex-escape` refusal in the symbolic-tier extractor: the pinned
Yosys 0.53 reads `\xdd` as the letter `x` and the two digits (`"\x41"` is `8'h31` in the scored netlist), while slang,
Icarus and Verilator read it as the byte `8'h41`, so a proof and a score could be about different circuits. New
`docs/sv-tools-split-audit.md` and `harness/sv/tools_split_audit/`: the per-tool table (slang, Yosys, Verilator,
Xcelium, Icarus and the ls-sv model) for every register row whose reason is a split among the tools or a program
the LRM forbids, with the class of each (illegal / only a non-pipeline tool dissents / pipeline split /
nondeterministic). `docs/sv-refusals.json`: policies for the 2026-10-31 rulings (classes ignored while the scored
frontend is Yosys `read_verilog -sv`; a slang-illegal program is rejected; a tools-split refusal needs a split among
the pipeline tools, Icarus-only splits are declared departures; LRM-legal nondeterminism is modelled and the golfer
proves the output deterministic; host access is disallowed; Mathlib is allowed in submissions), the new principle
`P-NO-HOST-ACCESS`, `P-SYNTHESIZABLE` reworded to design tasks, the svGolf host-access rows `sg-host-*` and
`sg-escaped-dollar`, the Mathlib rows, and two known holes (slang analysis-pass errors are not read by the extractor,
and the Lean file of a submission is not covered by the host-access gate). Row categories moved only where the audit
evidence is clear; the rows it is unsure of are listed in the audit page.

# [0.1.299] — 2026-10-31

Proof tactics: the second `sv_comb` fragment, operators (WP-G step 2, S2 and S2d; register `tl-sv-structure-fragment`).
`sv_structure` / `sv_equations` (the generic elaborator and the `always_comb` one) now read unary `~` and `!`, the six
reductions, `&&` and `||`, `==` and `!=` of equal-width operands, and the conditional `c ? a : b`, in assigns and in
`always_comb` bodies. Six new `Sk` skeleton constructors; the Boolean reading equals `Expr2.xfBits` (a `?:` prints as the
`if` an `always_comb` already printed, so `c ? a : b` and `if (c) y = a; else y = b;` give the same equation); the
width rules become `WidthObl` cases through two new structural definitions (`Sk.width`, `Sk.SelfOk`); one combined shape
theorem (`skT_shape`) now proves the five instance facts for the new constructors, and `gate_shape`, `cond_shape`,
`skT_selfWidth` and `low_xfWidth`/`low_xfBits` keep their statements as corollaries (the pin of `skT_selfWidth` gains
`Classical.choice`). Additive signatures: `Sk.low` and `Sk.bit` are unchanged (a dummy operand width and the lemma
`Sk.low_irrel`), so word-level operators can thread the context width once. The knownness theorem is untouched. The
flat-netlist fast path (`CombEqPlain`) decides the new constructors. A multi-bit `?:` or `if` condition leaves a
deliberately false `width_k` goal (write `|v ? a : b`); fill and concat arms and a width conversion of an operand are
refused with named messages (follow-up). `RdOK.ternary` moved from `CombProcLower` to `CombViewThm`. One `#pin_axioms`
block (`CombProcEq.lean`) checks the 80 new lemmas against `propext`, `Classical.choice`, `Quot.sound`. Examples:
`comb_ops` (generic, flat and `always_comb` designs with all operators, a hint pin, eight negative designs pinned
verbatim, a proof). The 24 goal dumps of the existing designs are byte-identical.

# [0.1.292] — 2026-10-31

Ascending dynamic packed part-select `iff` guards such as `iff en[idx +: 2]`
now use the existing `SelectRead` truthiness path. Descending dynamic and
aggregate selectors remain loud. The `always_ff_event_iff_dynamic` witness
covers disabled and enabled clock publications. Differential coverage grows
**556/542/0/14 → 557/543/0/14**; grammar coverage remains **240/212/28**.

# [0.1.291] — 2026-10-31

Constant-index packed-vector `iff` guards such as `iff en[1:0]` now use the
existing `SelectRead` truthiness path. Dynamic indexed and aggregate selectors
remain loud. The `always_ff_event_iff_vector` witness covers disabled and
enabled clock publications. Differential coverage grows **555/541/0/14 →
556/542/0/14**; grammar coverage remains **240/212/28**.

# [0.1.290] — 2026-10-31

Scalar `reset_iff` guards on active-low and active-high asynchronous-reset
events are now retained and sampled at the reset edge. The
`always_ff_async_reset_iff_reset` witness covers disabled and enabled reset
publications. Differential coverage grows **554/540/0/14 → 555/541/0/14**;
grammar coverage remains **240/212/28**.

# [0.1.290] — 2026-10-31

`sv_bridge` no longer loops on a pair it cannot split (WP-P3/P4 follow-up): two sides of different shape (a design that
writes a constant where the arithmetic reads a net, the `drop_carry` negative) are reported as such ("the goal and the
equation have different shapes here", both sides printed) instead of running the elaborator out of heartbeats; its
`congrN` call no longer runs the default-transparency `rfl` that unfolded `boolAt`. Only a failing proof reaches that
path. Pinned in `Examples/system-verilog/comb_bridge/bridge.lean` (`bridge_shape`).

# [0.1.289] — 2026-10-31

Direct scalar bit-select `iff` guards such as `always_ff @(posedge clk iff
en[0] or negedge rst_n)` now use the existing `SelectRead` evaluator. The
`always_ff_async_reset_iff_bit` witness covers disabled clock, unconditional
reset, and enabled clock publications. Part-selects and other indexed guard
forms remain loud. Differential coverage grows **553/539/0/14 → 554/540/0/14**;
grammar coverage remains **240/212/28**.

# [0.1.288] — 2026-10-31

Guarded asynchronous-reset `always_ff` lists now retain a scalar `iff` on the
clock event while keeping the active-low or active-high reset event
unconditional. The `always_ff_async_reset_iff` witness covers disabled clock,
reset, and enabled clock publications through the existing scheduler.
Differential coverage grows **552/538/0/14 → 553/539/0/14**; grammar coverage
remains **240/212/28**.

# [0.1.287] — 2026-10-31

Proof tactics: the multiplier-shaped designs lose their glue (WP-P3/P4). Two NEW modules, additive: `CombBridge`
(`SvState.cell`, the canonical row-major cell `st.boolAt n (rmN W r c)`, and the tactic `sv_bridge e [with h₁, …]`,
which closes a Nat-indexed goal from a raw `eq_*` hypothesis printed by `sv_equations`: it instantiates the
equation, normalizes the row-major index with `rmN_add_col`, and compares goal and instance by congruence with
`omega` on the index leaves; a failure names the index equality it could not prove, the goal's read and the
equation's) and `CombCover` (a first alternative of `sv_cover` for 2-D coverage goals: each writer's witnesses are
solved from the affine equations of the read's row and column, the disjunction is walked with `Classical.em` and the
proof term is built directly, writers the hypotheses alone refute are skipped; a shape it does not read falls back
to the old search, and a goal it reads but cannot prove is reported with the read and the condition each writer
would need). The rank-failure message of the sampling stage appends the read that forms the failing edge
(`rankReadNote`, `CombViewDiag.lean`), and the sampler adds one more value; the five Examples that pin that
message gain one line. Goal dumps of the 24 files that use the tactics are byte-identical (the four probes that
carry the pinned message differ only by the appended line). Examples: `comb_bridge` (the four index shapes, the
failure message, the 2-D cover rule, its error format). Every new theorem has a `#print axioms` pin (at most
`propext`, `Classical.choice`, `Quot.sound`).

# [0.1.284] — 2026-10-31

Symbolic-tier differential rows for the four-state rules the `always_comb` tactics will rely on (WP-G, step 2
groundwork; no semantics change). Eleven new `sem2/wpg_*` designs and `cases2.json` rows (736 → 747): the
procedural `if` with an x/z condition taking the else branch (`wpg_if_x`, `wpg_if_chain`), the conditional
expression with an x condition merging bitwise (`wpg_tern_x`, `wpg_tern_ctx`), `!` against `~` (`wpg_not`), the
six reductions at `1x`/`0x`/`xx`/`zz` (`wpg_red`), `&&`/`||` with an x operand and a deciding operand, scalar and
vector (`wpg_logic`), the last-write-wins order of one body (`wpg_order`), the carry cell as one body
(`wpg_carry`), a partial write (`wpg_partial`), and `wpg_local`, a block-local declaration, which stays a loud
refusal (`unknown statement kind "LocalDecl"`) and is not pinned. Pinned on Xcelium 24.03 (`xcelium_golden.json`
503 → 513 rows, purely additive; 288 cycles, 0 mismatches against the transcription of the ls-sv rules); all ten
pinned rows are XREF-MATCH against the Lean model (`diff_test2.py --golden`), none whitelisted.

# [0.1.287] — 2026-10-31

Scalar logical `iff` guards such as `always_ff @(posedge clk iff en && mode)`
are now retained and evaluated with the existing four-state expression rules.
The `always_ff_event_iff_logic` witness covers a disabled guard followed by an
enabled edge; unsupported calls, selects, and other expressions remain loud.
Differential coverage grows **551/537/0/14 → 552/538/0/14**; grammar coverage
remains **240/212/28**.

# [0.1.286] — 2026-10-31

Scalar equality and inequality `iff` guards such as `always_ff @(posedge clk
iff en == 1'b1)` are now retained and evaluated with the same four-state rules
as process expressions. The `always_ff_event_iff_cmp` witness covers a
disabled edge followed by an enabled comparison; indexed, called, and other
unsupported guards remain loud. Differential coverage grows
**550/536/0/14 → 551/537/0/14**; grammar coverage remains **240/212/28**.

# [0.1.285] — 2026-10-31

Timed `always_ff @(negedge clk iff en)` now retains its scalar guard alongside
the negative-edge clock and filters wake-up before the ordinary NBA body runs.
The `always_ff_event_iff_neg` witness checks a disabled falling edge followed by
an enabled capture and MATCHes; compound guards and guarded reset lists remain
loud. Differential coverage grows **549/535/0/14 → 550/536/0/14**; grammar
coverage remains **240/212/28**.

# [0.1.283] — 2026-10-31

Timed `always_ff @(posedge clk iff en)` now retains its scalar guard on the
positive-edge clock registration and filters wake-up before the ordinary NBA body runs. The
`always_ff_event_iff` witness checks a disabled edge followed by an enabled
capture and MATCHes; compound guards, guarded negative-edge clocks, and guarded
reset lists remain loud.
Differential coverage grows **548/534/0/14 → 549/535/0/14**; grammar coverage
remains **240/212/28**.

# [0.1.282] — 2026-10-31

Plain timed `always` event controls now retain scalar identifier `iff` guards;
the scheduler samples the guard when the adjacent edge is published and keeps
the process suspended when it is false or unknown. The `always_event_iff`
witness exercises a disabled edge followed by an enabled edge and MATCHes;
compound guards and guarded `always_ff` controls remain loud. Differential
coverage grows **547/533/0/14 → 548/534/0/14**; grammar coverage grows
**239/211/28 → 240/212/28**.

# [0.1.281] — 2026-10-31

Plain timed `always @(trigger)` now retains a one-entry any-edge registration
through the same Active/Inactive/NBA slot loop. The `always_event_bare`
witness changes the signal after a delay and MATCHes; clocked `always_ff`
bare controls and `iff` forms remain loud. Differential coverage grows
**546/532/0/14 → 547/533/0/14**; grammar coverage remains **239/211/28**.

# [0.1.280] — 2026-10-31

Plain timed `always @(a or b)` event lists now retain every scalar event and
wake through one multi-event registration in the existing Active/Inactive/NBA
slot loop. The `always_event_list` witness changes one of two listed signals
and MATCHes; conditional, non-scalar, and unsupported clock/reset lists remain
loud. Differential coverage grows **545/531/0/14 → 546/532/0/14** and grammar
coverage grows **239/210/29 → 239/211/28**.

# [0.1.279] — 2026-10-31

Timed `always_ff @(posedge clk or posedge rst)` now retains an active-high
asynchronous reset with its edge polarity and wakes through the existing
Active/Inactive/NBA scheduler. The `always_ff_async_reset_high` witness
matches reset assertion and post-release capture; the initial-only runner
continues to refuse the non-initial process. Differential coverage grows
**544/530/0/14 → 545/531/0/14** and grammar coverage remains **239/210/29**.

# [0.1.278] — 2026-10-31

Proof tactics: flat netlists scale (WP-P3b; register `tl-sv-structure-fragment`). Two NEW modules, additive:
`CombViewPlain` (`Summary.disjObl_of_plain`, `rankObl'_of_plain` for an arbitrary relation `R`,
`autoObl_of_plain`, `inRangeObl_of_plain`, and the `Decidable` instances for `DimNum`/`InR`/`InWin`) and
`CombEqPlain` (`widthObl_of_plain`, `bitReadObl_of_plain`, `coverObl_of_plain` through the decidable
`SrcPlain` and `SrcPlain.srcS`). When EVERY site is plain (no generate loop) and the goal has no free
parameter, `sv_structure` and `sv_equations` decide the closed obligations (`closeByDecide`: the kernel
evaluates them) instead of normalizing them with `simp`, whose cost was quadratic in the number of sites
(113 gates: a failure after 4 minutes, now about 12 s and 122 M heartbeats at the default
`maxHeartbeats 200000`; `sv_equations` 58.6 s to 11.3 s). Such a design leaves no `hauto`/`hin`/`hdisj`/`hrank`
goal and no `width`/`cover_k` goal; any failure (a loop, a parameter, a false statement) restores the state and
takes the old route with the old goals. `sv_equations` also names the equations of a netlist whose last site
drives a bit of a vector (the alias condition is `n ≤` the spine length, not `=`) and every tactic of the
chain runs with `maxRecDepth` raised inside the tactic (`withDeepRec`, `Core.Context`), so a 113-site player
file needs no `set_option`. `sv_cover` closes a coverage goal whose witness is a site (`∃ b, (b = site₀ ∨ …) ∧
…`) by picking the writer by name. The second elaborator `CombProcTactic` gets the same naming and
`withDeepRec` and falls through as before. Goal dumps of the 24 files that use the tactics (6 references and 18
Examples) are byte-identical before and after. Examples: `flat_net` (10-gate netlist: structure, hint, the
`always_comb` last-site naming, a parameterized 26-site adder for `sv_cover`). Every new theorem has a
`#print axioms` pin (at most `propext`, `Classical.choice`, `Quot.sound`). Not covered: the `always_comb`
(lowered) path has no fast path.

# [0.1.277] — 2026-10-31

Timed `always_ff @(negedge clk)` now registers a negative-edge clock in the
existing retained scheduler and re-arms through the ordinary Active/Inactive/
NBA path. The `always_ff_negedge` witness matches two falling-edge captures;
the initial-only runner still refuses the non-initial process. Differential
coverage grows **543/529/0/14 → 544/530/0/14** and grammar coverage remains
**239/210/29**.

# [0.1.276] — 2026-10-31

Timed `always_ff @(posedge clk or negedge rst_n)` now registers its
active-low asynchronous reset with the existing retained scheduler. A reset
negedge wakes the process and commits its nonblocking reset assignment through
the ordinary NBA path; a later clock edge captures the released value. The
`always_ff_async_reset` witness matches the pinned transcript, while the
initial-only path continues to refuse the non-initial process explicitly.
Differential coverage grows **542/528/0/14 → 543/529/0/14** and grammar
coverage remains **239/210/29**.

# [0.1.275] — 2026-10-31

The `always_latch_wake` timed witness now changes enable and data after time
zero, checks the enabled capture, and verifies that the latch holds while
disabled. It exercises the existing inferred-sensitivity wake queue without a
latch-specific scheduler. Differential coverage grows **541/527/0/14 →
542/528/0/14** while grammar coverage remains **239/210/29** and the clean
extraction headline remains **5,901/22,071**.

# [0.1.274] — 2026-10-31

The `always_ff_capture` timed witness now toggles its clock twice and checks both
positive-edge nonblocking captures. This exercises the retained `always_ff`
process through the existing event registration and NBA commit path; no
construct-specific scheduler was added. Differential coverage grows
**540/526/0/14 → 541/527/0/14** while grammar coverage remains **239/210/29**
and the clean extraction headline remains **5,901/22,071**.

# [0.1.273] — 2026-10-31

Timed continuous assignments now retain per-process driver samples and resolve
dynamic whole-net overlaps with strength-free four-state semantics (`z` for no
known driver, equal known values preserved, disagreement or `x` resolving to
`x`). The new `assign_net_resolution` fixture differentially matches the
two-driver `wire` case. Literal/static folds and variable multiple-driver
refusals remain unchanged. Differential coverage grows **539/525/0/14 →
540/526/0/14**; grammar coverage remains **239/210/29** and the generated
coverage page records the unchanged **5,901/22,071** clean extraction census.

# [0.1.272] — 2026-10-31

Proof library and tactics: `always_comb` bodies in the `sv_comb` fragment (WP-G, G2.2; register
`tl-sv-structure-fragment`). Four NEW modules, additive: `CombProcSummary` (the proc-aware summary
`siteOfP?`/`PDesign.summaryP`), `CombProcLower` (`Summary.soundL`: the summary's facts plus the new
`NoSelfRead` obligation give `lowerComb = some d'` and the lowered `Realized`; `driversOk_of_lowered`;
`struct_of_summaryL`/`struct_of_rankL`/`struct_of_lexL`), `CombProcEq` (the skeleton `PSk` with a choice node,
`eq_of_summaryL`: the equation of a procedural site is `st.boolAt n (lo+k) = if c then e1 else e2`, nested) and
`CombProcTactic` (a SECOND elaborator on the existing `sv_structure`, `sv_interface`, `sv_equations` syntax
nodes, tried first, `throwUnsupportedSyntax` unless the goal has the lowered shape `∃ d', (X.sem N).lowerComb =
some d' ∧ CombDesign d' ∧ Acyclic d'`; a refused body logs the planned tactic message and admits the goal, so
the proof fails to build and shows `sorryAx`). Fragment S1: `always_comb`, blocking whole-signal or window
assignments, `if`/`else`/`else if` trees, one written window, no latch, no self-read. NO existing LeanModels
file was edited, so every existing proof elaborates exactly as before (goal dumps of the five svGolf
references are byte-identical with and without the new tactic module); the old and the new chain share
nothing but definitions, and `G22-NOTE.md` (svGolf tree) lists which declarations are copies for a later
consolidation. Examples: `comb_proc` (gen non-vacuity, structure by rank/lexRank/comb-only, equation hint, five
negative designs pinned verbatim). Every theorem has a `#print axioms` pin (at most `propext`,
`Classical.choice`, `Quot.sound`), default heartbeats, no `set_option`. The first user: an adder written with
`always_comb` and `if`/`else`, proved for every width by the existing tactics. Not covered: several windows in
one body, `case`, temporaries, `?:`/`!`/`~` in bodies, `check.py --tactics` probing the lowered shape.

# [0.1.271] — 2026-10-31

Scheduler proof receipts now follow the delivered Active/Inactive behavior:
`#0` fixtures assert Inactive publication, loop transcripts record the live
retained continuations, and the six affected SystemVerilog proof targets
build cleanly after the `$monitor` state extension. The delay, waiting-target,
loop, `always`, and intra-assignment documentation now describe the same
boundary.

Timed conformance now admits literal level-sensitive `wait (condition)`.
Conditions are sampled immediately and rechecked after publication of a
signal they read; false or unknown conditions retain the process continuation
until a later update, while an already-true condition proceeds in Active.
The `wait_accept` differential witness covers delayed publication and
resumption through the existing scheduler loop. Event-triggered waits and
the legacy self-check path remain explicit boundaries.

The `always_comb_double_write_timed` witness now covers two source changes in
one Active process. The existing inferred-sensitivity queue re-runs the comb
body after each publication and settles on the final value.

The generated grammar page was refreshed with the census's deterministic
lexical first-witness rule. It exposes a stale committed page: five generate
rows had previously retained simpler witnesses, while the current first paths
are `comb_proc/add_proc.sv` and correctly refuse on its unrelated continuous
assignments. The page now records the measured **239/210/29**
(witnesses/MATCH/REFUSE) result rather than preserving that stale number.

# [0.1.270] — 2026-10-30

Proof library: the lowering of `always_comb` bodies, first stage (WP-G, G2.1). Two NEW modules,
`LeanModels/Sv/CombProcStmt.lean` and `LeanModels/Sv/CombProc.lean`, additive: nothing imports them yet, no
existing declaration changed, the semantics, the loader and the extractor are untouched. They prove, for
`always_comb` bodies of the first fragment (`begin..end`, whole-signal and window targets, `if`/`else`/`else if`
trees, one written window, no latch, no self-read), what `Design2.lowerComb` does: the self-read guard admits
the body when no read window overlaps the written window (a zero-width window intersection gives
`BWin.subAll = []`, so no symbolic window arithmetic enters), the process lowers to one
`assign {W} = {ifGuard ? .. : ..}` tree, and every hypothesis of that lowering follows from the facts the
`sv_comb` summary already carries (`AccOK`, `RdOK`, `instLhs_acc_w`). Includes the template recognizer
`treeStmt?` with its refusal messages and its inversion `treeStmt?_spec`, and the carry cell of the
`add_proc` design lowered at symbolic `N` and bit `k < N` (`carry_lowers`). Every theorem has a
`#print axioms` pin (at most `propext`, `Classical.choice`, `Quot.sound`), no `set_option` beyond a linter
switch, default heartbeats. The tactics do not use the modules yet; the register entry for procedural
`always_comb` bodies in the fragment is unchanged until they do.
Timed `$monitor` now retains the active registration and samples it in the
Postponed region. The first sample and each changed value emit before queued
`$strobe` output, matching the pinned `scheduler_region_outputs` transcript;
the registration is replaced by a later `$monitor` call. Differential coverage
grows **537/522/0/15 → 537/523/0/14**.

# [0.1.269] — 2026-10-30

The binary XNOR `~^` / `^~` in the symbolic tier (WP-L2; register `ex-xnor`). The extractor refused it
(`BinaryExpression:BinaryXnor`); in a SIGNAL expression it is now lowered to `~(a ^ b)`, the two nodes
the tier already has (`_convert_xnor_expr`; `_convert_binary_expr` gained a `_convert_binary_core` split so
the lowering runs exactly the `^` path). Both spellings are one slang operator and produce the same node.
The lowering is exact: slang converts both operands to the expression's own type first, so the inner `^`
and the outer `~` carry the xnor's context width and signedness; any x/z operand bit gives x and equal
known bits give 1 (IEEE 1800-2023 Table 11-14), and the extension bits of a wider context are
`0 ~^ 0 = 1`. A parameter default, a localparam and a generate condition are symbolic-constant positions:
not lowered, still the loud `BinaryExpression:BinaryXnor`. A signed operand pair assigned to a wider
target stays the tier's `ConversionExpression:width` (as `^` does). The reduction `~^a` was already
admitted; it is pinned by rows now. No LeanModels file changed (nothing in the library rebuilds), and
neither did any committed envelope (all symbolic envelopes re-extract byte-identical). New:
`extractors/sv/test_xnor_lowering.py` (12 tests, 10 fail with the lowering neutered), 13 rows in
`cases2.json` (10 simulated rows against Icarus and new pinned Xcelium traces, 3 refusal rows with their
measurements), fixtures `Examples/system-verilog/sem2/xnor_{bin,red,seq,sgn,sgn_wide,const,genconst}`
with the refusal messages pinned, and `Examples/system-verilog/xnor_n`: for every width the lowered
expression is the bitwise IEEE Table 11-14 (`xnor_vec`, x/z propagation `xnor_vec_unknown`, known
vectors `xnor_known`), the evaluator computes it (`xnor_eval`), and `xnor_n.sem N` is exactly that one
process (`xnor_n_processes`). The sv_comb tactics do not read it (they reject every unary operator; that
is the `~` item of the always_comb work). Register: `ex-xnor` now records the remaining refusal; the
ranked "allowed later" row 4 leaves the table.

# [0.1.268] — 2026-10-30

Genvar step spelled as an assignment (WP-L1; register `le-generate-genvar-step`).
`for (i = 0; i < N; i = i + 1)` was refused ("generate step outside the ++/--
tier") although `i++` was accepted, and the svGolf READMEs told players to write
`i++`. The extractor now lowers the assignment spellings of the +/-1 step
(`g = g + 1`, `g = 1 + g`, `g += 1`, `g = g - 1`, `g -= 1`, parenthesised or
not, with the plain signed 32-bit integer literal 1, in the genvar's own integer
arithmetic) to the SAME `Unary` `++` / `--` node as `g++` / `g--`
(`_genstep`, `_genstep_delta`, `_genstep_one`), so the semantic tier
(`stepDelta`), the family lemmas and the proof tactics are untouched and read
the design exactly as before. Every other assignment step (`g += 2`,
`g = g * 2`, a parameter amount `g = g + K` even where K is 1 at the defaults,
`g = 1 - g`, an unsigned or narrower literal) is the new loud
`GenerateFor:step` Unsupported node, never a guessed stride. No committed
envelope changes (37 symbolic generate-for envelopes re-extract byte-identical;
none holds an assignment step). New: `extractors/sv/test_generate_steps.py` (6
tests, 10 fail with the lowering neutered), 14 rows in `cases2.json` (12 admitted
rows against Icarus and new pinned Xcelium traces, 2 refusal rows), fixtures
`Examples/system-verilog/sem2/gstep_{up,down,nest,stride,param}`, and
`Examples/system-verilog/ripple_step`: the ripple-carry adder of `ripple_add`
written with `i = i + 1`, whose generate items equal `ripple_add`'s
(`gen.lean`) and which `sv_structure` + `sv_equations` prove for every
`N >= 1` unchanged (`ripple_step_correct`). Register: the entry now records the
remaining refusal; the ranked "allowed later" row 18 leaves the table.

# [0.1.267] — 2026-10-30

The timed scheduler now publishes guarded procedural NBA writes back into
Active until a deterministic zero-delay feedback loop settles. The new
`scheduler_zero_delay_convergent` witness matches `N=3`; the unbounded toggle
continues to terminate by fuel and remains a loud refusal. Differential
coverage grows **536/521/0/15 → 537/522/0/15**.
Grammar coverage grows **237/189/48 → 237/190/47** as the unary-bitwise-not
witness now runs through the convergent timed loop.

# [0.1.266] — 2026-10-30

The clock-discipline guard (WP-Q0, refusal-only; `LeanModels/Sv/ClockGuard2.lean`,
the first item S0 of `svgolf/design/sequential/README.md`). The cycle semantics
runs every edge process once per cycle and never reads the clock's value, so a
clocked design whose clock is undriven, tied to a constant, assign-derived (gated),
an internal net, a register, a second clock port, read as data, or whose
asynchronous reset is generated inside the design ran in the model on cycles
where no simulator sees an edge (measured on Xcelium 24.03 and Icarus 12.0: a
gated counter counts only the enabled edges, an undriven or tied clock never
captures). Such a design is now refused by the loader: `Clock:source`,
`Clock:reset`, `Clock:multiple`, `Clock:data-read`, and the existing Hier2
`Instance:clock` is reported at the loader too. The guard sits BESIDE `name.sem`
like the select and alias guards (the recorded instantiation lemmas are stated
for the unguarded family): `load_design_sv2` at the defaults and every probed
point, `probeCheckString`, the differential runner and `PDesign.clockReport`
run it; `Hier2.lean` and every proof file are untouched. Admitted designs prove
what they satisfy (`Design2.clockViolation_source`, `_single`, `_reads`,
`_of_noEdge`). No existing row of the corpus is affected (36 of the 691 rows hold
an edge process, all single-clock and admitted); 18 rows are new (7 admitted
designs against Icarus and new pinned Xcelium traces, 11 refusal rows with the
measurement of what the unguarded model got wrong); 17 fixtures
`Examples/system-verilog/sem2/clk_*` with the refusal messages pinned.
Register: `gu-clock-source`, `gu-clock-reset`, `gu-clock-multiple`,
`gu-clock-data-read` (later, plan SEQ), `le-instance-clock` and `sg-unclocked`
updated.

# [0.1.265] — 2026-10-30

Timed `$strobe` calls now flush through the scheduler's Postponed close after
Active, Inactive, and NBA work settle, so deferred arguments observe the final
value in the time slot. `$monitor` registration remains a loud boundary until
monitor state and change-trigger scheduling are represented. Differential
coverage grows **535/520/0/15 → 536/521/0/15**.

# [0.1.264] — 2026-10-30

The timed scheduler now delivers a procedural `#0` through the Inactive
region of the same time slot. The retained continuation is queued after the
Active pass, and writes from that continuation use the existing publication
queue. The zero-delay loop remains fuel-bounded and loud; postponed and
monitor-region output remain outside the tier. Differential coverage grows
**535/519/0/16 → 535/520/0/15**.

# [0.1.263] — 2026-10-30

Procedural signal publication is now part of the retained scheduler path.
Blocking writes are published after each statement in a timed process block,
and NBA commits publish their changed signals through the same edge and
implicit-sensitivity wake queue. The `@*`/double-change and NBA re-trigger
witnesses now match their pinned transcripts; zero-delay loops, `#0`, and
postponed output remain loud. Differential coverage grows **535/517/0/18 →
535/519/0/16** after the two existing scheduler rows are admitted, and the
grammar census routes `AlwaysImplicit` through the timed runner.

# [0.1.262] — 2026-10-30

Timed conformance now preserves `always_ff` as a distinct positive-edge
process and admits `always_latch` through the dormant implicit-sensitivity
path. Latch bodies run at time zero and wake on read changes while retaining
their value when disabled; procedural edge publication and asynchronous reset
lists remain loud. The new `always_ff_accept` and `always_latch_accept`
witnesses are routed through the timed runner.
Differential coverage grows **533/515/0/18 → 535/517/0/18**; grammar
coverage grows **236/186/50 → 237/188/49** as the `AlwaysFFBlock` and
`AlwaysLatchBlock` witnesses match.

Timed conformance now admits single-driver continuous `assign` processes as
implicit-sensitivity combinational work. The RHS runs at time zero and wakes
again when a read signal changes; dependent assignments use the same Active
queue. Multiple drivers remain loud pending a net-driver table and IEEE
four-state resolution. Differential coverage grows **530/513/0/17 →
533/515/0/18**; grammar coverage grows **236/160/76 → 236/186/50** as
continuous-assignment witnesses move through the timed runner.

# [0.1.260] — 2026-10-30

Timed conformance now admits `always_comb` through inferred implicit
sensitivity. Each process executes once at time zero, becomes dormant, and is
woken by blocking or NBA changes to a read signal; written signals are
excluded, and dependent comb processes propagate through the same scheduler
queue. Four differential witnesses cover blocking wake, NBA wake, dependent
propagation, and sensitivity exclusion. Timing controls inside `always_comb`
remain loud. Differential coverage grows **526/509/0/17 → 530/513/0/17**;
grammar coverage grows **236/159/77 → 236/160/76** as the
`AlwaysCombBlock` witness moves from REFUSE to MATCH.

# [0.1.259] — 2026-10-30

The scheduler core is now pinned before the next concurrent-process rung.
Timed differential witnesses cover blocking-versus-NBA ordering and initial /
`always` interaction, while five IEEE §4 gaps remain explicit loud refusals:
`#0` inactive delivery, procedural edge publication, NBA re-triggering,
double-change sensitivity, and postponed/monitor output regions. Differential
coverage grows **519/507/0/12 → 526/509/0/17**; grammar coverage grows
**235/159/76 → 236/159/77** because the new implicit-event-control witness is
counted as REFUSE.

# [0.1.258] — 2026-10-30

Silent-wrong-value fix in the symbolic extractor (WP-E1): a constant element or
range select through a member of a packed struct or union whose type is a
MULTI-DIMENSIONAL packed array (`p.bytes[2]` over `logic [3:0][7:0] bytes`,
`u.h[1]`, a write to `out_v.b[0]`, `p.bytes[2:1]`, `p.bytes[1][3:0]`) was
lowered in bit units: a one-bit `PartSel` at `member offset + label` (or a window
whose width disagreed with its span), with `hasUnsupported` false. The labels
count elements, so every such select is now the flat window of the selected
elements (`_sym_member_select_window`; nested chains and ascending members
included); run-time, parameter, out-of-range and indexed (`+:`/`-:`) member
labels stay loud. The same release adds the select-lowering invariant
`_sym_select_checked`, applied to every symbolic select and to the legacy select
reads and targets: an emitted width or window that disagrees with the compiler's
type or with the element width the semantic tier reads the base with is the loud
`<ExprKind>:window-mismatch` (it also refuses the constant nested element select
of a three-dimensional 2-state packed array, which was a BitSel of a BitSel read
as one bit). Differential rows `member_elem_struct`, `member_elem_union`,
`member_elem_nested`, `member_elem_target`, `member_elem_shapes` (Xcelium-pinned, 474 pinned rows;
Icarus 12.0 declares a continuous-driver departure on the last) and refusal rows
`member_elem_dyn`, `member_elem_indexed`. The register's known hole "element
select of a packed-array member" is closed and `*:window-mismatch` added. No
committed envelope changed; legacy corpus coverage is unchanged.

# [0.1.257] — 2026-10-30

The scheduler-facing conformance harness now drives plain `always` processes
through the retained Active/Inactive/NBA loop until `$finish` or the bounded
observation budget. The grammar census routes plain `Always` and non-`always_ff`
edge witnesses through this timed runner; `always_ff` remains a separate
boundary. Differential coverage grows **518/506/0/12 → 519/507/0/12** and
grammar coverage grows **235/122/113 → 235/159/76**. The coverage page now
states that the legacy self-check path remains initial-only while timed plain
`always` is admitted.

# [0.1.256] — 2026-10-30

The generated coverage page now leads with the real grammar census and the
sv-tests-2 clean-extraction share. The differential table is labelled as
self-consistency on the selected witness rows, and the initial-only boundary
is stated before the measurements.

# [0.1.255] — 2026-10-30

The legacy differential corpus now carries a compact packed concatenation and
replication witness. Coverage grows **517/505/0/12 → 518/506/0/12**; grammar
coverage grows **235/120/115 → 235/122/113** as both `ConcatenationExpression`
and `MultipleConcatenationExpression` move from continuous-assignment
refusals to admitted initial-process witnesses.

# [0.1.254] — 2026-10-30

The legacy differential corpus now carries a compact four-state power witness
for positive and zero exponents plus unknown base and exponent values. The
existing signed and unsigned power fixtures remain covered alongside it.
Coverage grows **516/504/0/12 → 517/505/0/12**; grammar coverage remains
**235/120/115** because the symbolic continuous-assignment witness is still
the canonical `PowerExpression` row.

# [0.1.253] — 2026-10-30

The legacy differential corpus now carries a compact four-state arithmetic
witness for `+`, `-`, `*`, `/`, and `%`, including an unknown add result.
Coverage grows **515/503/0/12 → 516/504/0/12**; grammar coverage grows
**235/118/117 → 235/120/115** in the regenerated census.

# [0.1.252] — 2026-10-30

The legacy differential corpus now carries a compact four-state comparison
witness for equality, inequality, and relational operators, including unknown
results. Coverage grows **514/502/0/12 → 515/503/0/12**; grammar coverage
remains **235/118/117**.

# [0.1.251] — 2026-10-30

The legacy differential corpus now carries a compact four-state binary-bitwise
witness for `&`, `|`, and `^`, including X-propagating operands. Coverage grows
**513/501/0/12 → 514/502/0/12**; grammar coverage grows
**235/116/119 → 235/118/117**.

# [0.1.250] — 2026-10-30

The legacy differential corpus now carries a compact four-state integral-shift
witness for logical and arithmetic left/right shifts. Coverage grows
**512/500/0/12 → 513/501/0/12**; grammar coverage grows **235/115/120 → 235/116/119**.

# [0.1.249] — 2026-10-30

The legacy differential corpus now carries a compact four-state logical-not
witness, covering zero, one, and unknown operands. Coverage grows
**511/499/0/12 → 512/500/0/12**; grammar coverage remains **235/113/122**.

# [0.1.248] — 2026-10-30

The legacy differential corpus now carries a compact four-state unary
bitwise-not witness, covering known and X/Z-propagating values. Coverage grows
**510/498/0/12 → 511/499/0/12**; grammar coverage remains **235/113/122**.

# [0.1.247] — 2026-10-30

The legacy differential corpus now carries a unary reduction witness for `|`,
`&`, and `^`, including an X-propagating reduction. Coverage grows
**509/497/0/12 → 510/498/0/12**; grammar coverage remains **235/113/122**.

# [0.1.246] — 2026-10-30

The legacy differential corpus now carries a compact unary-minus witness over
known and unknown four-state operands. Coverage grows **508/496/0/12 →
509/497/0/12**; grammar coverage remains **235/113/122**.

# [0.1.245] — 2026-10-30

The legacy differential corpus now carries the four-state unary-plus arithmetic
witness with known, unknown, signed, wide, nested, and concatenated operands.
Coverage grows **507/495/0/12 → 508/496/0/12**; grammar coverage remains
**235/113/122**.

# [0.1.244] — 2026-10-30

The legacy differential corpus now carries a compact logical `&&`/`||`
witness covering true and false scalar outcomes. Coverage grows
**506/494/0/12 → 507/495/0/12**; grammar coverage remains **235/113/122**.

# [0.1.243] — 2026-10-30

The legacy differential corpus now carries a compact scalar conditional
expression witness covering both `?:` branches. Coverage grows
**505/493/0/12 → 506/494/0/12**; grammar coverage remains **235/113/122**.

# [0.1.242] — 2026-10-30

The legacy differential corpus now carries a compact initial-process witness
for exact four-state `===`/`!==` comparisons. Coverage grows
**504/492/0/12 → 505/493/0/12**; grammar coverage remains **235/113/122**.

# [0.1.241] — 2026-10-30

The legacy differential corpus now carries a compact dynamic `inside`
expression witness with variable range endpoints and hit/miss checks. Coverage
grows **503/491/0/12 → 504/492/0/12**; grammar coverage remains
**235/113/122**.

# [0.1.240] — 2026-10-30

The legacy differential corpus now carries a compact ordinary `inside`
expression witness with scalar membership, range hit and miss checks, and a
literal `PASS` transcript. Differential coverage grows **502/490/0/12 →
503/491/0/12**; grammar coverage remains **235/113/122**.

# [0.1.239] — 2026-10-30

The legacy differential corpus now carries a compact typed local `let` witness
with repeated calls and literal `PASS` checks. Differential coverage grows
**501/489/0/12 → 502/490/0/12**; grammar coverage remains **235/113/122**.

# [0.1.238] — 2026-10-30

The legacy differential corpus now carries a compact pure local `let` witness
for default formal binding and reordered named actuals, with literal `PASS`
checks. Differential coverage grows **500/488/0/12 → 501/489/0/12**; grammar
coverage remains **235/113/122**.

# [0.1.237] — 2026-10-30

The legacy differential corpus now carries a compact pure local `let` witness
with repeated calls and literal `PASS` checks. Differential coverage grows
**499/487/0/12 → 500/488/0/12**; grammar coverage remains **235/113/122**.

# [0.1.236] — 2026-10-30

The legacy differential corpus now carries a compact dynamic `case (…) inside`
witness with variable range endpoints, matching and nonmatching paths, and a
literal `PASS` transcript. Differential coverage grows **498/486/0/12 →
499/487/0/12**; grammar coverage remains **235/113/122**.

# [0.1.235] — 2026-10-30

The legacy differential corpus now carries a compact ordinary `case (…) inside`
witness with range membership, first-match selection, and a literal `PASS`
transcript. Differential coverage grows **497/485/0/12 → 498/486/0/12**;
grammar coverage remains **235/113/122**.

# [0.1.234] — 2026-10-30

The legacy differential corpus now carries a compact `casez`/`casex` witness.
The shared first-match wildcard predicates handle Z wildcards and X/Z
wildcards respectively, with a literal `PASS` transcript. Coverage grows
**496/484/0/12 → 497/485/0/12**; grammar coverage remains **235/113/122**.

# [0.1.233] — 2026-10-30

The legacy differential corpus now pins a dynamic `priority if` chain without
a final `else` as a loud `ConditionalStatement:Priority` refusal. The admitted
fallback subset remains sound; no-match diagnostic behavior is not erased.
Coverage grows **495/484/0/11 → 496/484/0/12**; grammar coverage remains
**235/113/122**.

# [0.1.232] — 2026-10-30

The legacy differential corpus now pins a dynamic `unique if` chain as a loud
`ConditionalStatement:Unique` refusal. The admitted literal-equality fallback
subset remains sound; dynamic overlap behavior is not guessed. Coverage grows
**494/484/0/10 → 495/484/0/11**; grammar coverage remains **235/113/122**.

# [0.1.231] — 2026-10-30

The legacy differential corpus now pins a dynamic `unique0 case` label as a
loud `CaseStatement:Unique0` refusal. Literal labels remain admitted where the
no-match path is allowed; dynamic overlap behavior is not guessed. Coverage
grows **493/484/0/9 → 494/484/0/10**; grammar coverage remains
**235/113/122**.

# [0.1.230] — 2026-10-30

The legacy differential corpus now pins a `priority case` without a `default`
as a loud `CaseStatement:Priority` refusal. The no-match diagnostic path stays
explicit instead of being erased by first-match lowering. Coverage grows
**492/484/0/8 → 493/484/0/9**; grammar coverage remains **235/113/122**.

# [0.1.229] — 2026-10-30

The legacy differential corpus now pins a dynamic `unique case … inside`
refusal. Wildcard patterns retain the extractor's `CaseStatement:Unique`
boundary rather than erasing the qualifier or guessing a diagnostic channel.
Coverage grows **491/484/0/7 → 492/484/0/8**; grammar coverage remains
**235/113/122**.

# [0.1.228] — 2026-10-29

The differential corpus now records the existing loud refusal for a
side-effecting `let` expansion (`UnaryExpression:Postincrement`). This keeps
the unsupported expression-order boundary explicit without fabricating a
lowering; coverage grows **490/484/0/6 → 491/484/0/7**.

# [0.1.227] — 2026-10-29

The legacy adapter census now follows the extractor's marked flat-write
lowering for direct integral `$swriteb`, `$swriteo`, and `$swriteh` calls.
Selected and aggregate destinations remain loud. The three adapter-only
residuals fall **1 → 0** each; differential coverage remains **490/484/0/6**.

# [0.1.226] — 2026-10-29

The legacy adapter census now follows the extractor's marked flat-write
lowering for plain literal `$sformat` assignments. Direct integral targets are
admitted after the converter has checked the literal format and width;
selected/aggregate targets and `$swrite` remain loud. Differential coverage
remains **490/484/0/6**; the 1002-file adapter sweep moves **801/201 → 802/200**
and the sole plain `$sformat` residual is cleared.

# [0.1.225] — 2026-10-29

The legacy adapter census now follows the extractor's existing predefined
stdout lowering for `$fdisplay` and `$fwrite`: the converter has already
checked the descriptor, literal format, and argument purity and maps these
calls to the represented `$display`/`$write` state. Other descriptors and
unsupported forms remain loud. Differential coverage remains **490/484/0/6**;
the 1002-file adapter sweep moves **798/204 → 801/201** and both `$fdisplay`
and `$fwrite` adapter residuals fall to zero.

# [0.1.224] — 2026-10-29

The legacy fixed-struct-array ordering lowering now accepts a repeated
`rsort with (...)` (or `sort with (...)`) call when its key matches the
preceding ordering call. The compatibility check now compares the complete
argument-list payload at the correct syntax level; incompatible keys remain
loud. The existing `struct_array_ordering_with_field` envelope is fresh, and
the adapter sweep moves **797/205 → 798/204** with `Call:rsort` falling to
zero; differential coverage remains **490/484/0/6**.

## [0.1.223] — 2026-10-29

The legacy adapter census now recognizes the extractor's
`qualified_fallback_lowered` lowering for `unique if` and `priority if` chains
with explicit fallbacks. Complete chains have no qualifier diagnostic and run
as ordinary adapter control; incomplete or overlapping forms remain loud. The
`pure_qualified_if_fallback_adapter` fixture, adapter regression, generated
envelope, Lean receipt, and differential row cover the admitted form.
Differential coverage grows **489/483/0/6 → 490/484/0/6**; grammar coverage
remains **235/113/122**. On the checked-in **1002-file** SystemVerilog example
sweep (**1001 files before this witness**), the adapter census moves **795 clean
/ 206 partial → 797 clean / 205 partial**; the existing qualified-if fallback
residuals are cleared.

## [0.1.222] — 2026-10-29

The legacy adapter census now follows the extractor's
`coverage_nocov_statement` marker for discarded literal coverage queries. With
no represented coverage database, these calls return the fixed empty-coverage
result and carry no adapter state; dynamic arguments and covergroup-backed
designs remain loud. The `pure_coverage_nocov_statements_adapter` fixture,
adapter regression, generated envelope, Lean receipt, and differential row
cover the admitted forms. Differential coverage grows **488/482/0/6 →
489/483/0/6**; grammar coverage remains **235/113/122**. On the checked-in
**1001-file** SystemVerilog example sweep (**1000 files before this witness**),
the adapter census moves **794 clean / 206 partial → 795 clean / 206 partial**.

## [0.1.221] — 2026-10-29

The legacy adapter census now follows the extractor's
`fseek_stdout_error_statement` and `ftell_stdout_error_statement` markers for
discarded file-position calls on the predefined stdout descriptor. The fixed
error results carry no represented adapter state; dynamic descriptors and
other arguments remain loud. The
`pure_stdout_position_error_statements_adapter` fixture, adapter regression,
generated envelope, Lean receipt, and differential row cover the admitted
forms. Differential coverage grows **487/481/0/6 → 488/482/0/6**; grammar
coverage remains **235/113/122**. On the checked-in **1000-file** SystemVerilog
example sweep (**999 files before this witness**), the adapter census moves
**793 clean / 206 partial → 794 clean / 206 partial**.

## [0.1.220] — 2026-10-29

The legacy adapter census now follows the extractor's
`fopen_invalid_mode_statement` marker for discarded `$fopen` calls with an
invalid literal mode. The rejected call performs no represented filesystem
operation; dynamic modes and valid opens remain loud. The
`pure_fopen_invalid_mode_statements_adapter` fixture, adapter regressions,
generated envelope, Lean receipt, and differential row cover the admitted form.
Differential coverage grows **486/480/0/6 → 487/481/0/6**; grammar coverage
remains **235/113/122**. On the checked-in **999-file** SystemVerilog example
sweep (**998 files before this witness**), the adapter census moves **791 clean
/ 207 partial → 793 clean / 206 partial**; the existing `Call:$fopen`
residual is cleared.

## [0.1.219] — 2026-10-29

The legacy adapter census now follows the extractor's
`floating_string_atoreal_statement` marker for discarded `string.atoreal()`
conversions of source-pure ASCII strings. Dynamic, non-ASCII, and effectful
string histories remain loud. The `pure_string_atoreal_statements_adapter`
fixture, adapter regressions, generated envelope, Lean receipt, and
differential row cover the admitted form. Differential coverage grows
**485/479/0/6 → 486/480/0/6**; grammar coverage remains **235/113/122**. On
the checked-in **998-file** SystemVerilog example sweep (**997 files before
this witness**), the adapter census moves **789 clean / 208 partial → 791
clean / 207 partial**.

## [0.1.218] — 2026-10-29

The legacy adapter census now follows the extractor's
`associative_count_statement`, `associative_exists_statement`, and
`associative_empty_delete_statement` markers for discarded finite associative
`num`/`size` and literal `exists` observations, plus deletes on untouched
associative arrays. Dynamic keys and effectful histories remain loud. The
`pure_associative_count_exists_delete_statements_adapter` fixture, adapter
regressions, generated envelope, Lean receipt, and differential row cover the
admitted forms. Differential coverage grows **484/478/0/6 → 485/479/0/6**;
grammar coverage remains **235/113/122**. On the checked-in **997-file**
SystemVerilog example sweep (**996 files before this witness**), the adapter
census moves **786 clean / 210 partial → 789 clean / 208 partial**.

## [0.1.217] — 2026-10-29

The legacy adapter census now follows the extractor's
`associative_endpoint_statement` and `associative_delete_lowered` markers for
finite integral associative-array `first`/`last` statements and literal-key or
whole-array `delete` operations. Dynamic keys and effectful histories remain
loud. The `pure_associative_endpoint_delete_statements_adapter` fixture,
adapter regression, generated envelope, Lean receipt, and differential row
cover the admitted forms. Differential coverage grows **483/477/0/6 →
484/478/0/6**; grammar coverage remains **235/113/122**. On the checked-in
**996-file** SystemVerilog example sweep (**995 files before this witness**),
the adapter census moves **775 clean / 220 partial → 786 clean / 210 partial**.

## [0.1.216] — 2026-10-29

The legacy adapter census now recognizes pure literal-return function calls:
`literal_function_statement`, `literal_function_return`, and
`empty_function_default`. Calls with pure actuals and known literal/default
results carry no callable state; effectful, computed, output-bearing, and
unsupported calls remain loud. The
`pure_literal_function_values_adapter` fixture, adapter regressions,
generated envelope, Lean receipt, and differential row cover the admitted
forms. Differential coverage grows **482/476/0/6 → 483/477/0/6**; grammar
coverage remains **235/113/122**. On the checked-in 995-file SystemVerilog
example sweep (994 files before this witness), the adapter census moves
**766 clean / 228 partial → 775 clean / 220 partial**;
`SubroutineSymbol:Subroutine` falls **14 → 4** and the pure `seven` call
residuals fall to zero.

## [0.1.215] — 2026-10-29

The legacy adapter census now follows the extractor's `sformatf_statement`
marker for discarded literal integral `$sformatf` calls. The formatted value
is unobserved and carries no represented state; dynamic formats, unsupported
conversions, and effectful operands remain loud. The
`pure_sformatf_statements_adapter` fixture, adapter regressions, generated
envelope, Lean receipt, and differential row cover the admitted forms.
Differential coverage grows **481/475/0/6 → 482/476/0/6**; grammar coverage
remains **235/113/122**. On the checked-in 994-file SystemVerilog example
sweep (993 files before this witness), the adapter census moves **765 clean /
228 partial → 766 clean / 228 partial** and the discarded `$sformatf`
residuals fall to zero.

## [0.1.214] — 2026-10-29

The legacy adapter census now follows the extractor's `clog2_statement`,
`isunbounded_statement`, `signing_statement`, and `time_scale_statement`
markers for discarded scalar metadata queries. Constant `$clog2` and
`$isunbounded`, integral signing casts, and timescale metadata carry no
represented state; effectful and value-position forms remain loud. The
`pure_scalar_metadata_statements_adapter` fixture, adapter regressions,
generated envelope, Lean receipt, and differential row cover the admitted
forms. Differential coverage grows **480/474/0/6 → 481/475/0/6**; grammar
coverage remains **235/113/122**. On the checked-in 993-file SystemVerilog
example sweep (992 files before this witness), the adapter census moves
**760 clean / 232 partial → 765 clean / 228 partial** and the six scalar
metadata query residuals fall to zero.

## [0.1.213] — 2026-10-29

The legacy adapter census now follows the extractor's
`empty_subroutine_call` and `empty_input_task_call` markers. Empty tasks and
functions with pure input actuals have no represented state or output, so
their declarations and discarded calls are erased; nonempty, effectful,
output-bearing, and value-position calls remain loud. The
`pure_empty_subroutine_statements_adapter` fixture, adapter regressions,
generated envelope, Lean receipt, and differential row cover the admitted
forms. Differential coverage grows **479/473/0/6 → 480/474/0/6**; grammar
coverage remains **235/113/122**. On the checked-in 992-file SystemVerilog
example sweep (991 files before this witness), the adapter census moves
**757 clean / 234 partial → 760 clean / 232 partial** and the two empty-call
declaration residuals fall to zero.

## [0.1.212] — 2026-10-29

The legacy adapter census now follows the extractor's `typename_statement`
and `bits_statement` markers for discarded `$typename` and `$bits` calls.
Their expression arguments are not evaluated, while malformed and
value-position forms remain loud. The
`pure_type_width_query_statements_adapter` fixture, adapter regressions,
generated envelope, Lean receipt, and differential row cover the admitted
forms. Differential coverage grows **478/472/0/6 → 479/473/0/6**; grammar
coverage remains **235/113/122**. On the checked-in 991-file SystemVerilog
example sweep (990 files before this witness), the adapter census moves
**754 clean / 236 partial → 757 clean / 234 partial** and the two discarded
type/width query residuals fall to zero.

## [0.1.211] — 2026-10-29

The legacy adapter census now follows the extractor's `zero_size_statement`
marker for discarded `len` and `size` calls on untouched empty string and
queue storage. Initialized, populated, and effectful histories remain loud.
The `pure_zero_size_statements_adapter` fixture, adapter regressions, generated
envelope, Lean receipt, and differential row cover the admitted forms.
Differential coverage grows **477/471/0/6 → 478/472/0/6**; grammar coverage
remains **235/113/122**. On the checked-in 990-file SystemVerilog example
sweep (989 files before this witness), the adapter census moves **752 clean /
237 partial → 754 clean / 236 partial** and the two discarded zero-size query
residuals fall to zero.

## [0.1.210] — 2026-10-29

The legacy adapter census now follows the extractor's
`associative_empty_query_statement` and `associative_empty_endpoint_statement`
markers for discarded `num`, `size`, `first`, and `last` calls on untouched
associative arrays. Populated, dynamic, and effectful histories remain loud.
The `pure_associative_query_statements_adapter` fixture, adapter regressions,
generated envelope, Lean receipt, and differential row cover the admitted
forms. Differential coverage grows **476/470/0/6 → 477/471/0/6**; grammar
coverage remains **235/113/122**. On the checked-in 989-file SystemVerilog
example sweep (988 files before this witness), the adapter census moves **749
clean / 239 partial → 752 clean / 237 partial** and the four discarded empty
associative-query call residuals fall to zero.

## [0.1.209] — 2026-10-29

The legacy adapter census now follows the extractor's
`floating_math_statement` marker for discarded source-pure `$sqrt`, `$pow`,
and `$sin` calls. Effectful, timed, unsupported, and value-position forms
remain loud. The `pure_floating_math_statements_adapter` fixture, adapter
regressions, generated envelope, Lean receipt, and differential row cover the
admitted forms. Differential coverage grows **475/469/0/6 → 476/470/0/6**;
grammar coverage remains **235/113/122**. On the checked-in 988-file
SystemVerilog example sweep (987 files before this witness), the adapter
census moves **747 clean / 240 partial → 749 clean / 239 partial** and the
three discarded floating-math call residuals fall to zero.

## [0.1.208] — 2026-10-29

The legacy adapter census now follows the extractor's `enum_name_statement`
and `enum_numeric_statement` markers for discarded source-pure enum `name`,
`first`, `last`, `num`, `next`, and `prev` calls. Effectful receivers and step
arguments remain loud. The `pure_enum_method_statements_adapter` fixture,
adapter regressions, generated envelope, Lean receipt, and differential row
cover the admitted forms. Differential coverage grows **474/468/0/6 →
475/469/0/6**; grammar coverage remains **235/113/122**. On the checked-in
987-file SystemVerilog example sweep (986 files before this witness), the
adapter census moves **744 clean / 242 partial → 747 clean / 240 partial** and
the six discarded enum-method call residuals fall to zero.

## [0.1.207] — 2026-10-29

The legacy adapter census now follows the extractor's `string_query_statement`
marker for discarded source-pure `len`, `getc`, `atoi`, `atobin`, `compare`,
and `icompare` calls. Unknown, effectful, and dynamic string histories remain
loud. The `pure_string_query_statements_adapter` fixture, adapter regressions,
generated envelope, Lean receipt, and differential row cover the admitted
forms. Differential coverage grows **473/467/0/6 → 474/468/0/6**; grammar
coverage remains **235/113/122**. On the checked-in 986-file SystemVerilog
example sweep (985 files before this witness), the adapter census moves **742
clean / 243 partial → 744 clean / 242 partial** and the six discarded string
query call residuals fall to zero; the separate untouched-empty `len` case
remains on its `zero_size_statement` boundary.

## [0.1.206] — 2026-10-29

The legacy adapter census now follows the extractor's
`dimension_query_statement` marker for discarded fixed packed and unpacked
dimension queries: `$size`, `$high`, `$left`, `$right`, `$low`, `$increment`,
`$dimensions`, and `$unpacked_dimensions`. Dynamic, selected, and effectful
operands remain loud. The `pure_dimension_query_statements_adapter` fixture,
adapter regressions, generated envelope, Lean receipt, and differential row
cover the admitted forms. Differential coverage grows **472/466/0/6 →
473/467/0/6**; grammar coverage remains **235/113/122**. On the checked-in
985-file SystemVerilog example sweep (984 files before this witness), the
adapter census moves **740 clean / 244 partial → 742 clean / 243 partial** and
the eight discarded dimension-query call residuals fall to zero.

## [0.1.205] — 2026-10-29

The legacy adapter census now follows the extractor's `array_query_statement`
and `array_reduction_statement` markers for discarded fixed-array `min`,
`max`, `unique`, `unique_index`, `sum`, `product`, `and`, `or`, and `xor`
calls, including source-pure `with` clauses. Dynamic or effectful histories
and clauses remain loud. The `pure_array_query_statements_adapter` fixture,
adapter regressions, generated envelope, Lean receipt, and differential row
cover the admitted forms. Differential coverage grows **471/465/0/6 →
472/466/0/6**; grammar coverage remains **235/113/122**. On the checked-in
984-file SystemVerilog example sweep (983 files before this witness), the
adapter census moves **736 clean / 247 partial → 740 clean / 244 partial** and
the 13 discarded array-query call residuals fall to zero.

## [0.1.204] — 2026-10-29

The legacy adapter census now follows the extractor's `bit_query_statement`
marker for discarded literal and source-pure named-history calls to
`$countbits`, `$countones`, `$onehot`, `$onehot0`, and `$isunknown`. Computed,
dynamic, and effectful operands remain loud. The
`pure_bit_query_statements_adapter` fixture, adapter regressions, generated
envelope, Lean receipt, and differential row cover the admitted forms.
Differential coverage grows **470/464/0/6 → 471/465/0/6**; grammar coverage
remains **235/113/122**. On the checked-in 983-file SystemVerilog example
sweep (982 files before this witness), the adapter census moves **733 clean /
249 partial → 736 clean / 247 partial** and the ten discarded bit-query call
residuals fall to zero.

## [0.1.203] — 2026-10-29

The legacy adapter census now follows the extractor's existing source-pure
statement markers for discarded `$itor`, `$bitstoreal`, `$bitstoshortreal`,
`$rtoi`, `$realtobits`, and `$shortrealtobits` conversions. Effectful or
unsupported operands remain loud. The `pure_real_conversion_statements_adapter`
fixture, adapter regressions, generated envelope, Lean receipt, and differential
row cover the admitted forms. Differential coverage grows **469/463/0/6 →
470/464/0/6**; grammar coverage remains **235/113/122**. On the checked-in
982-file SystemVerilog example sweep (981 files before this witness), the
adapter census moves **723 clean / 258 partial → 733 clean / 249 partial** and
the 12 discarded-conversion call residuals fall to zero.

## [0.1.202] — 2026-10-29

The legacy adapter census now follows the extractor's existing inert
`pure_diagnostic` markers for monitor toggles, VCD controls, static SDF and
time-format calls, and the null `$system` task. Dynamic or effectful arguments
remain loud. The `pure_diagnostic_markers_adapter` fixture, adapter
regressions, generated envelope, Lean receipt, and differential row cover the
admitted forms. Differential coverage grows **468/462/0/6 → 469/463/0/6**;
grammar coverage remains **235/113/122**. On the checked-in 943-file
SystemVerilog example sweep, the adapter census moves **688 clean / 254
partial → 698 clean / 245 partial** and the 15 pure-diagnostic call residuals
fall to zero.

## [0.1.201] — 2026-10-29

The legacy adapter census now follows the extractor's inert lowering for bare
`$asserton`, `$assertoff`, and `$assertkill` tasks. These assertion controls
carry no represented self-check state; argumented forms remain loud. The
`assertcontrol_tasks_adapter` fixture, adapter regression, generated envelope,
Lean receipt, and differential row cover the admitted shape. Differential
coverage grows **467/461/0/6 → 468/462/0/6**; grammar coverage remains
**235/113/122**. On the checked-in 942-file SystemVerilog example sweep, the
adapter census moves **686 clean / 255 partial → 688 clean / 254 partial** and
the three bare assertion-control residuals fall to zero.

## [0.1.200] — 2026-10-29

The legacy adapter census now follows the extractor's inert lowering for
literal and source-pure `$assertcontrol` diagnostics. These controls carry no
self-check assertion state, while dynamic controls remain loud. The
`assertcontrol_adapter` fixture, adapter regressions, generated envelope, Lean
receipt, and differential row cover the admitted shape. Differential coverage
grows **466/460/0/6 → 467/461/0/6**; grammar coverage remains **235/113/122**.
On the checked-in 941-file SystemVerilog example sweep, `Call:$assertcontrol`
residuals fall **3 → 0** (686 clean / 255 partial).

## [0.1.199] — 2026-10-29

The legacy adapter census now follows the extractor's flat-cell lowering for
procedural untagged unpacked structs. A declaration is admitted only when its
conversion produces `Var`/`Empty` cells; unsupported fields and aggregate
boundaries remain loud. The `struct_decl_adapter` fixture, adapter regression,
generated envelope, Lean receipt, and differential row cover the family.
Differential coverage grows **465/459/0/6 → 466/460/0/6**; grammar coverage
remains **235/113/122**. On the checked-in 940-file SystemVerilog example
sweep, `VariableDeclStatement:type` residuals fall **2 → 0** (682 clean / 258
partial).

## [0.1.198] — 2026-10-29

The legacy adapter census now follows the extractor's flat-cell lowering for
procedural fixed unpacked arrays. A declaration is admitted only when its
conversion produces `Var`/`Empty` cells; unsupported leaves and aggregate
boundaries remain loud. The `fixed_array_decl_adapter` fixture, adapter
regression, generated envelope, Lean receipt, and differential row cover the
family. Differential coverage grows **464/458/0/6 → 465/459/0/6**; grammar
coverage remains **235/113/122**. On the checked-in 939-file SystemVerilog
example sweep, `VariableDeclStatement:type` residuals fall **12 → 2** (679
clean / 260 partial).

## [0.1.197] — 2026-10-29

The legacy adapter census now follows the extractor's finite dynamic-array
lowering. A procedural dynamic-array declaration with a source-pure constant
extent is admitted when the converter produces only flat `Var`/`Empty` cells;
symbolic extents and dynamic target operations remain loud. The
`dynamic_extent_adapter` fixture, adapter regression, generated envelope, Lean
receipt, and differential row cover the family. Differential coverage grows
**463/457/0/6 → 464/458/0/6**; grammar coverage remains **235/113/122**. On
the checked-in 938-file SystemVerilog example sweep, `VariableDeclStatement:type`
residuals fall **20 → 12** (671 clean / 267 partial).

## [0.1.196] — 2026-10-29

The legacy adapter census now follows the extractor's compile-time erasure for
malformed integral packed-dimension declarations. Rejected declarations, with
direct literal initializers recovered from their source spelling, allocate no
self-check cells; effectful initializers and value uses remain loud. The
`invalid_dimension_adapter` fixture, adapter regression, generated envelope,
Lean receipt, and differential row cover the family. Differential coverage
grows **462/456/0/6 → 463/457/0/6**; grammar coverage remains **235/113/122**.
The checked-in 937-file SystemVerilog example sweep remains at **20**
`VariableDeclStatement:type` residuals.

## [0.1.195] — 2026-10-29

The legacy adapter census now follows the extractor's declaration-only path
for zero-size dynamic-array declarations. `new[0]` and empty assignment
patterns create no flat self-check cells, while nonzero allocations and later
value uses remain loud. The `empty_dynamic_decl_adapter` fixture, adapter
regression, generated envelope, Lean receipt, and differential row cover the
family. Differential coverage grows **461/455/0/6 → 462/456/0/6**; grammar
coverage remains **235/113/122**. The checked-in 936-file SystemVerilog
example sweep remains at **20** `VariableDeclStatement:type` residuals.

## [0.1.194] — 2026-10-29

The legacy adapter census now treats the first string argument to represented
`$display` and `$write` calls as their format string. Escape spellings are
consumed by the existing formatter before ordinary expression walking, while
dynamic or unsupported value arguments remain loud. The
`display_format_escape_adapter` fixture, adapter regression, generated
envelope, Lean receipt, and differential row cover the family. Differential
coverage grows **448/442/0/6 → 449/443/0/6**; grammar coverage remains
**233/111/122**. The temporary public sv-tests audit remains **364 clean / 437
partial / 111 include skips**; the clean-file
`StringLiteral:named-control-escape` residual falls **1 → 0**, while adapter
unlockables remain **7**.

## [0.1.193] — 2026-10-29

The legacy adapter census now shares the converter's elaborated parameter
scope when walking expressions. Bounded `inside { ... }` membership with
literal or localparam items therefore reuses the existing literal lowering;
dynamic, effectful, and unsupported membership remains loud. The
`inside_parameter_adapter` fixture, adapter regression, generated envelope,
Lean receipt, and differential row cover the family. Differential coverage
grows **447/441/0/6 → 448/442/0/6**; the regenerated grammar census is
**233/111/122** (the stale pre-rebase page was **221/112/109**). The
temporary public sv-tests audit remains **364 clean / 437 partial / 111 include
skips**, and adapter unlockables rise **6 → 7**.

## [0.1.192] — 2026-10-29

Metadata-only packages now follow the extractor's package routing in the
legacy adapter census. Declaration-only package members, unreferenced package
subroutines, and imports no longer create false `PackageSymbol` residuals;
package storage and referenced subroutines remain loud. The
`package_metadata` fixture, adapter regressions, generated envelope, Lean
receipt, and differential row cover the family. Differential coverage grows
**446/440/0/6 → 447/441/0/6**; grammar coverage remains **221/112/109**. The
temporary public sv-tests audit remains **364 clean / 437 partial / 111 include
skips**, and clean-file package residuals fall from **2 to 0**.

## [0.1.191] — 2026-10-29

The legacy adapter census now applies the extractor's declaration-erasure
predicate to compilation-unit members. Integral and flat struct typedefs, and
their bound enum metadata, no longer produce false `TypeAliasType` or
`TransparentMemberSymbol` residuals; package storage and unsupported aliases
remain loud. The `compilation_unit_typedef` fixture, adapter regression,
generated envelope, Lean receipt, and differential row cover the family.
Differential coverage grows **445/439/0/6 → 446/440/0/6**; grammar coverage
remains **221/112/109**. The temporary public sv-tests audit remains **364
clean / 437 partial / 111 include skips**, while clean-file typedef residuals
fall from **26 to 0**.

## [0.1.190] — 2026-10-29

The legacy adapter census now follows the extractor's exact integral
`Parameter` admission. Elaborated module and compilation-unit integral
parameters are compile-time metadata, and their bound references no longer
create false `ParameterSymbol` residuals; real, string, type, and unresolved
parameter forms remain loud. The `parameter_metadata` fixture, adapter
regressions, generated envelope, Lean receipt, and differential row cover the
family. Differential coverage grows **444/438/0/6 → 445/439/0/6**; grammar
coverage remains **221/112/109**. The temporary public sv-tests audit remains
**364 clean / 437 partial / 111 include skips**; parameter-only adapter
residuals drop from **15 to 6** (`ParameterSymbol` **8→0** and
`ParameterSymbol:Parameter` **7→6**), with **3** sole parameter blockers
remaining.

## [0.1.189] — 2026-10-29

The legacy adapter census now admits `$display`, `$write`, `$finish`, and
`$stop`, whose output and termination effects already have self-check state.
Other system and user calls remain loud. The `statement_call_adapter` fixture,
adapter regressions, generated envelope, Lean receipt, and differential row
cover the family. Differential coverage grows **443/437/0/6 → 444/438/0/6**;
grammar coverage remains **221/112/109**.

## [0.1.188] — 2026-10-29

The legacy adapter census now uses the extractor's existing integral type
admission for local scalar and packed 2-state declarations. These declarations
already lower through static storage or `LocalDecl` with the ordinary `Squash2`
boundary; unsupported local types and effectful initializers remain loud. The
`local_2state_declarations` fixture, adapter regressions, generated envelope,
Lean receipt, and differential row cover the family. Differential coverage
grows **442/436/0/6 → 443/437/0/6**; grammar coverage remains **221/112/109**.

## [0.1.187] — 2026-10-29

The legacy adapter census now follows the extractor's declaration-only path
for integral typedefs, flat integral-struct typedefs, and bound enum metadata.
These compile-time aliases do not allocate self-check state; unsupported
tagged, generic, or otherwise effectful aliases remain loud. The
`typedef_metadata` fixture, adapter regressions, generated envelope, Lean
receipt, and differential row cover the admitted forms. Differential coverage
grows **441/435/0/6 → 442/436/0/6**; grammar coverage remains **221/112/109**.

## [0.1.186] — 2026-10-29

The legacy adapter census now follows the extractor's existing erasure rules
for declaration-only `real`, `realtime`, `shortreal`, `chandle`, and `event`
objects. These opaque declarations have no self-check state slot, while reads,
writes, triggers, and waits remain loud at their existing boundaries. The
`opaque_declarations` fixture, adapter regressions, generated envelope, Lean
receipt, and differential row cover the family. Differential coverage grows
**440/434/0/6 → 441/435/0/6**; grammar coverage grows **220/111/109 →
221/112/109**.

## [0.1.185] — 2026-10-29

The legacy adapter now recognizes source-pure ASCII string histories while
measuring the self-check surface: literal concatenation and constant
replication assignments can feed later `%s` observations without a false
`VariableSymbol:2state` or `NamedValueExpression:2state` residual. Unknown,
effectful, timed, and non-ASCII histories remain loud. The
`string_concat_replication_ops` fixture, adapter regressions, generated
envelope, Lean receipt, and differential row cover both §11.4.12.2 forms.
Differential coverage grows **439/433/0/6 → 440/434/0/6**.

## [0.1.184] — 2026-10-29

Finite fixed unpacked arrays of ASCII `string` literals now support exact
element reads in `foreach`, `while`, and `do…while` loops. Constant reads and
source-pure dynamic indices reuse packed literals and ternaries; writes,
aliases, dynamic or non-ASCII initializers, and aggregate forms remain loud.
The `fixed_string_array_loops` fixture, extractor regressions, generated
envelope, and differential row cover the family. Differential coverage grows
**438/432/0/6 → 439/433/0/6**.

## [0.1.183] — 2026-10-29

Compilation-unit `parameter` declarations now lower as elaboration metadata in
the legacy self-check tier. Their references use exact elaborated constants,
including packed widths, while compilation-unit variables and unsupported
parameter expressions remain loud. The `compilation_unit_parameter` fixture,
extractor regression, generated envelope, Lean receipt, and differential row
cover the new family. Differential coverage grows **437/431/0/6 → 438/432/0/6**;
grammar coverage is unchanged.

## [0.1.182] — 2026-10-29

Finite fixed unpacked arrays of untagged integral structs now accept complete
positional or keyed element patterns. Each element is flattened through the
existing struct-field cells in declared order, preserving per-field 2-state
startup and conversion. Partial, replicated, effectful, and whole-aggregate
forms remain loud. The `fixed_array_struct_initializer` fixture, extractor
regressions, generated envelope, Lean receipt, and differential row cover the
admitted family. Differential coverage grows **436/430/0/6 → 437/431/0/6**;
grammar coverage is unchanged.

## [0.1.181] — 2026-10-29

Fixed unpacked byte arrays now accept a direct ASCII string literal
initializer. Characters are sampled in declared array order and shorter
literals zero-pad the remaining cells through the existing 2-state boundary.
Dynamic strings, non-ASCII literals, and non-byte element arrays remain loud.
The `fixed_array_string_initializer` fixture, extractor regressions, generated
envelope, Lean receipt, and differential row cover the admitted shape.
Differential coverage grows **435/429/0/6 → 436/430/0/6**; grammar coverage is
unchanged.

## [0.1.180] — 2026-10-29

Fixed unpacked arrays whose leaf is an equal-width untagged union now flatten
to one aliased union cell per element. Union member reads and writes preserve
the existing aliasing semantics, with zero startup for 2-state leaves and the
existing four-state default for four-state leaves. Tagged, mixed-width,
aggregate-initialized, and whole-array forms remain loud. The
`fixed_array_unpacked_union` fixture, extractor regressions, generated
envelope, Lean receipt, and differential row cover the admitted family.
Differential coverage grows **434/428/0/6 → 435/429/0/6**; grammar coverage is
unchanged.

## [0.1.179] — 2026-10-29

Dimension metadata queries now cover direct dynamic arrays and queues when the
current extent is source-pure: unallocated aggregates report the IEEE empty
bounds, and one literal `new[N]` dynamic-array allocation reports its sampled
extent. `$dimensions` and `$unpacked_dimensions` retain the declared rank.
Dynamic allocation sizes, later mutations, aliases, and value uses remain
loud. The `dynamic_dimension_queries` fixture, extractor regressions, Lean
receipt, and differential row cover the admitted family. Differential
coverage grows **433/427/0/6 → 434/428/0/6**.
The fresh all-directory 22,071-file corpus census moves **5,884 clean /
16,120 partial → 5,901 clean / 16,103 partial** with 67 include skips.

## [0.1.178] — 2026-10-29

Declaration-only 2-state arrays combining fixed and dynamic unpacked
dimensions now support metadata queries for their fixed dimensions and full
unpacked rank. Selecting the dynamic dimension, initializing the array, and
value reads or writes remain loud because no dynamic storage is represented.
The `mixed_dimension_queries` fixture, extractor tests, Lean receipt, and
differential row cover the admitted slice. Differential coverage grows
**432/426/0/6 → 433/427/0/6**.

## [0.1.177] — 2026-10-29

`$info`, `$warning`, and `$error` now accept no-format calls whose pure
integral and source-pure ASCII string arguments use synthesized `%d`/`%s`
fields. Their diagnostic stream remains outside the self-check transcript;
opaque and effectful arguments remain loud. The `severity_default_format`
fixture, extractor tests, Lean receipt, and differential row cover the family.
Differential coverage grows **431/425/0/6 → 432/426/0/6**.

## [0.1.176] — 2026-10-29

`$display` and `$write` now accept no-format calls whose arguments are
represented integral values or source-pure ASCII strings, using the IEEE
default decimal or character representation. Unpacked, opaque, and dynamic
values remain loud. The `default_display_format` fixture, extractor tests,
Lean receipt, and differential row cover the new family. Differential coverage
grows **430/424/0/6 → 431/425/0/6**.

## [0.1.175] — 2026-10-29

Scalar and descending packed `wire bit` nets now lower in the legacy
self-check tier. Un-driven cells retain high-impedance net startup; four-state
literal continuous drivers squash `x`/`z` to zero through the existing
two-state boundary. Other net kinds, delays, dynamic drivers, and unsupported
shapes remain loud. The `two_state_net` fixture, extractor tests, Lean receipt,
and differential row cover the family. Differential coverage grows
**429/423/0/6 → 430/424/0/6**.

## [0.1.174] — 2026-10-29

Plain, un-driven user-defined nettypes with four-state integral scalar or
packed-vector data now lower to high-impedance flat cells in the legacy
self-check tier. Resolution functions, continuous drivers, and unsupported
data shapes remain loud. The `user_nettype` fixture, extractor tests, Lean
receipt, and differential row cover the admission and boundaries. Differential
coverage grows **428/422/0/6 → 429/423/0/6**; grammar coverage grows
**219/108/111 → 220/109/111** with a `SyntaxKind.NetTypeDeclaration` witness.

## [0.1.173] — 2026-10-29

Plain, un-driven `trireg` scalar and packed-vector declarations now lower to
high-impedance flat cells in the legacy self-check tier. Charge strength,
delays, declaration drivers, and continuous drivers remain loud because the
envelope has no retained charge state. The `trireg_net` fixture, extractor
tests, Lean receipt, and differential row cover the admission and boundaries.
Differential coverage grows **427/421/0/6 → 428/422/0/6**.

## [0.1.172] — 2026-10-29

Un-driven `tri0` and `tri1` declarations now lower to flat cells initialized
with their implicit pull zero or one in the legacy self-check tier. Driven
forms remain loud because pull-strength resolution is outside the envelope.
The `pull_net` fixture, extractor tests, Lean receipt, and differential row
cover both values and the driven refusal boundary. Differential coverage grows
**426/420/0/6 → 427/421/0/6**.

## [0.1.171] — 2026-10-29

Un-driven `wand`, `wor`, `triand`, and `trior` declarations now lower to
high-impedance flat cells in the legacy self-check tier. Existing literal
driver resolution remains available; dynamic, strengthened, and unsupported
multi-driver forms remain loud. The `wired_net` fixture, extractor tests, Lean
receipt, and differential row cover the family. Differential coverage grows
**425/419/0/6 → 426/420/0/6**.

## [0.1.170] — 2026-10-29

Un-driven `tri` declarations now lower to flat cells initialized with repeated
high-impedance bits in the legacy self-check tier. Driven nets retain the
existing literal-driver admission or remain loud when strength resolution is
needed. The `tri_net` fixture, extractor tests, Lean receipt, and differential
row cover the new boundary. Differential coverage grows **424/418/0/6 →
425/419/0/6**.

## [0.1.169] — 2026-10-28

Un-driven `supply0` and `supply1` declarations now lower to flat cells with
repeated zero or one initializers in the legacy self-check tier. Any
continuous driver remains loud because supply-strength resolution is outside
the envelope. The `supply_net` fixture, extractor tests, Lean receipt, and
differential row cover both values and the driven refusal boundary.
Differential coverage grows **423/417/0/6 → 424/418/0/6**.

## [0.1.168] — 2026-10-28

Direct whole-net aliases now share one legacy flat storage cell when their
module-scope integral nets have equal width and four-state status. Selected,
concatenated, non-net, mismatched, and symbolic alias graphs remain loud. The
`net_alias` fixture, extractor tests, Lean receipt, and differential row cover
the admission. Differential coverage grows **422/416/0/6 → 423/417/0/6**;
grammar coverage grows **218/107/111 → 219/108/111**.

## [0.1.167] — 2026-10-28

Literal concatenations are now accepted as format arguments for the legacy
output and quiet severity tasks. Only source-pure string pieces are folded;
dynamic and non-string formats remain loud. The `literal_format_concat`
fixture, extractor regressions, Lean receipt, and differential row cover the
boundary. Differential coverage grows **421/415/0/6 → 422/416/0/6**.

## [0.1.166] — 2026-10-28

Direct blocking copies between untagged packed structs and packed unions now
use the existing flat vector target state. Tagged aggregates and effectful or
unsupported sources remain loud. The `packed_aggregate_copy` fixture, extractor
regressions, generated envelope, Lean receipt, and differential row cover the
boundary. Differential coverage grows **420/414/0/6 → 421/415/0/6**; the
external corpus snapshot is unchanged because its checkout is unavailable.

# SystemVerilog tier changelog

## [0.1.165] — 2026-10-28

The legacy self-check tier now lowers blocking assignments through a finite
sampled dynamic outer unpacked array when its elements have fixed unpacked
integral dimensions. Dynamic selectors expand over the existing flattened
cells; unsampled, nested-dynamic, aggregate, effectful, and scheduled forms
remain loud. The `nested_dynamic_array_target` fixture, extractor tests,
generated envelope, Lean receipt, and differential row cover the boundary.
Differential coverage grows **419/413/0/6 → 420/414/0/6**; grammar coverage
remains **218/107/111**. The sv-tests-2 checkout is unavailable, so the
committed corpus snapshot remains **5,814 clean / 16,186 partial / 67 include
skips**.

## [0.1.164] — 2026-10-28

Discarded pure `$rtoi` calls now lower through the shared floating
source-purity boundary. Read-only real names, literals, and nested pure math
calls are admitted; effectful, timed, unsupported, and value-position forms
remain loud. The `discarded_pure_rtoi` fixture, extractor regressions,
generated envelope, Lean receipt, and differential row cover the change.

## [0.1.163] — 2026-10-28

Discarded pure `$realtobits` and `$shortrealtobits` calls now lower through
the shared floating source-purity boundary. Read-only real names, literals,
and nested pure math calls are admitted; effectful, timed, unsupported, and
value-position forms remain loud. The `discarded_pure_real_to_bits` fixture,
extractor regressions, generated envelope, Lean receipt, and differential row
cover the change.

## [0.1.162] — 2026-10-28

Discarded pure floating math calls now lower through the existing source-
purity boundary. `$sqrt`, `$pow`, `$sin`, and nested pure calls are admitted;
effectful, timed, unsupported, and value-position forms remain loud. The
`discarded_pure_floating_math` fixture, extractor regressions, generated
envelope, Lean receipt, and differential row cover the change.

## [0.1.161] — 2026-10-28

Discarded `$itor`, `$bitstoreal`, and `$bitstoshortreal` calls now admit
source-pure integral operands. Read-only names and pure integral expressions
are evaluated and then erased; writes, timing, unsupported expressions, and
wrong-width sources remain loud. The `pure_integral_real_conversions` fixture,
extractor regressions, generated envelope, Lean receipt, and differential row
cover the admitted subset. Differential coverage grows **415/409/0/6 →
416/410/0/6**, and grammar coverage grows **218/106/112 → 218/107/111**.

## [0.1.160] — 2026-10-28

Fixed unpacked integral arrays used as legacy `case (...) inside` labels now
admit cells no wider than the subject. Narrow cells receive the case-context
signed or unsigned extension before source-order membership checks. Dynamic or
nested arrays, effectful elements, nonintegral cells, and over-wide cells remain
loud. The existing array-widening receipt, new standalone fixture, extractor
regressions, generated envelopes, and differential row cover the boundary;
differential coverage grows **414/408/0/6 → 415/409/0/6**, and grammar coverage
grows **218/102/116 → 218/106/112**.

## [0.1.159] — 2026-10-28

Discarded calls to source-declared literal-return functions now accept
compile-time pure integral argument expressions, including unary and binary
literal combinations. Dynamic, effectful, named-state, copy-out, and
unsupported arguments remain loud. The
`literal_function_computed_statement` fixture, extractor regression, generated
envelope, Lean receipt, and differential row cover the admitted subset.

## [0.1.158] — 2026-10-28

Ordinary `unique0 case` chains with distinct integral literal labels now lower
through the first-match case representation. The qualifier's allowed no-match
path means an explicit `default` is unnecessary. Wildcard, `inside`, duplicate,
dynamic, effectful, and scheduler-facing forms remain loud. The `unique0_case`
fixture, extractor regressions, generated envelope, Lean receipt, and
differential row cover the admitted subset.

## [0.1.157] — 2026-10-28

`priority case` and `priority casez` chains with an explicit `default` now
lower through the ordinary first-match case representation because no no-match
diagnostic can occur. Cases without a fallback and effectful, unsupported, or
scheduler-facing forms remain loud. The `priority_case_fallback` fixture,
extractor regressions, generated envelope, Lean receipt, and differential row
cover the admitted subset.

## [0.1.156] — 2026-10-28

Qualified `priority if` chains with an explicit final `else` now lower to the
ordinary first-match conditional because the qualifier has no no-match diagnostic
path. A `unique if` chain is admitted only when its conditions are distinct
literal equalities over one integral variable and the final `else` covers the
no-match path; dynamic, overlapping, and missing-fallback forms remain loud.
The `qualified_if_fallback` fixture, extractor regressions, generated envelope,
Lean receipt, and differential row cover the new subset. Differential coverage
grows **410 rows / 404 matches / 0 disagreements / 6 recorded refusals → 411 /
405 / 0 / 6**; grammar coverage remains **218/101/117**. The fresh 22,067-path
census moves **5,794 → 5,804 clean / 16,206 → 16,196 partial / 67 include
skips**; `ConditionalStatement:Unique` falls **20 → 17** and
`ConditionalStatement:Priority` falls **11 → 4**.

## [0.1.155] — 2026-10-28

The symbolic `sv-0.2` tier now admits signed scalar and packed-vector
declarations when their storage is 2-state. Signedness survives `PDecl`
ingestion and parameter instantiation, while signed comparison expressions use
the existing semantic-tier two's-complement rule. Signed four-state declarations,
enums, arrays, aggregates, and scheduler behavior remain loud. The
`symbolic_signed_2state` fixture, extractor regressions, generated envelope, and
Lean receipt pass; the self-check differential table and legacy corpus census
are unchanged because this is symbolic-mode-only.

## [0.1.154] — 2026-10-28

Blocking writes from pure integral expressions into named `real` or `shortreal`
variables now erase into the existing opaque floating-storage boundary.
Effectful sources, member stores, timed writes, and nonblocking publication
remain loud. The `floating_integral_write` fixture, extractor regressions,
differential row, and Lean receipt pass. Differential coverage grows **409 rows
/ 403 matches / 0 disagreements / 6 recorded refusals → 410 / 404 / 0 / 6**;
grammar coverage remains **218/101/117**. The fresh 22,067-path census moves
**5,792 → 5,794 clean / 16,208 → 16,206 partial / 67 include skips**;
`AssignmentExpression:target` falls **2,693 → 2,679**.

## [0.1.153] — 2026-10-28

Blocking assignments from a named string now sample the source-pure ASCII history at
the assignment point and erase the opaque destination write. The destination keeps
the copied value when the source is subsequently changed; unknown, computed,
timed, nonblocking, and non-ASCII forms remain loud. The
`string_direct_copy` fixture, extractor regressions, sv-tests-2
`6.16--string-assignment-from-literal.sv` receipt, differential row, and Lean
receipt cover the value-copy rule. Differential coverage grows **408 rows / 402
matches / 0 disagreements / 6 recorded refusals → 409 / 403 / 0 / 6**; grammar
coverage remains **218/101/117**. The fresh **22,065-path** census moves **5,790
→ 5,792 clean / 16,208 → 16,206 partial / 67 include skips**;
`CallExpression` falls **2,564 → 2,563** and `NamedValueExpression:2state` falls
**1,269 → 1,267**. The global `AssignmentExpression:target` count remains
**2,693** because these two files also carried other residual blockers in the
previous snapshot.

## [0.1.152] — 2026-10-28

Blocking assignments from a source-pure conditional string expression now erase
after the selected ASCII branch is reconstructed and its condition is proven
as a 0/1 literal history. Unknown, computed, timed, nonblocking, and aliased
forms remain loud. The `conditional_string_assignment` fixture, extractor
regressions, differential row, and Lean receipt pass. Differential coverage
grows **407 rows / 401 matches / 0 disagreements / 6 recorded refusals → 408 /
402 / 0 / 6**; grammar coverage remains **218/101/117**. The fresh 22,067-path
census moves **5,791 → 5,792 clean / 16,209 → 16,208 partial / 67 include
skips**; `AssignmentExpression:target` falls **2,694 → 2,693** and
`NamedValueExpression:2state` falls **1,270 → 1,269**.

## [0.1.151] — 2026-10-28

Empty automatic tasks with input-only formals now erase at the call site after
their actuals pass the pure-expression boundary. Effectful actuals, output,
inout, ref, defaulted, and nonempty task forms remain loud. The
`empty_input_task` fixture, extractor regressions, differential row, and Lean
receipt pass. Differential coverage grows **406 rows / 400 matches / 0
disagreements / 6 recorded refusals → 407 / 401 / 0 / 6**; grammar coverage
changes **218/100/118 → 218/101/117**. The fresh 22,067-path census moves
**5,790 → 5,791 clean / 16,210 → 16,209 partial / 67 include skips**;
`ExpressionStatement:CallExpression` falls **2,677 → 2,675** and
`SubroutineSymbol:Subroutine` falls **1,469 → 1,466**.

## [0.1.150] — 2026-10-28

The symbolic `sv-0.2` tier now admits unsigned integral 2-state scalar and
packed-vector declarations. `PDecl.twoState` survives ingestion,
`Design2` applies zero startup and x/z-to-zero input conversion, and
`Expr2.squash2` evaluates assignment-boundary conversions. Aggregate,
object, string/real, handle, event, and signed symbolic forms remain loud.
The `symbolic_two_state` envelope, semantic-tier proof receipt, and extractor
regressions cover the new path. The self-check differential table and legacy
corpus census are unchanged because this item is symbolic-mode-only.

## [0.1.149] — 2026-10-28

Automatic functions with a single pure literal assignment to their implicit
scalar return variable now lower at the call site, including discarded calls.
Effectful bodies, nonliteral histories, and output or aliasing formals remain
loud. The `automatic_implicit_function_return` fixture, extractor regressions,
differential row, and Lean receipt pass. Differential coverage grows **405 rows
/ 399 matches / 0 disagreements / 6 recorded refusals → 406 / 400 / 0 / 6**.
The fresh 22,067-path census moves **5,789 → 5,790 clean / 16,211 → 16,210
partial / 67 include skips**; `CallExpression` falls **2,565 → 2,564**.

## [0.1.148] — 2026-10-28

Static functions with a single literal assignment to their implicit return
variable now lower at the call site, including an untyped function whose return
type is implicitly `logic`. Discarded calls use the same lowering. Automatic
implicit-return functions, effectful bodies, and nonliteral histories remain
loud; explicit-return automatic literal functions retain their existing path.
The `implicit_function_return` fixture, extractor regressions, differential row,
and Lean receipt pass. Differential coverage grows **404 rows / 398 matches /
0 disagreements / 6 recorded refusals → 405 / 399 / 0 / 6**. The external
sv-tests-2 checkout gained two paths during measurement, so the fresh snapshot
is **22,067 paths: 5,789 clean / 16,211 partial / 67 include skips** versus
**22,065: 5,785 / 16,213 / 67** previously; after accounting for those two
new clean paths, this item contributes **+2 clean / -2 partial**, and
`CallExpression` falls **2,567 → 2,565**.

## [0.1.147] — 2026-10-28

Procedural `event` declarations are now inert metadata for the time-zero
self-check state, so a pure `$typename(event)` string query can run while event
waits and triggers remain loud. The `typename_event_declaration` fixture,
extractor regression, differential row, and Lean receipt pass. Differential
coverage grows **403 rows / 397 matches / 0 disagreements / 6 recorded refusals
→ 404 / 398 / 0 / 6**; the fresh 22,065-path census moves **5,784 → 5,785
clean / 16,214 → 16,213 partial**, with `VariableSymbol:2state` falling
**2,105 → 2,101**.

## [0.1.146] — 2026-10-28

Scalar string `.len()` and `.compare()` observations now ignore IEEE
1800-2023 §6.16 NUL-character writes, which leave the string unchanged.
Nonzero indexed writes and dynamic or aliased histories remain loud. The
`string_null_query_observations` fixture, extractor regression, differential row,
and Lean receipt pass. Differential coverage grows **402 rows / 396 matches /
0 disagreements / 6 recorded refusals → 403 / 397 / 0 / 6**; the fresh
22,065-path census moves **5,782 → 5,784 clean / 16,216 → 16,214 partial**,
with `CallExpression` falling **2,569 → 2,567**.

## [0.1.145] — 2026-10-28

Scalar string `.len()`, `.substr()`, and `.compare()` observations now replay
source-pure concatenation and replication histories. Dynamic and direct aliased
histories remain loud. The `string_concat_query_observations` fixture,
extractor regression, differential row, and Lean receipt pass. Differential
coverage grows **401 rows / 395 matches / 0 disagreements / 6 recorded
refusals → 402 / 396 / 0 / 6**; the fresh 22,065-path census moves **5,779 →
5,782 clean / 16,219 → 16,216 partial**, with `CallExpression` falling
**2,572 → 2,569**.

## [0.1.144] — 2026-10-28

Source-pure literal and query histories now replay exact scalar
`string.compare()` and `string.icompare()` results. Direct named-string
aliases, dynamic or effectful histories, and non-ASCII values remain loud. The
`string_compare_observations` fixture, extractor regression, differential row,
and Lean receipt pass. Differential coverage grows **400 rows / 394 matches /
0 disagreements / 6 recorded refusals → 401 / 395 / 0 / 6**; the fresh
22,065-path census remains **5,779 clean / 16,219 partial**.

## [0.1.143] — 2026-10-28

Direct scalar `.len()` and `.substr()` observations now replay exact ASCII
values from literal and source-pure string query histories. Direct named-string
copies, dynamic or effectful histories, and non-ASCII values remain loud. The
`string_query_observations` fixture, extractor regression, differential row,
and Lean receipt pass. Differential coverage grows **399 rows / 393 matches /
0 disagreements / 6 recorded refusals → 400 / 394 / 0 / 6**; the fresh
22,065-path census moves **5,743 → 5,779 clean / 16,255 → 16,219 partial**,
with `CallExpression` falling **2,606 → 2,572**.

## [0.1.142] — 2026-10-28

Local string declarations now replay exact ASCII values from source-pure
`toupper()`, `tolower()`, `substr()`, `$sformatf`, and `$typename` query
initializers. Named copies, dynamic arguments, effectful histories, and
non-ASCII results remain loud. The `string_query_initializers` fixture,
extractor regression, differential row, and Lean receipt pass. Differential
coverage grows **398 rows / 392 matches / 0 disagreements / 6 recorded
refusals → 399 / 393 / 0 / 6**; the fresh 22,065-path census moves **5,738 →
5,743 clean / 16,260 → 16,255 partial** and `VariableSymbol:2state` falls
**2,112 → 2,105**.

## [0.1.141] — 2026-10-28

Source-pure ASCII string values now replay through multi-operand
concatenations for equality and `%s` display, including replication of named
literal histories. Direct one-operand packed shells, dynamic, controlled,
timed, and non-ASCII histories remain loud. The `string_concat_comparison`
fixture, extractor regression, differential row, and Lean receipt pass.
Differential coverage grows **397 rows / 391 matches / 0 disagreements /
6 recorded refusals → 398 / 392 / 0 / 6**; the fresh 22,065-path census moves
**5,727 → 5,738 clean / 16,271 → 16,260 partial** and
`NamedValueExpression:2state` falls **1,293 → 1,269**.

## [0.1.140] — 2026-10-28

Source-pure `$typename` queries now lower to ASCII packed strings for direct
comparisons and for blocking assignments observed by `.len()`. Effectful and
non-ASCII type-name sources remain loud. The `typename_comparison` fixture,
extractor regression, differential row, and Lean receipt pass. Differential
coverage grows **396 rows / 390 matches / 0 disagreements / 6 recorded
refusals → 397 / 391 / 0 / 6**; the fresh 22,065-path census moves **5,723 →
5,727 clean / 16,275 → 16,271 partial** and `CallExpression` falls **2,613 →
2,606**.

## [0.1.46] — 2026-10-28

The SystemVerilog self-check prerelease now has 395 differential rows: 389
matches, zero disagreements, and 6 recorded refusals. The grammar census has
218 pyslang syntax witnesses: 100 MATCH and 118 REFUSE. The 22,065-path
committed corpus snapshot has 5,719 clean files and 16,279 partial files, with
67 include skips. Since `sv-v0.1.45`, the tier added literal string conversion
for enum `.name()` comparisons, the string-length `putc` boundary, unsigned
packed associative-array endpoints, context-sized associative `exists`
comparisons, and their fixtures, extractor regressions, and Lean receipts.

## [0.1.139] — 2026-10-28

Literal-history `string.toupper()` and `string.tolower()` results now compare
through the existing exact ASCII string path, including preservation of
nonalphabetic characters. Dynamic, controlled, timed, and non-ASCII string
histories remain loud. The fixture, extractor regression, and Lean receipt
pass. Differential coverage grows **395 rows / 389 matches / 0 disagreements /
6 recorded refusals → 396 / 390 / 0 / 6**; the fresh 22,065-path census moves
**5,719 → 5,723 clean / 16,279 → 16,275 partial** and `CallExpression` falls
**2,617 → 2,613**.

## [0.1.138] — 2026-10-28

Enum `.name()` comparisons now accept the elaborated propagated conversion
around ASCII string literals, preserving their packed bytes for the existing
self-check equality path. Direct names, `first()`/`last()` chains, and the
empty result for an invalid enum value are covered by the fixture, extractor
regression, and Lean receipt. Differential coverage grows **394 rows / 388
matches / 0 disagreements / 6 recorded refusals → 395 / 389 / 0 / 6**; the
fresh 22,065-path census moves **5,703 → 5,719 clean / 16,295 → 16,279
partial**.

## [0.1.137] — 2026-10-28

Finite literal-key associative-array `exists(index)` results now participate in
equality and case-equality expressions with IEEE 1800-2023 §7.9.3 context
sizing: the unsigned one-bit presence result is zero-extended to the larger
operand. Dynamic keys, aliases, and aggregate histories remain loud. The
fixture, extractor regression, and Lean receipt pass. Differential coverage
grows **393 rows / 387 matches / 0 disagreements / 6 recorded refusals → 394 /
388 / 0 / 6**; the fresh 22,065-path census moves **5,699 → 5,703 clean /
16,299 → 16,295 partial**, removing four `BinaryExpression:width` blockers.

## [0.1.136] — 2026-10-28

Source-pure finite associative arrays with unsigned packed integral index
aliases now replay `first` and `last` endpoint history according to IEEE
1800-2023 §7.8.4's unsigned ordering. Dynamic keys, controls, timing, and
aggregate forms remain loud. The fixture, extractor regression, and Lean
receipt pass. Differential coverage grows **392 rows / 386 matches / 0
disagreements / 6 recorded refusals → 393 / 387 / 0 / 6**; the fresh
22,065-path census moves **5,698 → 5,699 clean / 16,300 → 16,299 partial**
and `ExpressionStatement:CallExpression` falls **2,678 → 2,677**.

## [0.1.135] — 2026-10-28

Source-pure `string.putc` calls whose index is the receiver's literal
`s.len()` now replay as the IEEE 1800-2023 §6.16.2 out-of-range no-op. Dynamic,
aliased, controlled, timed, and non-ASCII forms remain loud. The fixture,
extractor regression, and Lean receipt pass. Differential coverage grows
**391 rows / 385 matches / 0 disagreements / 6 recorded refusals → 392 / 386 /
0 / 6**; the fresh 22,065-path census moves **5,697 → 5,698 clean /
16,301 → 16,300 partial** and `ExpressionStatement:CallExpression` falls
**2,679 → 2,678**.

## [0.1.134] — 2026-10-28

Source-pure `itoa`, `bintoa`, `octtoa`, and `hextoa` calls now replay literal
integral arguments as exact unpadded ASCII decimal, binary, octal, and
lower-case hexadecimal string replacements, including signed renderings.
Dynamic, unknown, aliased, control-dependent, and unsupported forms remain
loud. The fixture, extractor regressions, and Lean receipt pass. Differential
coverage grows **390 rows / 384 matches / 0 disagreements / 6 recorded
refusals → 391 / 385 / 0 / 6**; the fresh 22,065-path census moves **5,684 →
5,697 clean / 16,314 → 16,301 partial** and
`ExpressionStatement:CallExpression` falls **2,694 → 2,679**.

## [0.1.45] — 2026-10-28

The SystemVerilog self-check surface now has 390 differential rows: 384
matches, zero disagreements, and 6 recorded refusals. The grammar census has
218 pyslang syntax witnesses: 100 MATCH and 118 REFUSE. The 22,065-path
committed corpus snapshot has 5,684 clean files and 16,314 partial files, with
67 include skips. The latest rungs extend finite associative-array presence,
endpoint, streaming, compound-assignment, and dimension-history observations;
dynamic, scheduler-owned, and aggregate forms outside the flat representation
remain loud.

## [0.1.133] — 2026-10-28

Discarded finite associative-array `exists(index)` calls now erase as pure
presence observations after the literal-key finite-cell validator succeeds.
Dynamic keys, aliases, controls, timing, and other aggregate uses remain
loud. The fixture, extractor regressions, and Lean receipt pass. Differential
coverage grows **389 rows / 383 matches / 0 disagreements / 6 recorded
refusals → 390 / 384 / 0 / 6**; the fresh 22,065-path census remains **5,684
clean / 16,314 partial** with 67 include skips.

## [0.1.132] — 2026-10-28

Untouched integral-key associative arrays now return all-`x` values from
`$low` and `$high`, matching IEEE 1800-2023 §20.7 and composing with
`$isunknown` and zero `$size`. Populated, dynamic, aliased, controlled, and
timed histories remain loud. The fixture, extractor regression, and Lean
receipt pass. Differential coverage grows **388 rows / 382 matches / 0
disagreements / 6 recorded refusals → 389 / 383 / 0 / 6**. The fresh
22,065-path census moves **5,681 → 5,684 clean / 16,317 → 16,314 partial**;
`CallExpression:dimension:argument` falls **37 → 34**.

## [0.1.131] — 2026-10-28

System associative-array dimension queries now replay source-pure finite
integral-key histories: `$left`, `$right`, `$low`, `$high`, `$increment`, and
`$size` report populated bounds, integral-index metadata, and exact counts after
writes and deletes. Dynamic, string-key, controlled, timed, and empty low/high
forms remain loud. The fixture, extractor regression, and Lean receipt pass.
Differential coverage grows **387 rows / 381 matches / 0 disagreements / 6
recorded refusals → 388 / 382 / 0 / 6**. The fresh 22,065-path census moves
**5,674 → 5,681 clean / 16,324 → 16,317 partial**; `AssignmentExpression:target`
falls **2,702 → 2,695** and `CallExpression:dimension:argument` falls **44 →
37**.

## [0.1.130] — 2026-10-28

`$size` now observes source-pure finite integral-key associative-array
histories through the same presence replay as `.num()` and `.size()`, including
compound writes and `delete`. Untouched and cleared arrays return zero; fixed
array queries keep their declared-dimension path, and dynamic or string-key
forms remain loud. The fixture, extractor regression, and Lean receipt pass.
Differential coverage grows **386 rows / 380 matches / 0 disagreements / 6
recorded refusals → 387 / 381 / 0 / 6**. The fresh 22,065-path census moves
**5,670 → 5,674 clean / 16,328 → 16,324 partial**; `AssignmentExpression:target`
falls **2,706 → 2,702** and `CallExpression:dimension:argument` falls **48 →
44**.

## [0.1.129] — 2026-10-28

Finite source-pure associative arrays now replay compound assignments at
literal selectors and immutable literal-key bindings. Their flat cells retain
the read-modify-write value and presence, so later `num()`/`size()` calls see
the exact distinct-key count. Dynamic or controlled selectors, aliases, timing,
and unsupported operators remain loud. The fixture, extractor regressions, and
Lean receipt pass. Differential coverage grows **385 rows / 379 matches /
0 disagreements / 6 recorded refusals → 386 / 380 / 0 / 6**. The fresh
22,065-path census moves **5,668 → 5,670 clean / 16,330 → 16,328 partial**;
`CallExpression` falls **2,619 → 2,617**.

## [0.1.128] — 2026-10-28

Integral-key finite associative arrays now lower source-pure `next(index)` and
`prev(index)` histories, selecting the nearest present key on the requested
side and preserving the zero/unchanged-index miss behavior. Dynamic keys,
aliases, and timed or control-dependent histories remain loud. The new fixture,
extractor regressions, and Lean receipt pass. Differential coverage grows
**384 rows / 378 matches / 0 disagreements / 6 recorded refusals → 385 / 379 /
0 / 6**. The fresh 22,065-path census moves **5,661 → 5,668 clean /
16,337 → 16,330 partial**; `AssignmentExpression:target` falls **2,721 →
2,706**.

## [0.1.127] — 2026-10-28

Right streaming now admits finite source-pure integral-key associative arrays
in ascending index order, using the existing flat scalar cells. Dynamic keys,
non-integral aggregates, and other whole-array forms remain loud. The new
fixture, extractor regressions, and Lean receipt pass. Differential coverage
grows **383 rows / 377 matches / 0 disagreements / 6 recorded refusals → 384 /
378 / 0 / 6**. The fresh 22,065-path census moves **5,646 → 5,661 clean /
16,352 → 16,337 partial**; `AssignmentExpression:target` falls **2,744 →
2,721**.

## [0.1.126] — 2026-10-28

Discarded integral-key associative-array `first(index)` and `last(index)` calls
now preserve their output-index side effect through a presence-priority chain.
Empty arrays leave the index unchanged; string-key outputs and dynamic
histories remain loud. The new fixture and Lean receipt pass. Differential
coverage grows **382 rows / 376 matches / 0 disagreements / 6 recorded
refusals → 383 / 377 / 0 / 6**. The committed 22,065-path census remains
**5,646 clean / 16,352 partial** with 67 include skips;
`AssignmentExpression:target` remains **2,744**,
`ExpressionStatement:CallExpression` **2,710**, and `CallExpression` **2,635**.
Grammar coverage remains **218 / 97 / 121**.

## [0.1.125] — 2026-10-28

Blocking assignments from integral-key associative-array `first(index)` and
`last(index)` now use a presence-priority chain. They return one and update
the index variable to the least or greatest present literal key; empty arrays
return zero and leave the index unchanged. String-key endpoint outputs and
dynamic or unsupported histories remain loud. The new fixture and Lean receipt
pass. Differential coverage grows **381 rows / 375 matches / 0 disagreements /
6 recorded refusals → 382 / 376 / 0 / 6**. The committed 22,065-path census
remains **5,646 clean / 16,352 partial** with 67 include skips;
`AssignmentExpression:target` remains **2,744**,
`ExpressionStatement:CallExpression` **2,710**, and `CallExpression` **2,635**.
Grammar coverage remains **218 / 97 / 121**.

## [0.1.124] — 2026-10-28

Blocking associative-array `delete(key)` and whole-array `delete()` calls now
replay finite literal-key history. Key deletes restore element defaults and
clear presence; whole-array deletes clear every known cell, so later reads,
`exists`, and `num()`/`size()` queries observe the deletion. Dynamic keys,
aliases, timed/control-dependent calls, and unknown aggregate operations remain
loud. The new fixture and Lean receipt pass. Differential coverage grows
**380 rows / 374 matches / 0 disagreements / 6 recorded refusals → 381 / 375 /
0 / 6**. The committed 22,065-path census remains **5,646 clean / 16,352
partial** with 67 include skips; `AssignmentExpression:target` remains
**2,744**, `ExpressionStatement:CallExpression` **2,710**, and
`CallExpression` **2,635**. Grammar coverage remains **218 / 97 / 121**.

## [0.1.123] — 2026-10-28

Blocking associative-array `num()` and `size()` queries now replay the number
of distinct literal integral or ASCII string keys written before the query.
Repeated writes do not increase the count; dynamic keys, aliases, deletes,
whole-array operations, timed/control-dependent writes, and other aggregate
methods remain loud. The new fixture and Lean receipt pass. Differential
coverage grows **379 rows / 373 matches / 0 disagreements / 6 recorded
refusals → 380 / 374 / 0 / 6**. The fresh 22,065-path census moves **5,637 →
5,646 clean / 16,361 → 16,352 partial** with 67 include skips;
`AssignmentExpression:target` falls **2,751 → 2,744**, while
`ExpressionStatement:CallExpression` remains **2,710** and `CallExpression`
falls **2,645 → 2,635**. Grammar coverage remains **218 / 97 / 121**.

## [0.1.122] — 2026-10-28

Blocking `string.putc(index, character)` calls now replay through source-pure
ASCII string history, including low-byte integral characters and ignored or
out-of-range writes. Dynamic, timed, control-dependent, aliased, and
non-ASCII forms remain loud. The new fixture and Lean receipt pass;
differential coverage grows **378 rows / 372 matches / 0 disagreements / 6
recorded refusals → 379 / 373 / 0 / 6**. The fresh 22,065-path census moves
**5,629 → 5,637 clean / 16,369 → 16,361 partial** with 67 include skips;
`ExpressionStatement:CallExpression` falls **2,722 → 2,710** and
`AssignmentExpression:target` remains **2,751**.

## [0.1.121] — 2026-10-28

Blocking assignments from literal text wrapped around the metadata-only
top-level `$sformatf("%m")` query now replay through source-pure string
history. Nested hierarchy, functions, generated scopes, dynamic formats,
timed writes, and nonblocking publication remain loud. The new fixture and
Lean receipt pass; differential coverage grows **377 rows / 371 matches / 0
disagreements / 6 refusals → 378 / 372 / 0 / 6**. The committed 22,065-path
census remains **5,622 clean / 16,376 partial** with 67 include skips, and
`AssignmentExpression:target` remains **2,757**.

## [0.1.120] — 2026-10-28

Blocking assignments from the metadata-only top-level `$sformatf("%m")` query
now replay the module scope through source-pure string history. Nested
hierarchy, functions, generated scopes, and other dynamic format forms remain
loud. The new fixture and Lean receipt pass; differential coverage grows
**376 rows / 370 matches / 0 disagreements / 6 refusals → 377 / 371 / 0 / 6**.
The committed 22,065-path census remains **5,622 clean / 16,376 partial** with
67 include skips, and `AssignmentExpression:target` remains **2,757**.

## [0.1.119] — 2026-10-28

Blocking assignments from metadata-only `$typename` queries now replay the
resolved ASCII type spelling through source-pure string history. Effectful,
dynamic, timed, and nonblocking forms remain loud. The new fixture and Lean
receipt pass; differential coverage grows **375 rows / 369 matches / 0
disagreements / 6 refusals → 376 / 370 / 0 / 6**. The fresh 22,065-path census
reports **5,622 clean / 16,376 partial** with 67 include skips, and
`AssignmentExpression:target` falls **2,782 → 2,757**.

## [0.1.118] — 2026-10-28

Constant nested subarray references now copy into multidimensional fixed
unpacked integral destinations by ordinal leaf cell. Same-root overlap, dynamic
selections, and effectful sources remain loud. The new fixture and Lean receipt
pass; differential coverage grows **374 rows / 368 matches / 0 disagreements /
6 refusals → 375 / 369 / 0 / 6**. A fresh 22,065-path census reports **5,611
clean / 16,387 partial** with 67 include skips; the target wall remains 2,782
after the corpus revision added six paths.

## [0.1.117] — 2026-10-28

Blocking conditional assignments over multidimensional fixed unpacked integral
arrays now lower each ordinal cell to a source-preserving ternary, including
arrays with differing declared bounds but equal shapes. Nonblocking self-alias
branches remain loud. The new fixture and Lean receipt pass; differential
coverage grows **373 rows / 367 matches / 0 disagreements / 6 refusals → 374 /
368 / 0 / 6**, while the committed census remains **5,602 clean / 16,390
partial** because the shape is absent from the unavailable external checkout.

## [0.1.116] — 2026-10-28

Exact blocking self-copies of multidimensional fixed unpacked integral arrays
now lower to an inert `Empty` path over the flattened cells. Nonblocking,
partial, dynamic, and effectful copies remain loud. The new fixture and Lean
receipt pass; differential coverage grows **372 rows / 366 matches / 0
disagreements / 6 refusals → 373 / 367 / 0 / 6**, while the committed census
remains **5,602 clean / 16,390 partial** because the shape is absent from the
unavailable external checkout.

## [0.1.44] — 2026-10-28

The SystemVerilog self-check surface now has 372 differential rows: 366
matches, zero disagreements, and 6 recorded refusals. The grammar census has
218 pyslang syntax witnesses: 97 MATCH and 121 REFUSE. The 22,059-path
committed corpus snapshot has 5,602 clean files and 16,390 partial files, with
67 include skips. The latest rungs cover multiple literal integral
`$sformatf` conversions and blocking self-aliasing in unpacked structs and
one-dimensional fixed arrays; nonblocking publication and scheduler-owned
forms remain loud.

## [0.1.115] — 2026-10-28

Blocking conditional whole-array assignments with a self-alias branch now
lower each fixed-array cell to a source-preserving ternary. Nonblocking
self-alias branches remain loud because publication is scheduler-visible. The
new fixture and Lean receipt pass; differential coverage grows **371 rows / 365
matches / 0 disagreements / 6 refusals → 372 / 366 / 0 / 6**. The committed
census is unchanged at **5,602 clean / 16,390 partial** because this fixture
shape is absent from the unavailable external checkout.

## [0.1.114] — 2026-10-28

Blocking conditional whole-struct assignments with a self-alias branch now
lower each integral field to a source-preserving ternary. Nonblocking
self-alias branches remain loud because publication is scheduler-visible. The
new fixture and Lean receipt pass; differential coverage grows **370 rows / 364
matches / 0 disagreements / 6 refusals → 371 / 365 / 0 / 6**. The committed
census is unchanged at **5,602 clean / 16,390 partial** because this fixture
shape is absent from the unavailable external checkout.

## [0.1.113] — 2026-10-28

Exact blocking self-copies of flattened integral unpacked structs now lower to
an inert `Empty` path. Nonblocking self-copies remain loud because publication
is scheduler-visible. The new fixture and Lean receipt pass; differential
coverage grows **369 rows / 363 matches / 0 disagreements / 6 refusals → 370 /
364 / 0 / 6**. The committed census is unchanged at **5,602 clean / 16,390
partial** because this fixture shape is absent from the unavailable external
checkout.

## [0.1.112] — 2026-10-28

Exact blocking self-copies of one-dimensional fixed unpacked arrays of
integral unpacked structs now lower to an inert `Empty` path. Nonblocking
self-copies remain loud because publication is scheduler-visible. The new
fixture and Lean receipt pass; differential coverage grows **368 rows / 362
matches / 0 disagreements / 6 refusals → 369 / 363 / 0 / 6**. The committed
census is unchanged at **5,602 clean / 16,390 partial** because this fixture
shape is absent from the unavailable external checkout.

## [0.1.111] — 2026-10-28

Literal `$sformatf` results with multiple integral conversions now replay exact
ASCII text when assigned to strings. Dynamic or nested operands, unsupported
conversion markers, timed forms, and nonblocking writes remain loud. The new
fixture and Lean receipt pass; differential coverage grows **367 rows / 361
matches / 0 disagreements / 6 refusals → 368 / 362 / 0 / 6**, and the fresh
census moves **5,601 → 5,602 clean / 16,391 → 16,390 partial** with
`AssignmentExpression:target` at **2,782**.

## [0.1.110] — 2026-10-28

Literal escaped-percent `$sformatf` results with one integral conversion now
replay exact ASCII text when assigned to strings. Multiple conversions or
escaped percents, dynamic operands, timed forms, and nonblocking writes remain
loud. The new fixture and Lean receipt pass; differential coverage grows **366
rows / 360 matches / 0 disagreements / 6 refusals → 367 / 361 / 0 / 6**, and
the fresh census moves **5,600 → 5,601 clean / 16,392 → 16,391 partial** with
`AssignmentExpression:target` at **2,783**.

## [0.1.109] — 2026-10-28

Integral literal operands of `%s`/`%S` `$sformatf` assignments now replay as
packed printable ASCII bytes when the width is a multiple of eight. Unknown,
non-byte-width, NUL/control, dynamic, timed, and nonblocking forms remain
loud. The new fixture and Lean receipt pass; differential coverage grows **365
rows / 359 matches / 0 disagreements / 6 refusals → 366 / 360 / 0 / 6**, and
the fresh census moves **5,599 → 5,600 clean / 16,393 → 16,392 partial** with
`AssignmentExpression:target` at **2,784**.

## [0.1.108] — 2026-10-28

Literal-prefix/suffix `$sformatf` results with one integral conversion now
replay exact ASCII text when assigned to strings. Decimal, hexadecimal,
binary, octal, and character forms are covered; dynamic operands, multiple
conversions, escaped-percent formats, timed forms, and nonblocking writes
remain loud. The new fixture and Lean receipt pass; differential coverage
grows **364 rows / 358 matches / 0 disagreements / 6 refusals → 365 / 359 / 0 /
6**, and the fresh census moves **5,597 → 5,599 clean / 16,395 → 16,393
partial** with `AssignmentExpression:target` at **2,785**.

## [0.1.107] — 2026-10-28

Zero-width string `$sformatf` results (`%0s`/`%0S`) assigned to strings now
replay exact ASCII text for literal operands and source-pure string history,
including one literal prefix and suffix around the conversion. Dynamic or
non-ASCII operands, additional conversions, timed forms, and nonblocking
writes remain loud. The new fixture and Lean receipt pass; differential
coverage grows **363 rows / 357 matches / 0 disagreements / 6 refusals → 364 /
358 / 0 / 6**, and the fresh 22,059-path census moves **5,596 → 5,597 clean /
16,396 → 16,395 partial** with `AssignmentExpression:target` at **2,787**.

## [0.1.106] — 2026-10-28

Zero-width binary and octal `$sformatf` results (`%0b/%0B` and `%0o/%0O`)
assigned to strings now replay minimal exact text for known integral literals.
Unknown or dynamic operands, timed forms, and nonblocking writes remain loud.
The new fixture and Lean receipt pass; differential coverage is **363 rows / 357
matches / 0 disagreements / 6 recorded refusals**, and the census remains
**5,584 clean / 16,414 partial** with `AssignmentExpression:target` at
**2,810**.

## [0.1.105] — 2026-10-28

Literal integral decimal `$sformatf` results (`%d`, `%D`, `%0d`, `%0D`) assigned
to strings now replay exact decimal text. Unknown or dynamic operands, timed
forms, and nonblocking writes remain loud. The new fixture and Lean receipt
pass; differential coverage is **362 rows / 356 matches / 0 disagreements / 6
recorded refusals**, and the census remains **5,584 clean / 16,414 partial**
with `AssignmentExpression:target` at **2,810**.

## [0.1.104] — 2026-10-28

Literal integral `$sformatf("%o", ...)` and `$sformatf("%O", ...)` results
assigned to strings now replay exact lower-case octal text. Unknown or dynamic
operands, timed forms, and nonblocking writes remain loud. The new fixture and
Lean receipt pass; differential coverage is **361 rows / 355 matches / 0
disagreements / 6 recorded refusals**, and the census remains **5,584 clean /
16,414 partial** with `AssignmentExpression:target` at **2,810**.

## [0.1.103] — 2026-10-28

Literal integral `$sformatf("%b", ...)` and `$sformatf("%B", ...)` results
assigned to strings now replay their exact packed 0/1 text, retaining literal
width. Unknown or dynamic operands, timed forms, and nonblocking writes remain
loud. The new fixture and Lean receipt pass; differential coverage is **360
rows / 354 matches / 0 disagreements / 6 recorded refusals**, and the census
remains **5,584 clean / 16,414 partial** with `AssignmentExpression:target` at
**2,810**.

## [0.1.102] — 2026-10-28

Literal integral `$sformatf("%c", ...)` and `$sformatf("%C", ...)` results
assigned to strings now replay their low-byte ASCII character. Unknown, zero,
non-ASCII/control, dynamic, timed, and nonblocking forms remain loud. The new
fixture and Lean receipt pass; differential coverage is **359 rows / 353
matches / 0 disagreements / 6 recorded refusals**, and the census remains
**5,584 clean / 16,414 partial** with `AssignmentExpression:target` at
**2,810**.

## [0.1.101] — 2026-10-28

Source-pure ASCII `$sformatf("%s", ...)` and `$sformatf("%S", ...)` results
assigned to strings now replay exact text from literal operands or earlier
literal string history. Dynamic operands, unsupported formats, timed forms, and
nonblocking writes remain loud. The new fixture and Lean receipt pass;
differential coverage is **358 rows / 352 matches / 0 disagreements / 6
recorded refusals**, and the census remains **5,584 clean / 16,414 partial**
with `AssignmentExpression:target` at **2,810**.

## [0.1.100] — 2026-10-28

Literal `$sformatf("%h", ...)` and `$sformatf("%H", ...)` results from
integral literals now replay as source-pure ASCII string assignments. Later
comparisons and diagnostics see the exact hexadecimal value; dynamic operands,
other formats, timed forms, and nonblocking writes remain loud. The
`string_sformatf_literal_assignment` fixture and Lean receipt supply the `PASS`
evidence; differential coverage is **357 rows / 351 matches / 0 disagreements
/ 6 recorded refusals**, and the fresh census is **5,584 clean / 16,414
partial** with `AssignmentExpression:target` at **2,810**.

## [0.1.99] — 2026-10-28

Constant-index string-byte assignments from one-byte ASCII literals now replay
the source-pure string history, so later comparisons and `%0s` diagnostics
observe the updated character. Dynamic, out-of-range, multi-byte, timed, and
nonblocking forms remain loud. The `string_index_literal_character` fixture and
Lean receipt supply the `PASS` evidence; differential coverage is **356 rows /
350 matches / 0 disagreements / 6 recorded refusals**, and the fresh census is
**5,582 clean / 16,416 partial** with `AssignmentExpression:target` at
**2,812**.

## [0.1.98] — 2026-10-28

Blocking assignment of the one-byte NUL string literal to a constant-indexed
string character now lowers to the existing §6.16 ignored-write rule. Dynamic,
nonzero, timed, and nonblocking forms remain loud. The
`string_null_literal_character` fixture and Lean receipt supply the `PASS`
evidence; differential coverage is **355 rows / 349 matches / 0 disagreements
/ 6 recorded refusals**, and the fresh corpus census is **5,580 clean / 16,418
partial** with `AssignmentExpression:target` at **2,814**.

## [0.1.97] — 2026-10-28

Source-pure `string.toupper()`, `string.tolower()`, and bounded `substr()`
assignments now use ASCII literal history and fold subsequent comparisons.
Dynamic, aliased, timed, nonblocking, and non-ASCII forms remain loud. The
`string_case_assignment` and `string_substr_assignment` fixtures and Lean
receipts supply the `PASS` evidence; differential coverage is **354 rows / 348
matches / 0 disagreements / 6 recorded refusals** and grammar coverage remains
**218 / 97 / 121**.

## [0.1.96] — 2026-10-28

Blocking literal queue writes followed by an empty queue concatenation now
remain admissible when the only later observation is `.size()`. The
`queue_literal_then_empty_concat` fixture and Lean receipt cover the exact
zero-size history; dynamic or nonliteral writes and queue element observations
remain loud. Differential coverage is **352 rows / 346 matches / 0
disagreements / 6 recorded refusals**; grammar coverage remains **218 / 97 /
121**.

## [0.1.95] — 2026-10-28

The integral power family now has unsigned, signed, and zero-to-negative
self-check rows in the executable differential matrix. All three match their
committed `PASS` declarations. The zero-to-negative case remains a documented
IEEE 1800-2023 §11.4.3 Table 11-4 / Icarus divergence from the separate
reference run. Differential coverage is **351 rows / 345 matches / 0
disagreements / 6 recorded refusals**; grammar coverage remains **218 / 97 /
121**.

## [0.1.94] — 2026-10-28

Exact blocking self-copies of constant subarrays now lower to an `Empty`
no-op, matching the existing whole-array self-copy rule. Nonblocking,
overlapping, dynamic, and nonintegral forms remain loud because their
publication or storage behavior is not erased. The
`fixed_array_subarray_self_copy` fixture and Lean receipt supply the
`PASS` evidence. Differential coverage is now **348 rows / 342 matches / 0
disagreements / 6 recorded refusals**; grammar coverage remains **218 / 97 /
121** and the committed census remains **5,401 clean / 16,597 partial** with
67 include skips.

## [0.1.93] — 2026-10-28

Blocking copies between two disjoint constant subarrays of one fixed
multidimensional integral array now lower to cellwise writes. The extractor
checks that the source and destination cell sets do not overlap, preserving
the complete source snapshot; overlapping, dynamic, timed, and nonblocking
forms remain loud. The `fixed_array_disjoint_subarray_copy` fixture and Lean
receipt supply the `PASS` evidence. Differential coverage is now **347 rows /
341 matches / 0 disagreements / 6 recorded refusals**; grammar coverage
remains **218 / 97 / 121** and the committed census remains **5,401 clean /
16,597 partial** with 67 include skips.

## [0.1.92] — 2026-10-28

Unpacked concatenations assigned to scalar-integral dynamic arrays now admit a
zero-argument function whose complete body assigns one integral literal through
the implicit function name. The call is materialized as one sampled cell while
effectful or state-dependent function operands remain loud. The
`dynamic_array_concat_literal_function` fixture and Lean receipt supply the
`PASS` evidence. Differential coverage is now **346 rows / 340 matches / 0
disagreements / 6 recorded refusals**; grammar coverage remains **218 / 97 /
121** and the committed census remains **5,401 clean / 16,597 partial** with
67 include skips.

## [0.1.91] — 2026-10-28

Source-pure ASCII string history now flows through constant replication and
concatenation writes. A named string with only earlier unconditional blocking
literal writes can be reconstructed for a blocking target and a matching `%s`
diagnostic; computed, control-dependent, timed, nonblocking, and non-ASCII
forms remain loud. The existing `replication/dynamic_string` fixture now
matches `dynamic abab`. Differential coverage is **345 rows / 339 matches / 0
disagreements / 6 recorded refusals**; grammar coverage remains **218 / 97 /
121** and the committed census is unchanged at **5,401 clean / 16,597
partial** with 67 include skips.

## [0.1.90] — 2026-10-28

Blocking assignments of literal integral zero to a constant-indexed string
byte now lower to `Empty`, matching IEEE 1800-2023 §6.16's ignored
null-character rule. Dynamic indices, nonzero values, timed forms, and
nonblocking writes remain loud. The `string_null_character` fixture and Lean
receipt supply the `PASS` evidence. Differential coverage is now **344 rows /
338 matches / 0 disagreements / 6 recorded refusals**; grammar coverage
remains **218 / 97 / 121**. The external census snapshot remains **5,401
clean / 16,597 partial** with 67 include skips.

## [0.1.89] — 2026-10-28

Whole-array continuous assignment now admits a one-dimensional fixed-unpacked
variable source with a complete literal declaration initializer and no later
writes. The extractor expands that immutable source into ordinal per-cell
time-zero writes, including opposite source and destination range directions;
mutable, net, sliced, dynamic, timed, and nonblocking forms remain loud. The
`static_fixed_array_continuous_copy` fixture and Lean receipt supply the
`PASS` evidence. Differential coverage is now **343 rows / 337 matches / 0
disagreements / 6 recorded refusals**; grammar coverage remains **218 / 97 /
121**. The external census snapshot remains **5,401 clean / 16,597 partial**
with 67 include skips.

## [0.1.88] — 2026-10-28

Malformed integral packed-dimension declarations with a direct literal
initializer now follow the same compile-time rejection path as uninitialized
declarations. The initializer is recovered only from the declaration spelling
when pyslang has replaced it with `InvalidExpression`; calls and other
effectful initializers remain loud. The `invalid_packed_dimension_literal`
fixture and Lean receipt supply the `PASS` evidence. Differential coverage is
now **342 rows / 336 matches / 0 disagreements / 6 recorded refusals**;
grammar coverage remains **218 / 97 / 121**. The external census snapshot is
still unavailable in this checkout and remains **5,401 clean / 16,597 partial**
with 67 include skips.

## [0.1.87] — 2026-10-28

Declaration-only integral variables whose packed dimension is rejected during
elaboration now disappear as inert metadata. The narrow `ErrorType` slice
covers malformed ranges such as `bit [3:x]` and `bit [3]`; ordinary 2-state
variables, initialized malformed declarations, and invalid uses remain loud.
The `invalid_packed_dimension_decl` compile-error fixture and Lean receipt
supply the `PASS` evidence. Differential coverage is now **341 rows / 335
matches / 0 disagreements / 6 recorded refusals**; grammar coverage remains
**218 / 97 / 121**. The committed 22,065-file snapshot is externally
unavailable; its prior **5,401 clean / 16,597 partial** counts are unchanged
in this checkout, with 67 include skips.

## [0.1.86] — 2026-10-27

Declarations initialized by `new[0]` or an empty assignment pattern now lower
to inert metadata for both 2-state and 4-state dynamic arrays. Nonzero
allocations and later dynamic-array operations remain loud. Differential
coverage is **340 rows / 334 matches / 0 disagreements / 6 recorded refusals**;
grammar coverage remains **218 / 97 / 121**. The pinned 22,065-file census is
unchanged at **5,401 clean / 16,597 partial** with 67 include skips while the
external corpus checkout is unavailable.

## [0.1.85] — 2026-10-27

Exact whole-array blocking self-copies for one-dimensional fixed unpacked
integral arrays now lower to an `Empty` no-op. Sliced, overlapping, nonblocking,
timed, dynamic, aggregate, and effectful copies remain loud. The
`fixed_array_self_copy` fixture and Lean receipt supply `selfcopy 3 7`.
Differential coverage is now **339 rows / 333 matches / 0 disagreements / 6
recorded refusals**; grammar coverage remains **218 / 97 / 121**. The pinned
22,065-file census remains **5,401 clean / 16,597 partial** with 67 include
skips while the external corpus checkout is unavailable.

## [0.1.84] — 2026-10-27

Whole assignments to a one-dimensional fixed unpacked integral array now admit
source-pure RHS patterns that read the destination itself. The extractor first
captures every RHS cell in local temporaries, then writes the flattened cells,
preserving the complete-RHS-before-store rule. Nested, dynamic, aggregate,
effectful, and width-mismatched aliasing remains loud. The existing
`assignment_patterns/self_alias.sv` fixture now supplies the `self 7 3`
receipt. Differential coverage is now **338 rows / 332 matches / 0
disagreements / 6 recorded refusals**; grammar coverage remains **218 / 97 /
121**. The pinned 22,065-file census remains **5,401 clean / 16,597 partial**
with 67 include skips while the external corpus checkout is unavailable.

## [0.1.83] — 2026-10-27

Unreferenced package functions and tasks are now erased after the elaborated
call graph proves that no `CallExpression.subroutine` targets them. Calls from
modules, imports, other packages and recursive bodies retain the existing
`Package:Subroutine` boundary. The `package_unused_subroutines` fixture and Lean
receipt supply the `PASS` evidence. Differential coverage is now **337 rows /
331 matches / 0 disagreements / 6 recorded refusals**; grammar coverage
remains **218 / 97 / 121**. The pinned 22,065-file census remains **5,401 clean
/ 16,597 partial** with 67 include skips while the external corpus checkout is
unavailable.

## [0.1.82] — 2026-10-27

Unreferenced module-scope functions and tasks are now erased as inert
declarations after the elaborated call graph proves no `CallExpression`
targets them. Referenced, recursive, receiver, DPI, and effectful-call
declarations remain loud because callable frames and external effects are not
represented. The `unused_subroutines` fixture supplies the `PASS` receipt.
Differential coverage is now **336 rows / 330 matches / 0 disagreements / 6
recorded refusals**; grammar coverage remains **218 / 97 / 121**. The pinned
22,065-file census remains **5,401 clean / 16,597 partial** with 67 include
skips while the external corpus checkout is unavailable.

## [0.1.81] — 2026-10-27

Finite multidimensional unpacked integral arrays now admit `foreach` loops
when every dimension is explicitly bound. Dynamic reads and writes expand to
mutually exclusive conditions over the existing flat leaf cells; incomplete,
dynamic, queue, aggregate, and effectful forms remain loud. The
`foreach_nested` fixture supplies the `sum=21` differential receipt.
Differential coverage is now **335 rows / 329 matches / 0 disagreements / 6
recorded refusals**; grammar coverage remains **218 / 97 / 121**. The pinned
22,065-file census is unchanged at **5,401 clean / 16,597 partial** with 67
include skips.

## [0.1.80] — 2026-10-27

One-dimensional fixed integral arrays now render as `%p` diagnostic arguments
through their existing flattened cells. Declared index order and signed
element rendering are preserved; nested, dynamic, effectful, and non-`%p`
aggregate values remain loud. The `array_named_display` fixture covers the
rendered transcript and the nested-array refusal. Differential coverage is now
**334 rows / 328 matches / 0 disagreements / 6 recorded refusals**; the
chapter-only census moves from **5,396 clean / 16,602 partial** to **5,401
clean / 16,597 partial** over 22,065 files, and
`NamedValueExpression:2state` falls **1,473 → 1,462**.

## [0.1.79] — 2026-10-27

Source-pure string equality and relational comparisons now fold for direct
ASCII literals and named strings with earlier unconditional blocking literal
writes. Equality, case equality, inequality, and the four ordered comparisons
produce exact one-bit literals; computed, control-dependent, timed,
nonblocking, dynamic, and non-ASCII histories remain loud. Differential
coverage is now **333 rows / 327 matches / 0 disagreements / 6 recorded
refusals**; the chapter-only census moves from **5,384 clean / 16,614 partial**
to **5,396 clean / 16,602 partial** over 22,065 files, and
`NamedValueExpression:2state` falls **1,488 → 1,473**.

## [0.1.78] — 2026-10-27

Explicit casts from a finite source-pure `real` or `shortreal` to an integral
type now round to the nearest integer, with ties away from zero, before the
ordinary target-width conversion. Direct literals and source-ordered direct
blocking literal histories are admitted; computed, control-dependent, timed,
non-finite, and dynamic real sources remain loud. Differential coverage is
now **332 rows / 326 matches / 0 disagreements / 6 recorded refusals**; the
chapter-only census moves from **5,359 clean / 16,639 partial** to **5,384
clean / 16,614 partial** over 22,065 files, and
`ConversionExpression:Explicit` falls **34 → 9**.

## [0.1.77] — 2026-10-27

Static locals now preserve source order within a procedural scope, allowing a
later closed pure initializer to read an earlier static declaration. Runtime,
effectful, random, environment, cross-scope, and pre-process ordering cases
remain loud. Differential coverage is now **331 rows / 325 matches / 0
disagreements / 6 recorded refusals**. The chapter-only census moves from
**5,331 clean / 16,667 partial** to **5,359 clean / 16,639 partial** over
22,065 files; `StaticLocal:initializer` falls **168 → 140**.

## [0.1.76] — 2026-10-27

Literal-return user functions now accept named integral arguments whose
declaration and earlier writes are direct blocking literals in the time-zero
initial history. Computed, control-dependent, timed, nonblocking, dynamic,
output, inout, and reference arguments remain loud. Differential coverage is
now **330 rows / 324 matches / 0 disagreements / 6 recorded refusals**; the
chapter-only census remains **5,331 clean / 16,667 partial** over 22,065 files.

## [0.1.75] — 2026-10-27

`$timeformat` now accepts a source-pure named integral history for its unit,
precision, and width arguments when no `%t` consumer exists. The call remains
an inert configuration operation in the self-check state; a `%t` consumer,
computed, control-dependent, timed, nonblocking, or dynamic argument remains
loud. Differential coverage grows to **329 rows / 323 matches / 0
disagreements / 6 recorded refusals**, with grammar coverage unchanged at
**218 / 97 / 121**. The root-level witness is outside the chapter walk, so the
census remains **5,331 clean / 16,667 partial** and the statement-call blocker
remains **2,718**.

## [0.1.74] — 2026-10-27

`$assertcontrol` now accepts named integral arguments when their declaration
and earlier blocking writes are direct literals in the time-zero initial
history. The self-check tier has no assertion-control register, so the
validated call remains an inert `Empty`; computed, control-dependent, timed,
nonblocking, and dynamic arguments remain loud. Differential coverage grows
to **328 rows / 322 matches / 0 disagreements / 6 recorded refusals**, with
grammar coverage unchanged at **218 / 97 / 121**. The root-level witness is
outside the chapter walk, so the census remains **5,331 clean / 16,667 partial**
and the statement-call blocker remains **2,718**.

## [0.1.73] — 2026-10-27

Discarded `$countbits`, `$countones`, `$onehot`, `$onehot0`, and
`$isunknown` calls now accept named integral operands whose declaration and
earlier blocking writes are direct literals in the time-zero initial history.
The result is unobserved, so the envelope erases the call after the shared
source-order check; computed, control-dependent, timed, nonblocking, and
dynamic histories remain loud. Differential coverage grows to **327 rows / 321
matches / 0 disagreements / 6 recorded refusals**, with grammar coverage at
**218 / 97 / 121**. The witness is outside the chapter-only corpus walk, so
its **5,331 clean / 16,667 partial** counts and the **2,718** statement-call
blocker are unchanged.

## [0.1.72] — 2026-10-27

The four timed sv-tests-2 `$q_exam` witnesses now lower through a
source-ordered literal-delay replay: codes 2, 4, 5, and 6 report exact tick
statistics for mean interarrival, shortest completed wait, longest current
wait, and average completed wait. The timed receipt drives the existing
`elabTimedDesign`/timer scheduler at 4 and 6 ticks; the time-zero differential
matrix remains 326 rows with 320 matches, no disagreements, and 6 recorded
refusals. The chapter-only census is now **5,331 clean / 16,667 partial** over
22,065 files (67 include skips), and `ExpressionStatement:CallExpression`
falls from 2,722 to 2,718. Dynamic delays, overflow, branches, extra initial
processes, and computed or aliased queue histories remain loud.

## [0.1.71] — 2026-10-27

The self-check surface now has 326 differential rows: 320 matches, zero
disagreements, and 6 recorded refusals. The grammar census remains at 218
pyslang syntax witnesses: 97 MATCH and 121 REFUSE. The chapter-only census
remains at 5,327 clean files and 16,670 partial files with 67 include skips.
`CallExpression` falls from 2,655 to 2,648.
Untimed initial-block `$realtime` now feeds the exact `$rtoi`, `$realtobits`,
and `$shortrealtobits` conversion paths as zero; continuous, scheduled, and
elapsed-time forms remain loud.

## [0.1.70] — 2026-10-27

The self-check surface now has 325 differential rows: 319 matches, zero
disagreements, and 6 recorded refusals. The grammar census remains at 218
pyslang syntax witnesses: 97 MATCH and 121 REFUSE. The chapter-only census
remains at 5,327 clean files and 16,670 partial files with 67 include skips.
The exact real-conversion slices now accept `$itor` over a source-pure named
integral history, while computed, control-dependent, timed, nonblocking,
dynamic, and standalone real-storage forms remain loud.

## [0.1.69] — 2026-10-27

The self-check surface now has 324 differential rows: 318 matches, zero
disagreements, and 6 recorded refusals. The grammar census remains at 218
pyslang syntax witnesses: 97 MATCH and 121 REFUSE. The chapter-only census
remains at 5,327 clean files and 16,670 partial files with 67 include skips.
`$rtoi` now folds a finite named real or short-real after source order proves
only direct literal assignments, preserving exact decimal truncation toward
zero; computed, control-dependent, timed, nonblocking, dynamic, and
out-of-range histories remain loud.

## [0.1.68] — 2026-10-27

The self-check surface now has 323 differential rows: 317 matches, zero
disagreements, and 6 recorded refusals. The grammar census remains at 218
pyslang syntax witnesses: 97 MATCH and 121 REFUSE. The current 22,064-path
chapter census moves to 5,327 clean files and 16,670 partial files with 67
include skips; `CallExpression` falls from 2,656 to 2,655. An untyped mailbox
with one scalar integral literal now admits `try_peek()` into a destination of
a non-equivalent type, returning the required negative status without
consuming or writing mailbox state; aliases, dynamic histories, equivalent
types, and other mailbox methods remain loud.

## [0.1.67] — 2026-10-27

The self-check surface now has 322 differential rows: 316 matches, zero
disagreements, and 6 recorded refusals. The grammar census remains at 218
pyslang syntax witnesses: 97 MATCH and 121 REFUSE. The current 22,064-path
chapter census remains at 5,326 clean files and 16,671 partial files with 67
include skips; the new witness is root-level and outside that walk. Direct
blocking scalar `$dist_uniform(seed, low, high)` assignments now resolve
signed 32-bit bounds from one earlier literal assignment in the same initial
process; computed, reassigned, timed, nonblocking, and value-position forms
remain loud.

## [0.1.66] — 2026-10-27

The self-check surface now has 321 differential rows: 315 matches, zero
disagreements, and 6 recorded refusals. The grammar census remains at 218
pyslang syntax witnesses: 97 MATCH and 121 REFUSE. The current 22,064-path
corpus census has 5,326 clean files and 16,671 partial files with 67 include
skips; `AssignmentExpression:target` falls from 2,844 to 2,842. A direct
scalar-literal queue copied to a differently sized fixed array now lowers the
IEEE 1800-2023 §7.6 run-time mismatch to an immediate `$finish`, preserving
earlier output and preventing a partial copy. Equal-size copies and dynamic,
aliased, or effectful queue histories remain loud.

## [0.1.65] — 2026-10-27

The self-check surface now has 320 differential rows: 314 matches, zero
disagreements, and 6 recorded refusals. The grammar census remains at 218
pyslang syntax witnesses: 97 MATCH and 121 REFUSE. The 22,059-path corpus
snapshot remains at 5,304 clean files and 16,688 partial files with 67 include
skips. Source-ordered scalar-literal mailbox histories now admit `peek()` and
`try_peek()`: both copy the FIFO head without consuming it, and `try_peek()`
also reports the empty-queue result. Dynamic messages, aliases, branches,
empty blocking peeks, and width mismatches remain loud.

## [0.1.64] — 2026-10-27

The self-check surface now has 319 differential rows: 313 matches, zero
disagreements, and 6 recorded refusals. The grammar census remains at 218
pyslang syntax witnesses: 97 MATCH and 121 REFUSE. The 22,059-path corpus
remains at 5,304 clean files and 16,688 partial files with 67 include skips;
`CallExpression` falls from 2,729 to 2,672. Fixed-size bitstream `$bits`
operands are now admitted from their elaborated type without evaluating the
source expression, including increments, assignments, calls, and selected
reads; initialized dynamic-size operands remain loud.

## [0.1.63] — 2026-10-27

The self-check surface now has 318 differential rows: 312 matches, zero
disagreements, and 6 recorded refusals. The grammar census remains at 218
pyslang syntax witnesses: 97 MATCH and 121 REFUSE. The 22,059-path corpus
moves to 5,304 clean files and 16,688 partial files with 67 include skips;
`AssignmentExpression:target` falls from 2,845 to 2,844 files. A source-pure
scalar-literal queue can now copy into a same-count fixed unpacked integral
array left to right; mismatches, aliases, aggregate elements, and scheduled
forms remain loud.

## [0.1.62] — 2026-10-27

The self-check surface now has 317 differential rows: 311 matches, zero
disagreements, and 6 recorded refusals. The grammar census remains at 218
pyslang syntax witnesses: 97 MATCH and 121 REFUSE. The 22,059-path corpus
moves to 5,303 clean files and 16,689 partial files with 67 include skips;
`CallExpression` falls from 2,731 to 2,729. A direct empty queue assignment
after a literal initializer now makes later `size()` queries exactly zero;
nonempty mutations and content reads remain loud.

## [0.1.61] — 2026-10-27

The self-check surface now has 316 differential rows: 310 matches, zero
disagreements, and 6 recorded refusals. The grammar census remains at 218
pyslang syntax witnesses: 97 MATCH and 121 REFUSE. The 22,059-path corpus
remains at 5,301 clean files and 16,691 partial files with 67 include skips;
`VariableSymbol:2state` falls from 2,223 to 2,118 files. A 2-state queue
initialized only by scalar literals now answers `size()` exactly; queue
mutations, content reads, and dynamic initializers remain loud.

## [0.1.60] — 2026-10-27

The self-check surface now has 315 differential rows: 309 matches, zero
disagreements, and 6 recorded refusals. The grammar census remains at 218
pyslang syntax witnesses: 97 MATCH and 121 REFUSE. The 22,059-path corpus
remains at 5,301 clean files and 16,691 partial files with 67 include skips.
The no-argument `$dumpportsflush()` task is admitted as an inert external VCD
flush; argumented port-dump operations remain loud.

## [0.1.59] — 2026-10-27

The self-check surface now has 312 differential rows: 307 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 218
pyslang syntax witnesses: 96 MATCH and 122 REFUSE. The 22,059-path corpus
moves to 5,298 clean files and 16,694 partial files with 67 include skips;
the `CaseStatement:Unique` wall falls from 45 to 41 files. A sound literal
subset of `unique case` is now admitted: duplicate-free integral patterns
with a default arm, or complete coverage of every value for subjects up to
8 bits on a two-state subject. Dynamic, duplicate, incomplete, wildcard,
four-state complete-without-default, `unique0`, and priority forms remain
loud.

## [0.1.58] — 2026-10-27

The self-check surface now has 311 differential rows: 306 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 218
pyslang syntax witnesses: 96 MATCH and 122 REFUSE. The 22,059-path corpus
moves to 5,294 clean files and 16,698 partial files with 67 include skips;
the `ExpressionStatement:CallExpression` wall falls to 2,739. A finite
source-pure pair of literal `for` loops around scalar mailbox `put()`/`get()`
operations now replays exact FIFO history; dynamic bounds, aliases, branches,
timing, and other mailbox methods remain loud.

## [0.1.57] — 2026-10-27

The self-check surface now has 310 differential rows: 305 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 218
pyslang syntax witnesses: 96 MATCH and 122 REFUSE. The 22,059-path corpus
moves to 5,293 clean files and 16,699 partial files with 67 include skips;
the `ExpressionStatement:CallExpression` wall falls to 2,740. Fixed
one-dimensional unpacked struct arrays now also admit a direct packed
two-field `sort` key such as `{x.blue, x.green}`; computed, dynamic, and
aggregate keys remain loud.

## [0.1.56] — 2026-10-27

The self-check surface now has 309 differential rows: 304 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 218
pyslang syntax witnesses: 96 MATCH and 122 REFUSE. The 22,059-path corpus
moves to 5,292 clean files and 16,700 partial files with 67 include skips;
the `ExpressionStatement:CallExpression` wall falls to 2,741. Fixed
one-dimensional unpacked struct arrays now admit literal `sort`/`rsort` with
`(item.field)` ordering while computed and aggregate keys remain loud.

## [0.1.55] — 2026-10-27

The self-check surface now has 308 differential rows: 303 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 218
pyslang syntax witnesses: 96 MATCH and 122 REFUSE. The 22,059-path corpus
remains at 5,287 clean files and 16,705 partial files; the
`ExpressionStatement:CallExpression` wall remains 2,746. A named `string`
with source-pure blocking ASCII literal history is now admitted for `%s`/`%S`
`$sformatf`; dynamic and effectful histories remain loud.

## [0.1.54] — 2026-10-27

The self-check surface now has 307 differential rows: 302 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 218
pyslang syntax witnesses: 96 MATCH and 122 REFUSE. The 22,059-path corpus
remains at 5,287 clean files and 16,705 partial files; the
`ExpressionStatement:CallExpression` wall remains 2,746. Literal ASCII string
operands are now admitted for `%s`/`%S` in `$sformatf`; dynamic string storage
and non-ASCII operands remain loud.

## [0.1.53] — 2026-10-27

The self-check surface now has 306 differential rows: 301 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 218
pyslang syntax witnesses: 96 MATCH and 122 REFUSE. The 22,059-path corpus
remains at 5,287 clean files and 16,705 partial files; the
`ExpressionStatement:CallExpression` wall remains 2,746. Literal integral
`$sformatf` expressions now admit `%0b/%0h/%0o/%0d` and uppercase aliases via
the existing minimal-width renderers.

## [0.1.52] — 2026-10-27

The self-check surface now has 305 differential rows: 300 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 218
pyslang syntax witnesses: 96 MATCH and 122 REFUSE. The 22,059-path corpus
remains at 5,287 clean files and 16,705 partial files; the
`ExpressionStatement:CallExpression` wall remains 2,746. Literal integral
`$sformatf` expressions now admit `%c`/`%C` through the low-byte ASCII renderer;
dynamic or nonintegral string formatting remains loud.

## [0.1.51] — 2026-10-27

The self-check surface now has 304 differential rows: 299 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 218
pyslang syntax witnesses: 96 MATCH and 122 REFUSE. The 22,059-path corpus
remains at 5,287 clean files and 16,705 partial files; the
`ExpressionStatement:CallExpression` wall remains 2,746. A discarded literal
integral `$sformatf` call now reuses the expression converter and lowers to an
inert statement; dynamic formats and unsupported operands remain loud.

## [0.1.50] — 2026-10-27

The self-check surface now has 303 differential rows: 298 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 218
pyslang syntax witnesses: 96 MATCH and 122 REFUSE. The 22,059-path corpus
moves to 5,287 clean files and 16,705 partial files; the
`ExpressionStatement:CallExpression` wall falls to 2,746 while
`AssignmentExpression:target` remains 2,852. Literal zero-time queue
histories now lower `$q_exam` codes 2, 4, 5, and 6 to zero, and code 1
tracks current length through static removals; timed and computed histories
remain loud.

## [0.1.49] — 2026-10-27

The self-check surface now has 302 differential rows: 297 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 218
pyslang syntax witnesses: 96 MATCH and 122 REFUSE. The 22,059-path corpus
moves to 5,286 clean files and 16,706 partial files; the
`ExpressionStatement:CallExpression` wall falls to 2,747 while
`AssignmentExpression:target` remains 2,852. Literal FIFO/LIFO queue histories
now lower `$q_remove` payloads to scalar job, inform, and status writes;
dynamic, timed, empty, and other queue operations remain loud.

## [0.1.48] — 2026-10-27

The self-check surface now has 301 differential rows: 296 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 218
pyslang syntax witnesses: 96 MATCH and 122 REFUSE. The 22,059-path corpus
moves to 5,274 clean files and 16,718 partial files; the
`ExpressionStatement:CallExpression` wall remains 2,759 and `CallExpression`
falls to 2,739. Literal one-integral-operand `$sformatf` expressions now
render `%b/%h/%o/%d` and their uppercase equivalents through the packed-string
evaluator; dynamic formats, other conversions, and nonintegral operands remain
loud.

## [0.1.47] — 2026-10-27

The self-check surface now has 300 differential rows: 295 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 218
pyslang syntax witnesses: 96 MATCH and 122 REFUSE. The 22,059-path corpus
moves to 5,273 clean files and 16,719 partial files; the
`ExpressionStatement:CallExpression` wall falls to 2,759. Queue status calls
now admit source-pure named operands after one prior literal assignment, which
unlocks the `$q_exam` statistic-code fixture; computed and stateful queue forms
remain loud.

## [0.1.46] — 2026-10-27

The self-check surface now has 299 differential rows: 294 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 218
pyslang syntax witnesses: 96 MATCH and 122 REFUSE. The 22,059-path corpus
moves to 5,272 clean files and 16,720 partial files; `CallExpression` falls
to 2,750. Value-position `$q_full` now follows source-pure literal queue
history when prior status checks precede the first query; later status reads
and queue payload operations remain loud.

## [0.1.45] — 2026-10-27

The self-check surface now has 298 differential rows: 293 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 218
pyslang syntax witnesses: 96 MATCH and 122 REFUSE. The 22,059-path corpus
moves to 5,270 clean files and 16,722 partial files; `CallExpression` falls
to 2,752. Direct blocking scalar assignments from `$dist_uniform` now accept
signed literal 32-bit bounds, including negative-only and zero-crossing
ranges, with explicit seed updates; computed and value-position forms remain
loud.

## [0.1.44] — 2026-10-27

The self-check surface now has 295 differential rows: 290 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 218
pyslang syntax witnesses: 95 MATCH and 123 REFUSE. The 22,059-path corpus
moves to 5,254 clean files and 16,738 partial files, with
`AssignmentExpression:target` at 2,852. A bounded `$dist_uniform(seed, 0,
1000)` assignment now updates a 32-bit seed and one dynamic fixed-array cell;
other random calls, bounds, storage, and effectful selectors remain loud.

## [0.1.43] — 2026-10-27

The self-check surface now has 282 differential rows: 277 matches, zero
disagreements, and 5 recorded refusals. The grammar census has 218 pyslang
syntax witnesses: 95 MATCH and 123 REFUSE. The 22,059-path corpus remains at
5,240 clean files and 16,752 partial files, with `AssignmentExpression:target`
at 2,853 and `ExpressionStatement:CallExpression` at 2,775. The
discarded-result slice now covers numeric enum queries, fixed-array reductions
and locator queries (including source-pure `with` clauses), literal string
transformations, and empty queue/dynamic-array deletes; stateful and effectful
forms remain loud.

## [0.1.42] — 2026-10-26

The self-check surface now has 276 differential rows: 271 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 217
pyslang syntax witnesses: 92 MATCH and 125 REFUSE. The 22,059-path corpus
remains at 5,240 clean files and 16,752 partial files, with
`AssignmentExpression:target` at 2,853 and
`ExpressionStatement:CallExpression` at 2,775. The discarded-result slice
now covers zero-size queue/array/string queries, ASCII string queries and
`atoreal()`, pre-trigger `event.triggered()`, and enum `.name()` calls; each
reuses the value converter and leaves dynamic or stateful forms loud.

## [0.1.41] — 2026-10-26

The self-check surface now has 271 differential rows: 266 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 217
pyslang syntax witnesses: 92 MATCH and 125 REFUSE. The 22,059-path corpus
remains at 5,240 clean files and 16,752 partial files, with
`AssignmentExpression:target` at 2,853 and
`ExpressionStatement:CallExpression` at 2,775. Discarded statement calls now
cover integral signing casts, literal time-scale queries, invalid literal
`$fopen` modes, and empty associative-array count and endpoint queries; each
reuses the value-position proof and keeps dynamic or stateful forms loud.

## [0.1.40] — 2026-10-26

The self-check surface now has 266 differential rows: 261 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 217
pyslang syntax witnesses: 92 MATCH and 125 REFUSE. The 22,059-path corpus
remains at 5,240 clean files and 16,752 partial files, with
`ExpressionStatement:CallExpression` at 2,775. Admitted discarded `$clog2`
queries now erase their pure result after the existing operand checks; malformed
and effectful forms remain loud.

## [0.1.39] — 2026-10-26

The self-check surface now has 261 differential rows: 256 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 217
pyslang syntax witnesses: 92 MATCH and 125 REFUSE. The 22,059-path corpus
remains at 5,240 clean files and 16,752 partial files, with
`ExpressionStatement:CallExpression` at 2,775. Discarded literal
`$countbits`, `$countones`, `$onehot`, `$onehot0`, and `$isunknown` calls now
erase without represented state effects; dynamic operands remain loud.

## [0.1.38] — 2026-10-26

The self-check surface now has 260 differential rows: 255 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 217
pyslang syntax witnesses: 92 MATCH and 125 REFUSE. The 22,059-path corpus
remains at 5,240 clean files and 16,752 partial files, with
`ExpressionStatement:CallExpression` at 2,775. Discarded valid
`$bits(expr)` calls now erase without evaluating their expression, as required
by IEEE 1800; value-returning and malformed forms remain loud.

## [0.1.37] — 2026-10-26

The self-check surface now has 259 differential rows: 254 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 217
pyslang syntax witnesses: 92 MATCH and 125 REFUSE. The 22,059-path corpus
remains at 5,240 clean files and 16,752 partial files, with
`ExpressionStatement:CallExpression` at 2,775. A discarded valid
`$typename(expr)` call now erases without evaluating its expression, as required
by IEEE 1800; value-returning and malformed forms remain loud.

## [0.1.36] — 2026-10-26

The self-check surface now has 258 differential rows: 253 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 217
pyslang syntax witnesses: 92 MATCH and 125 REFUSE. The 22,059-path corpus
remains at 5,240 clean files and 16,752 partial files, with `CallExpression`
at 2,771. The literal predefined-stdout `$ftell(32'h8000_0001)` error result
now lowers to signed `-1`; dynamic descriptors and file-position state remain
loud.

## [0.1.35] — 2026-10-26

The self-check surface now has 257 differential rows: 252 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 217
pyslang syntax witnesses: 92 MATCH and 125 REFUSE. The 22,059-path corpus
measures 5,240 clean files and 16,752 partial files, with `CallExpression`
falling from 2,772 to 2,771. The literal predefined-stdout
`$fseek(32'h8000_0001, 0, 0)` error result now lowers to signed `-1`; dynamic
descriptors, offsets, whence values, and other file operations remain loud.

## [0.1.34] — 2026-10-26

The self-check surface now has 256 differential rows: 251 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 217
pyslang syntax witnesses: 92 MATCH and 125 REFUSE. The 22,059-path corpus
measures 5,239 clean files and 16,753 partial files, with
`CallExpression` falling from 2,778 to 2,772. Literal-only
`$coverage_control`, `$coverage_get`, `$coverage_get_max`, `$coverage_merge`,
and `$coverage_save` calls return the standard `SV_COV_NOCOV` zero in the
empty self-check coverage database; dynamic scopes and coverage constructs
remain loud.

## [0.1.33] — 2026-10-26

The self-check surface now has 255 differential rows: 250 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 217
pyslang syntax witnesses: 92 MATCH and 125 REFUSE. The 22,058-path corpus
moves to 5,233 clean files and 16,758 partial files, with
`AssignmentExpression:target` falling to 2,853. Pure conditional net drivers
with literal arms and one direct literal source initialization now snapshot
before static per-bit resolution; changing, effectful, unknown, and
strength-sensitive drivers remain loud.

## [0.1.32] — 2026-10-26

The self-check surface now has 254 differential rows: 249 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 217
pyslang syntax witnesses: 92 MATCH and 125 REFUSE. The 22,058-path corpus
moves to 5,231 clean files and 16,760 partial files, with
`AssignmentExpression:target` falling to 2,855. Fixed packed-net windows fed
by one direct literal source initialization now snapshot before the existing
static per-bit resolver; dynamic, multiply-written, effectful, and
strength-sensitive drivers remain loud.

## [0.1.31] — 2026-10-26

The self-check surface now has 253 differential rows: 248 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 217
pyslang syntax witnesses: 92 MATCH and 125 REFUSE. The 22,058-path corpus
remains at 5,230 clean files, 16,761 partial files, and 67 include skips. This
release admits dynamic indexed slices over nested packed elements by scaling
the runtime outer label in whole inner-element chunks; effectful, aggregate,
and unsupported forms remain loud.

## [0.1.30] — 2026-10-26

The self-check surface now has 252 differential rows: 247 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 217
pyslang syntax witnesses: 92 MATCH and 125 REFUSE. The 22,058-path corpus
remains at 5,230 clean files, 16,761 partial files, and 67 include skips. This
release admits dynamic `+:` and `-:` reads and targets on noncanonical one-bit
packed vectors through normalized flat windows; simple dynamic ranges,
effectful, unsigned, aggregate, and unsupported forms remain loud; partial
reads retain the selected evaluator boundary.

## [0.1.29] — 2026-10-26

The self-check surface now has 251 differential rows: 246 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 217
pyslang syntax witnesses: 92 MATCH and 125 REFUSE. The 22,058-path corpus
remains at 5,230 clean files, 16,761 partial files, and 67 include skips. This
release admits pure signed dynamic targets on noncanonical one-bit packed
vectors by normalizing their declared labels; unsigned, effectful, aggregate,
and unsupported forms remain loud.

## [0.1.28] — 2026-10-26

The self-check surface now has 250 differential rows: 245 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 217
pyslang syntax witnesses: 92 MATCH and 125 REFUSE. The 22,058-path corpus
measures 5,230 clean files, 16,761 partial files, and 67 include skips. This
release admits dynamic indexing of nested packed elements for reads and
blocking targets by scaling the runtime label by the element width; ascending,
descending, aggregate, effectful, and unsupported forms remain loud.

## [0.1.27] — 2026-10-26

The self-check surface now has 249 differential rows: 244 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 217
pyslang syntax witnesses: 92 MATCH and 125 REFUSE. The 22,058-path corpus
measures 5,227 clean files, 16,764 partial files, and 67 include skips. This
release admits dynamic `+:` and `-:` slices inside descending multidimensional
packed cells of bounded fixed arrays, with runtime bases scaled to the flat
cell representation; ascending, aggregate, alias-sensitive, and effectful
forms remain loud.

## [0.1.26] — 2026-10-26

The self-check surface now has 248 differential rows: 243 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 217
pyslang syntax witnesses: 92 MATCH and 125 REFUSE. The 22,058-path corpus
measures 5,227 clean files, 16,764 partial files, and 67 include skips. This
release admits one dynamic selector when reading a bounded multidimensional
integral subarray into a distinct flat row; multiple dynamic, aggregate,
aliased, shape-mismatched, and effectful forms remain loud.

## [0.1.25] — 2026-10-26

The self-check surface now has 247 differential rows: 242 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 217
pyslang syntax witnesses: 92 MATCH and 125 REFUSE. The 22,058-path corpus
measures 5,227 clean files, 16,764 partial files, and 67 include skips. This
release extends finite multidimensional subarray copies to one dynamic selector
after a constant prefix; multiple dynamic, aggregate, aliased, and effectful
forms remain loud.

## [0.1.24] — 2026-10-26

The self-check surface now has 246 differential rows: 241 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 217
pyslang syntax witnesses: 92 MATCH and 125 REFUSE. The 22,058-path corpus
measures 5,227 clean files, 16,764 partial files, and 67 include skips. This
release admits dynamic outer subarray copies into bounded multidimensional
integral arrays through guarded flat-cell expansion; multiple dynamic,
aggregate, aliased, and effectful forms remain loud.

## [0.1.23] — 2026-10-26

The self-check surface now has 238 differential rows: 233 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 217
pyslang syntax witnesses: 90 MATCH and 127 REFUSE. The 22,056-path corpus
measures 5,207 clean files, 16,782 partial files, and 67 include skips. This
release adds continuous sources from finite literal bindings, disjoint fixed
array slice copies, unsized one-bit left streams, pure literal integral net
expressions, and one dynamic selector in any dimension of finite multidimensional
arrays. Dynamic, overlapping, aggregate, and otherwise stateful forms remain
loud.

## [0.1.22] — 2026-10-26

The self-check surface now has 232 differential rows: 227 matches, zero
disagreements, and 5 recorded refusals. The grammar census remains at 217
pyslang syntax witnesses: 90 MATCH and 127 REFUSE. The 22,056-path corpus
measures 5,207 clean files, 16,782 partial files, and 67 include skips. This
release admits exact IEEE-754 `$realtobits` and `$shortrealtobits` conversions
from finite literal-bound real and shortreal variables; dynamic and
control-dependent real storage remains loud.

## [0.1.21] — 2026-10-25

The self-check surface now has 165 differential rows: 161 matches, zero
disagreements, and 4 recorded refusals. The grammar census remains at 214
pyslang syntax witnesses: 83 MATCH and 131 REFUSE. The 22,050-path corpus
measures 4,912 clean files, 17,072 partial files, and 66 include skips. This
release admits exact literal dynamic-array `size()` queries, four-state-aware
literal string `atobin()`/`atooct()`/`atohex()` conversions, and default-zero
literal semaphore `try_get` sequences. Dynamic, aliased, invalid, and other
stateful forms remain loud.

## [0.1.20] — 2026-10-25

The self-check surface now has 161 differential rows: 157 matches, zero
disagreements, and 4 recorded refusals. The grammar census remains at 214
pyslang syntax witnesses: 83 MATCH and 131 REFUSE. The 22,050-path corpus
measures 4,888 clean files, 17,096 partial files, and 66 include skips. This
release extends source-pure literal string support with assignment-aware
`.len()`, `.atoi()`, `.compare()`, and `.icompare()` results, including exact
decimal scanning and normalized ordering. Dynamic, aliased, non-ASCII, and
stateful string operations remain loud.

## [0.1.19] — 2026-10-25

The self-check surface now has 158 differential rows: 154 matches, zero
disagreements, and 4 recorded refusals. The grammar census remains at 214
pyslang syntax witnesses: 83 MATCH and 131 REFUSE. The 22,049-path corpus
measures 4,856 clean files, 17,127 partial files, and 66 include skips. This
release admits the state-free zero-key `semaphore.try_get(0)` result, exact
counts for untouched constructed mailboxes, and source-pure literal puts with
their corresponding unbounded-mailbox `num()` counts. Dynamic, aliased,
bounded, and other stateful mailbox/semaphore operations remain loud.

## [0.1.18] — 2026-10-25

The self-check surface now has 155 differential rows: 151 matches, zero
disagreements, and 4 recorded refusals. The grammar census remains at 214
pyslang syntax witnesses: 83 MATCH and 131 REFUSE. The 22,049-path corpus
measures 4,855 clean files, 17,128 partial files, and 66 include skips. This
release extends shallow untagged unpacked-union support with whole-value copies,
equality, conditional selection, compound member updates, and ordinary `case`
subjects, all through the shared flat-cell representation. Tagged, mixed-width,
nested, scheduled, and other aggregate forms remain loud.

## [0.1.17] — 2026-10-24

The self-check surface now has 150 differential rows: 146 matches, zero
disagreements, and 4 recorded refusals. The grammar census remains at 214
pyslang syntax witnesses: 83 MATCH and 131 REFUSE. The 22,049-path corpus
measures 4,853 clean files, 17,130 partial files, and 66 include skips. This
release admits direct reads and blocking writes through equal-width integral
members of shallow untagged unpacked unions by flattening them to one aliased
vector cell. Tagged, mixed-width, nested, whole-union, and scheduled forms
remain loud.

## [0.1.16] — 2026-10-24

The self-check surface now has 145 differential rows: 141 matches, zero
disagreements, and 4 recorded refusals. The grammar census remains at 214
pyslang syntax witnesses: 83 MATCH and 131 REFUSE. The 22,048-path corpus
measures 4,843 clean files, 17,139 partial files, and 66 include skips. This
release admits source-pure real/time severity arguments and constant formatted
`$sformat`/`$swrite` writes to packed variables and selections; dynamic,
effectful, aggregate, and unsupported formatting forms remain loud.

## [0.1.15] — 2026-10-24

The self-check surface now has 140 differential rows: 136 matches, zero
disagreements, and 4 recorded refusals. The grammar census remains at 214
pyslang syntax witnesses: 83 MATCH and 131 REFUSE. The 22,049-path corpus
measures 4,841 clean files, 17,142 partial files, and 66 include skips. This
release admits literal-zero semaphore `get` and `put` calls after a proven
constructor assignment; dynamic and stateful semaphore methods remain loud.

## [0.1.14] — 2026-10-24

The self-check surface now has 135 differential rows: 131 matches, zero
disagreements, and 4 recorded refusals. The grammar census has 214 pyslang
syntax witnesses: 83 MATCH and 131 REFUSE. The 22,048-path corpus measures
4,833 clean files, 17,149 partial files, and 66 include skips. This release
adds discarded literal `$itor`, `$bitstoreal`, and `$bitstoshortreal` calls,
plus inert handling for the standard-invalid dynamic-array continuous target
and multiple continuous assignments to one variable. Dynamic, effectful, and
stateful forms remain loud.

## [0.1.13] — 2026-10-24

The self-check surface now has 130 differential rows: 126 matches, zero
disagreements, and 4 recorded refusals. The grammar census has 214 pyslang
syntax witnesses: 83 MATCH and 131 REFUSE. The 22,048-path corpus remains
4,829 clean files, 17,153 partial files, and 66 include skips. This release
adds metadata-only `$bits(real)` and `$bits(shortreal)` queries plus exact
literal `$itor` nesting through `$rtoi`, `$realtobits`, and
`$shortrealtobits`. Named, computed, dynamic, and effectful forms remain
loud.

## [0.1.12] — 2026-10-24

The self-check surface now has 126 differential rows: 122 matches, zero
disagreements, and 4 recorded refusals. The grammar census has 214 pyslang
syntax witnesses: 83 MATCH and 131 REFUSE. The 22,048-path corpus measures
4,829 clean files, 17,153 partial files, and 66 include skips. This release
adds literal-input pure function calls, literal `$rtoi`, `$realtobits`, and
`$shortrealtobits` conversions, plus their discarded-result statement forms.
Dynamic, effectful, and stateful forms remain loud.

## [0.1.11] — 2026-10-24

The self-check surface now has 121 differential rows: 117 matches, zero
disagreements, and 4 recorded refusals. The grammar census has 214 pyslang
syntax witnesses: 83 MATCH and 131 REFUSE. The 22,048-path corpus measures
4,816 clean files, 17,166 partial files, and 66 include skips. This release
adds literal-strength continuous-driver slices, inert literal assertion-control
calls, and empty 2-state queue initializers. Dynamic, effectful, and
stateful forms remain loud.

## [0.1.10] — 2026-10-24

The self-check surface now has 114 differential rows: 110 matches, zero
disagreements, and 4 recorded refusals. The grammar census has 213 pyslang
syntax witnesses: 82 MATCH and 131 REFUSE. The 22,048-path corpus measures
4,810 clean files, 17,172 partial files, and 66 include skips. This release
adds literal continuous drivers for one-dimensional fixed-unpacked net-array
cells, reusing flat `Net` cells and the existing time-zero four-state
resolution path. Whole-array, dynamic, multidimensional, timed, and effectful
forms remain loud.

## [0.1.9] — 2026-10-24

The self-check surface now has 109 differential rows: 105 matches, zero
disagreements, and 4 recorded refusals. The grammar census has 213 pyslang
syntax witnesses: 82 MATCH and 131 REFUSE. The 22,048-path corpus measures
4,806 clean files, 17,176 partial files, and 66 include skips. This release
adds literal whole-net and selected packed continuous drivers, typed enum
defaults in packed-struct array patterns, and time-zero resolution for static
literal wire-driver sets. Dynamic, variable, selected-resolution, timed, and
effectful forms remain loud.

## [0.1.8] — 2026-10-24

The self-check surface now has 104 differential rows: 100 matches, zero
disagreements, and 4 recorded refusals. The grammar census has 212 pyslang
syntax witnesses: 81 MATCH and 131 REFUSE. The 22,048-path corpus measures
4,791 clean files, 17,191 partial files, and 66 include skips. This release
adds constant indexed streaming targets, discarded literal-return calls,
inert literal `$timeformat`, literal-initialized procedural floating
declarations, and exact `.len()` queries on unchanged literal strings.

## [0.1.7] — 2026-10-24

The self-check surface now has 99 differential rows: 95 matches, zero
disagreements, and 4 recorded refusals. The grammar census remains at 211
pyslang syntax witnesses: 80 MATCH and 131 REFUSE. The 22,046-file corpus
measures 4,783 clean files, 17,197 partial files, and 66 include skips.
This release adds zero-size queries after explicit empty writes and `new[0]`,
literal-return zero-argument functions, inert monitor toggles without a
registration, and stdout-directed `$fwrite` with its no-newline behavior.

## [0.1.6] — 2026-10-24

The self-check surface now has 94 differential rows: 90 matches, zero
disagreements, and 4 recorded refusals. The grammar census remains at 211
pyslang syntax witnesses: 80 MATCH and 131 REFUSE. The 22,046-file corpus
measures 4,766 clean files, 17,214 partial files, and 66 include skips.
This release adds pure real system-function writes, zero-time `$stime` and
integral `$realtime` queries, zero-size queue and dynamic-array queries, and
zero-length queries on inert strings.

## [0.1.5] — 2026-10-24

The self-check surface now has 89 differential rows: 85 matches, zero
disagreements, and 4 recorded refusals. The grammar census remains at 211
pyslang syntax witnesses: 80 MATCH and 131 REFUSE. The 22,046-file corpus
measures 4,752 clean files, 17,228 partial files, and 66 include skips. This
release adds opaque `process::self()` writes and direct null writes for opaque
handles, plus post-incremented fixed-array index writes with the required
write-before-update ordering.

## [0.1.4] — 2026-10-24

The self-check surface now has 84 differential rows: 80 matches, zero
disagreements, and 4 recorded refusals. The grammar census has 211 pyslang
syntax witnesses: 80 MATCH and 131 REFUSE. The 22,046-file corpus measures
4,747 clean files, 17,233 partial files, and 66 include skips. Recent admitted
forms include time-zero `$realtime` writes, literal-only string concatenation
and replication writes, and empty queue and dynamic-array literal writes.

## [0.1.3] — 2026-10-24

The self-check surface now has 76 differential rows: 72 matches, zero
disagreements, and 4 recorded refusals. The grammar census has 209 pyslang
syntax witnesses: 78 MATCH and 131 REFUSE. The 22,046-file corpus measures
4,745 clean files, 17,235 partial files, and 66 include skips. Recent admitted
forms include opaque class-handle declarations and null writes, empty
subroutine calls, pure floating literal writes, and default values from empty
functions.

## [0.1.2] — 2026-10-23

The self-check surface now has 71 differential rows: 67 matches, zero
disagreements, and 4 recorded refusals. The grammar census has 206 pyslang
syntax witnesses: 75 MATCH and 131 REFUSE. The 22,046-file corpus measures
4,689 clean files, 17,291 partial files, and 66 include skips. Recent admitted
forms include literal time-scale queries and inert literal `$sdf_annotate`
calls, alongside constant dynamic-array cells and deferred pure `$strobe`
arguments.

## [0.1.1] — 2026-10-23

The self-check surface now has 66 differential rows: 62 matches, zero
disagreements, and 4 recorded refusals. The grammar census has 204 pyslang
syntax witnesses: 73 MATCH and 131 REFUSE. The 22,046-file corpus measures
4,654 clean files, 17,326 partial files, and 66 include skips. Recent admitted
forms include elaboration-constant indexed packed targets, out-of-bounds
struct defaults, packed-struct streaming sources, and constant-range
streaming `with` targets.

## [0.1.0] — 2026-10-23

The first public SV self-check prerelease records the executable surface and
its measured coverage. The pinned differential corpus has 57 rows: 53 matches,
zero disagreements, and 4 recorded refusals. The grammar census has 202
pyslang syntax witnesses: 71 MATCH and 131 REFUSE. On the 22,046-file
sv-tests-2 snapshot, the extractor reports 4,617 clean files, 17,363 partial
files, and 66 include skips.

The self-check surface now includes integral unpacked-struct copies and
patterns, finite multidimensional array patterns and copies, packed windows in
selected array cells, recursive right-streaming unpack into fixed arrays, and
fixed-slice left-streaming targets. Unsupported aggregate, dynamic, timed, and
effectful forms continue to fail loudly with their construct name.
## [0.1.195] — 2026-10-29

Resolved forward typedef declarations now follow the extractor's existing
compile-time alias erasure in the legacy adapter census. A forward declaration
that resolves to an admitted integral or flat-struct typedef contributes no
self-check state; unresolved, class, and opaque forwards remain loud. The
`forward_typedef_metadata` fixture, adapter regressions, generated envelope,
Lean receipt, and differential row cover the family. Differential coverage
grows **449/443/0/6 → 450/444/0/6**; grammar coverage grows **233/111/122 →
234/112/122**. The temporary public sv-tests audit moves **364 clean / 437
partial / 111 include skips → 368 / 433 / 111**, while adapter unlockables
remain **7**.
## [0.1.196] — 2026-10-29

The legacy adapter census now mirrors the extractor's identity-based erasure
of uncalled subroutine declarations. An unreferenced task or function has no
time-zero effect and contributes no self-check state; referenced subroutines
remain loud at the callable boundary. The
`unreferenced_subroutine_metadata` fixture, adapter regressions, generated
envelope, Lean receipt, and differential row cover the family. Differential
coverage grows **450/444/0/6 → 451/445/0/6**; grammar coverage remains
**234/112/122**. The temporary public audit remains **368 clean / 433 partial /
111 include skips**, while adapter `SubroutineSymbol:Subroutine` residuals fall
**24 → 22** and the clean `fork_return` residual disappears.
## [0.1.197] — 2026-10-29

Empty arguments in no-conversion `$display` and `$write` calls now lower to
literal spaces through the existing `%s` renderer. The default integral and
string arguments retain their ordinary formatting, while an omitted operand
for a real conversion specifier remains loud. The
`empty_display_arguments` fixture, adapter regressions, generated envelope,
Lean receipt, and differential row cover the family. Differential coverage
grows **451/445/0/6 → 452/446/0/6**; grammar coverage grows
**234/112/122 → 235/113/122**. The temporary public sv-tests audit moves
**368 clean / 433 partial / 111 include skips → 380 / 421 / 111**; the
`EmptyArgumentExpression` adapter residual falls **12 → 0**, and adapter
unlockables remain **7**.
## [0.1.198] — 2026-10-29

The legacy adapter census now follows the extractor's source-history erasure
for discarded `string.putc`, `itoa`, `bintoa`, `octtoa`, and `hextoa` calls.
Literal source-pure methods contribute no self-check string state; dynamic,
effectful, and unsupported calls remain loud. The `string_method_adapter`
fixture, adapter regressions, generated envelope, Lean receipt, and
differential row cover the admitted shape. Differential coverage grows
**452/446/0/6 → 453/447/0/6**; grammar coverage remains **235/113/122**.
The temporary public sv-tests audit remains **380 clean / 421 partial / 111
include skips**, while clean-file adapter residuals `Call:itoa`, `Call:bintoa`,
`Call:octtoa`, `Call:hextoa`, and `Call:putc` each fall **1 → 0**; adapter
unlockables remain **7**.
## [0.1.199] — 2026-10-29

The legacy adapter census now follows the extractor's exact inert forms of
`$exit` and `$printtimescale`. These module-originating diagnostics contribute
no represented self-check state; unsupported argument forms and hierarchy
requirements remain loud. The `pure_diagnostic_adapter` fixture, adapter
regressions, generated envelope, Lean receipt, and differential row cover the
admitted shape. Differential coverage grows **453/447/0/6 → 454/448/0/6**;
grammar coverage remains **235/113/122**. The temporary public sv-tests audit
remains **380 clean / 421 partial / 111 include skips**, while adapter residuals
`Call:$exit` fall **1 → 0** and `Call:$printtimescale` fall **2 → 0**;
adapter unlockables remain **7**.
## [0.1.200] — 2026-10-29

The legacy adapter census now follows the extractor's represented forms of
`$info`, `$warning`, `$error`, and `$fatal`. Severity calls evaluate their
accepted pure arguments without adding a diagnostic stream to the self-check
state, while `$fatal` retains its represented whole-run halt. Unsupported
argument forms remain loud. The `severity_adapter` fixture, adapter
regressions, generated envelope, Lean receipt, and differential row cover the
family. Differential coverage grows **454/448/0/6 → 455/449/0/6**; grammar
coverage remains **235/113/122**. The temporary public sv-tests audit remains
**380 clean / 421 partial / 111 include skips**.
## [0.1.202] — 2026-10-29

The legacy adapter census now follows extractor elaboration flattening for
clean generated scopes. Generated processes remain in the ordinary self-check
vocabulary, while generated bodies containing delays or other unsupported
constructs stay loud at the nested boundary. The `generate_adapter` fixture,
adapter regressions, generated envelope, Lean receipt, and differential row
cover the family. Differential coverage grows **456/450/0/6 → 457/451/0/6**;
grammar coverage remains **235/113/122**.
## [0.1.203] — 2026-10-29

The legacy adapter census now follows the extractor's opaque class-handle
declaration erasure. Uninitialized `mailbox` and `semaphore` handles in module
and procedural scopes contribute no self-check state; reads, construction,
assignments, and methods remain loud. The `opaque_handle_adapter` fixture,
adapter regressions, generated envelope, Lean receipt, and differential row
cover the family. Differential coverage grows **457/451/0/6 → 458/452/0/6**;
grammar coverage remains **235/113/122**. On the checked-in 932-file example
sweep, `VariableDeclStatement:type` residuals fall **28 → 24**.
## [0.1.204] — 2026-10-29

The legacy adapter census now follows the extractor's literal semaphore
declaration shortcut. A local `semaphore` initialized by `new(N)` for a
nonnegative literal contributes no flat declaration state; dynamic constructors
and all semaphore operations remain loud. The `literal_semaphore_adapter`
fixture, adapter regressions, generated envelope, Lean receipt, and
differential row cover the family. Differential coverage grows
**458/452/0/6 → 459/453/0/6**; grammar coverage remains **235/113/122**. On
the checked-in 933-file example sweep, `VariableDeclStatement:type` residuals
fall **24 → 23**.
## [0.1.205] — 2026-10-29

The legacy adapter census now follows the extractor's declaration-only path for
an untouched 2-state mixed fixed/dynamic array. A declaration such as
`bit cells[2][][3]` contributes no flat state when all later occurrences are
dimension queries; initializers and value uses remain loud. The
`mixed_array_dimension_adapter` fixture, adapter regressions, generated
envelope, Lean receipt, and differential row cover the family. Differential
coverage grows **459/453/0/6 → 460/454/0/6**; grammar coverage remains
**235/113/122**. The checked-in 934-file example sweep remains at **23**
`VariableDeclStatement:type` residuals because this exact declaration shape was
not previously present in that corpus.
## [0.1.206] — 2026-10-29

The legacy adapter census now follows static associative-array declaration
erasure. Declarations that the extractor lowers to finite flat cells or
declaration-only storage no longer create a false aggregate type residual;
dynamic keys and value operations remain loud at their existing boundaries. The
`associative_decl_adapter` fixture, adapter regression, generated envelope,
Lean receipt, and differential row cover the family. Differential coverage
grows **460/454/0/6 → 461/455/0/6**; grammar coverage remains **235/113/122**.
On the checked-in 935-file example sweep, `VariableDeclStatement:type`
residuals fall **23 → 20**.
## [0.1.201] — 2026-10-29

The legacy adapter census now follows the extractor's assignment-block
lowering for source-pure fixed-array `sort`, `rsort`, and `reverse` calls,
including the existing struct-array ordering path. Unknown, dynamic, and
unsupported array histories remain loud. The `ordering_adapter` fixture,
adapter regressions, generated envelope, Lean receipt, and differential row
cover the family. Differential coverage grows **455/449/0/6 → 456/450/0/6**;
grammar coverage remains **235/113/122**. The temporary public sv-tests audit
remains **380 clean / 421 partial / 111 include skips**.
# [0.1.291] — 2026-10-31

Constant-index packed-vector `iff` guards such as `iff en[1:0]` now use the
existing `SelectRead` truthiness path. Dynamic indexed and aggregate selectors
remain loud. The `always_ff_event_iff_vector` witness covers disabled and
enabled clock publications. Differential coverage grows **555/541/0/14 →
556/542/0/14**; grammar coverage remains **240/212/28**.
# [0.1.293] — 2026-10-31

Descending dynamic packed part-select `iff` guards such as `iff en[idx -: 2]`
now use the existing `SelectRead` direction and truthiness path. Aggregate
selectors remain loud. The `always_ff_event_iff_dynamic_neg` witness covers
disabled and enabled clock publications. Differential coverage grows
**557/543/0/14 → 558/544/0/14**; grammar coverage remains **240/212/28**.
# [0.1.294] — 2026-10-31

Packed concatenation `iff` guards such as `iff {en[1], en[0]}` now use the
existing `SExpr.concat` truthiness path. Replications and other aggregate
selectors remain loud. The `always_ff_event_iff_concat` witness covers disabled
and enabled clock publications. Differential coverage grows **558/544/0/14 →
559/545/0/14**; grammar coverage remains **240/212/28**.
# [0.1.295] — 2026-10-31

Constant replication `iff` guards such as `iff {2{en}}` now use the existing
`SExpr.concat` truthiness path. Calls and other aggregate selectors remain
loud. The `always_ff_event_iff_replication` witness covers disabled and enabled
clock publications. Differential coverage grows **559/545/0/14 → 560/546/0/14**;
grammar coverage remains **240/212/28**.
# [0.1.296] — 2026-10-31

Logical negation of admitted vector `iff` guards such as `iff !en[1:0]` now
uses the existing vector truthiness path. The `always_ff_event_iff_vector_not`
witness covers nonzero and zero vectors. Differential coverage grows
**560/546/0/14 → 561/547/0/14**; grammar coverage remains **240/212/28**.
# [0.1.297] — 2026-10-31

Bitwise inversion of admitted vector `iff` guards such as `iff ~en[1:0]` now
uses the existing `SelectRead` and unary evaluator. The
`always_ff_event_iff_vector_bnot` witness covers nonzero and zero vectors.
Differential coverage grows **561/547/0/14 → 562/548/0/14**; grammar coverage
remains **240/212/28**.
# [0.1.298] — 2026-10-31

Logical implication `iff` guards such as `iff en -> mode` now use the
side-effect-free `!en || mode` lowering and existing logical evaluator. The
`always_ff_event_iff_implication` witness covers false and true implications.
Differential coverage grows **562/548/0/14 → 563/549/0/14**; grammar coverage
remains **240/212/28**.
# [0.1.299] — 2026-10-31

Width-normalized scalar comparisons in `iff` guards, such as `iff en == 1`,
now retain their expression-context `Resize` nodes and use the existing guard
evaluator. The `always_event_iff_unsized` witness covers disabled and enabled
edges. Differential coverage grows **563/549/0/14 → 564/550/0/14**; grammar
coverage remains **240/212/28**.
# [0.1.300] — 2026-10-31

Plain `always` now supports one-bit constant packed-select event expressions
through a retained sampled-value registration. The `always_event_bit_select`
witness covers wake-up on a changed selected bit. Differential coverage grows
**564/550/0/14 → 565/551/0/14**. The fresh grammar page remeasures the
committed witness set at **240/209/31** (from the stale **240/212/28** page);
no new syntax production is introduced here.
# [0.1.301] — 2026-10-31

Edge-qualified constant packed-select events such as `always @(posedge
bus[2])` now use the retained sampled-expression registration and existing
four-state edge rule. The `always_event_bit_select_posedge` witness covers a
0-to-1 selected-bit edge. Differential coverage grows **565/551/0/14 →
566/552/0/14**; grammar coverage remains **240/209/31**. The read-only event
expression repricer moves from **26/26** to **22/22** sole files/spans.
# [0.1.302] — 2026-10-31

Constant packed part-select events such as `always @(bus[3:0])` now compare
the complete sampled vector through the existing scheduler registration. The
`always_event_part_select` witness covers a whole-vector value change.
Differential coverage grows **566/552/0/14 → 567/553/0/14**; grammar coverage
remains **240/209/31**. The event-expression repricer moves from **22/22** to
**21/21** sole files/spans.
# [0.1.303] — 2026-10-31

Scalar conditional event expressions such as `always @(sel ? a : b)` now use
the retained sampled-expression registration and ordinary ternary evaluator.
The `always_event_conditional` witness covers a selected-branch value change.
Differential coverage grows **567/553/0/14 → 568/554/0/14**; grammar coverage
remains **240/209/31**. The event-expression repricer moves from **21/21** to
**20/20** sole files/spans.
# [0.1.304] — 2026-10-31

Scalar binary event expressions using `&`, `|`, or `^` now compare their
evaluated result through the retained sampled-expression registration. The
`always_event_binary` witness covers unchanged and changed results.
Differential coverage grows **568/554/0/14 → 569/555/0/14**; grammar coverage
remains **240/209/31**. The event-expression repricer moves from **20/20** to
**18/18** sole files/spans.
# [0.1.305] — 2026-10-31

Reduction `|`, `&`, and `^` event expressions now compare their scalar result
through the retained sampled-expression registration. The
`always_event_reduction` witness covers a reduction result transition.
Differential coverage grows **569/555/0/14 → 570/556/0/14**; grammar coverage
grows **240/209/31 → 240/210/30** as the reduction witness moves to MATCH. The event-expression repricer moves from **18/18** to
**16/16** sole files/spans.
# [0.1.306] — 2026-10-31

Unary scalar `~` and `!` event expressions now compare their evaluated result
through the retained sampled-expression registration. The `always_event_unary`
witness covers a unary result transition. Differential coverage grows
**570/556/0/14 → 571/557/0/14**; grammar coverage remains **240/210/30**.
The sole event-expression repricer remains **16/16** because this source also
carries another boundary.
# [0.1.307] — 2026-10-31

Concatenation event expressions such as `always @({a, b})` now compare the
complete packed result through the retained sampled-expression registration.
The `always_event_concat` witness covers a concatenated value change.
Differential coverage grows **571/557/0/14 → 572/558/0/14**; grammar coverage
remains **240/210/30**.
# [0.1.394] — 2026-11-01

Parameter-dependent pure symbolic procedural `for` loops are now retained in
sv-0.2 envelopes and expanded by `Param2` at each concrete parameter point.
`sem2/symbolic_parameter_for` adds a four-cycle Icarus MATCH at `N = 3`;
effectful bounds and non-unit steps remain loud. The phase-2 corpus grows
**787 → 788** rows; self-check coverage remains **638 rows / 615 agree / 0
disagree / 23 recorded refusals**.

# [0.1.395] — 2026-11-01

Pure sv-0.2 user functions with one automatic local temporary may now inline
that local's single blocking assignment into the return expression.
`sem2/symbolic_local_function` adds a four-cycle Icarus MATCH; unassigned or
stateful locals and general call frames remain loud. The phase-2 corpus grows
**788 → 789** rows; self-check coverage remains **638 rows / 615 agree / 0
disagree / 23 recorded refusals**.

# [0.1.396] — 2026-11-01

Pure sv-0.2 user functions may now inline an automatic local declared with a
source-pure initializer before returning that local. The
`symbolic_local_initializer_function` witness adds a four-cycle Icarus MATCH;
stateful locals and general call frames remain loud. The phase-2 corpus grows
**789 → 790** rows; self-check coverage remains **638 rows / 615 agree / 0
disagree / 23 recorded refusals**.


# [0.1.397] — 2026-11-01

Pure sv-0.2 user functions may now inline a source-pure local initializer when
the function publishes that local through its implicit return assignment. The
`symbolic_local_initializer_implicit_function` witness adds a four-cycle
Icarus MATCH; stateful locals and general call frames remain loud. The phase-2
corpus grows **790 → 791** rows; self-check coverage remains **638 rows / 615
agree / 0 disagree / 23 recorded refusals**.

# [0.1.398] — 2026-11-01

Pure sv-0.2 user functions may now inline a source-pure local blocking
assignment when the function publishes that local through its implicit return
assignment. The `symbolic_local_function_implicit` witness adds a four-cycle
Icarus MATCH; stateful locals and general call frames remain loud. The phase-2
corpus grows **791 → 792** rows; self-check coverage remains **638 rows / 615
agree / 0 disagree / 23 recorded refusals**.

# [0.1.399] — 2026-11-01

Pure sv-0.2 user functions may now fold a short chain of automatic local
declaration initializers before an explicit return. The
`symbolic_local_chain_function` witness adds a four-cycle Icarus MATCH; longer
or stateful locals and general call frames remain loud. The phase-2 corpus
grows **792 → 793** rows; self-check coverage remains **638 rows / 615 agree /
0 disagree / 23 recorded refusals**.

# [0.1.400] — 2026-11-01

The pure local-initializer USERFN chain now erases its referenced function
declaration during symbolic module admission. The previous envelope lowered
the call but retained `SubroutineSymbol:Subroutine`, causing `runner2` to
refuse it; the regenerated `symbolic_local_chain_function` envelope contains
only the typed expression tree. Coverage counts are unchanged pending the
Xcelium differential rerun.

# [0.1.401] — 2026-11-01

The initializer-implicit witness now carries a source-bound
`icarus_unavailable` declaration for Icarus 13's reproducible `vvp` assertion
at `vthread.cc:5468`. Xcelium was also unavailable on this host because no
license could be checked out (`NOLICN`/`LMF-03015`); neither oracle is treated
as a semantic match.

# [0.1.402] — 2026-11-02

Pure sv-0.2 user functions may now fold a short local initializer chain when
the final local is published through an implicit return assignment. The
`symbolic_local_chain_implicit_function` witness adds a four-cycle Icarus
MATCH; longer or stateful locals and general call frames remain loud. The
phase-2 corpus grows **793 → 794** rows; self-check coverage remains **638 rows
/ 615 agree / 0 disagree / 23 recorded refusals**.

# [0.1.403] — 2026-11-02

The implicit local-initializer-chain witness now records its exact Icarus 13
`vvp` assertion at `vthread.cc:5468` as a source-bound unavailable oracle.
Coverage remains unchanged until a simulator provides a trace.

# [0.1.404] — 2026-11-02

Pure sv-0.2 user functions may now fold two automatic locals assigned once in
source order before an explicit return. The
`symbolic_local_assignment_chain_function` witness adds a four-cycle Icarus
MATCH; stateful locals and general call frames remain loud. The phase-2 corpus
grows **794 → 795** rows; self-check coverage remains **638 rows / 615 agree /
0 disagree / 23 recorded refusals**.

# [0.1.405] — 2026-11-02

Pure sv-0.2 user functions may now fold the same two-local assignment chain
when the final local is published through an implicit return assignment. The
`symbolic_local_assignment_chain_implicit_function` witness covers the
four-cycle form; stateful locals and general call frames remain loud. The
phase-2 corpus grows **795 → 796** rows; self-check coverage remains **638
rows / 615 agree / 0 disagree / 23 recorded refusals**.

# [0.1.406] — 2026-11-02

Pure sv-0.2 user functions may now fold a short chain of at least two
automatic locals assigned once in source order, including the three-local
`symbolic_local_assignment_three_chain_function` witness. Stateful locals and
general call frames remain loud. The phase-2 corpus grows **796 → 797** rows;
self-check coverage remains **638 rows / 615 agree / 0 disagree / 23 recorded
refusals**.

# [0.1.407] — 2026-11-02

The three-local pure assignment-chain USERFN form now also supports an
implicit return assignment. The
`symbolic_local_assignment_three_chain_implicit_function` witness covers the
four-cycle form; stateful locals and general call frames remain loud. The
phase-2 corpus grows **797 → 798** rows; self-check coverage remains **638
rows / 615 agree / 0 disagree / 23 recorded refusals**.

# [0.1.408] — 2026-11-02

Parameter-dependent symbolic procedural `for` loops now retain positive
literal compound steps (`i += 2`, `i = i + 2`, and `i = i - 2`) and expand them
at each parameter point. The `symbolic_parameter_for_compound_step` witness
adds a four-cycle Icarus MATCH; effectful and nonliteral loop state remains
loud. The phase-2 corpus grows **798 → 799** rows; self-check coverage remains
**638 rows / 615 agree / 0 disagree / 23 recorded refusals**.

# [0.1.409] — 2026-11-02

Parameter-dependent symbolic procedural `for` loops now evaluate a positive
parameter expression used as a compound step. The
`symbolic_parameter_for_parameter_step` witness adds a four-cycle Icarus
MATCH at `N = 5, S = 2`; zero, negative, effectful, and nonliteral amounts
remain loud. The phase-2 corpus grows **799 → 800** rows; self-check coverage
remains **638 rows / 615 agree / 0 disagree / 23 recorded refusals**.
## Structured SVA AST retention

Concurrent assertions now retain Slang's structured property syntax in each
`SvaProperty.ast` envelope node. Ingestion parses the typed SVA tree and the E
contract bridge instantiates ordinary boolean leaves as `Expr2`; source text is
provenance only and is no longer reparsed by a Lean `splitOn` parser. Unsupported
property forms remain named failures. The SVA evaluator also uses sampled-value
edges and fails unknown assertion decisions conservatively.

## `sv_equations` Nat-facing report forms

The `sv_equations?` report now prints constant bit indices as numerals and
generate-loop bounds over the Nat binder (`1 ≤ i → i < N`). The summary keeps
its Int affine representation internally; only the diagnostic presentation is
normalized, so existing proof terms and soundness checks are unchanged.

## Guarded generate guards in int32 mode

Generate-if constant evaluation now reads typed 32-bit integer parameters from
`IEnv.nvals`, matching the unbounded `vals` path. This keeps `int32Agrees`
semantic rather than representation-sensitive for guarded families; the
`sklansky_guards/int32_guard` fixture pins agreement at `N = 16` and `N = 1`.

## Exact signed generate guards

Generate-if and generate-for guard arithmetic now uses signed 32-bit `int`
semantics, including the sign bit of `&`, `|`, and `^` operands, with typed
parameters read from `nvals`. Unsupported guard operators remain loud. The
clean-room `guard_correctness/add_gg2` fixture pins the signed-bitwise case.

The regression guard now also checks the INT lookup itself (`N` is bound in
`nvals`) and the `((N - 6) & 1) != 0` case at `N = 5`. The
`only_n16`, `add_gg2`, and `add_int32` fixtures all build with their
`int32Agrees` checks, so parameter-dependent generate branches no longer fail
just because the exact path uses the typed-value table.
The `add_int32` proof also inspects the instantiated process shape: `N = 16`
selects `s = sr`, while `N = 5` wraps `M` to the negative signed-32 value and
selects `s = ~sr`.

## Sklansky comb-tactic obligation boundary

The source-shaped Sklansky walls remain loud and named: a conditional generate
inside a generate loop reports `GuardEval obligation`, while a dynamic or
nonlinear genvar read or write reports `non-affine genvar-index obligation`.
The clean-room `sklansky_guards` and `sklansky_guards/nonaffine` rows pin these
messages. Guarded-family retention is not admitted until its proof path carries
guard totality through the generated family and preserves branch-selected site
identities; no branch is dropped on a failed evaluation.

## Always-comb alias guard in semantic families

The generated `name.sem` family now uses an alias-guarded instantiation wrapper
at every concrete parameter point, including flattened hierarchy. The original
unguarded instantiation remains available to the structural proof route; the
executable semantic family turns an unsafe `always_comb` copy into the named
`AlwaysComb:alias-read` process. Width-parametric guard rows cover two distinct
concrete widths, so the refusal is not limited to the default elaboration.
## 2026-11-06 — Sklansky guarded-family contract

The Sklansky design note now specifies the proof-facing `GuardTotal`
obligation, branch-qualified identities, and the required error behavior for
guarded generate families. The guarded-family prototype remains parked until
that premise is threaded through `AutoObl` and `Summary.sound`; failed guard
evaluation is never treated as an empty family.

## 2026-11-06 — F1 unknown sampled decisions are loud

The finite SVA evaluator now refuses ordinary boolean expressions, negations,
`$past`, and `$stable` when their sampled value is unknown, including the
default sample before the trace begins. This prevents simulator-style
x-optimism (`!x` becoming true) in the E contract. `$rose` and `$fell` keep
their sampled-value edge semantics.

## 2026-11-07 — F1 sampled-value conversion follows §16.6

Corrected the finite SVA evaluator after the rule-3 audit. Boolean evaluation
now retains `Logic` through nested negation, conjunction, disjunction, and
sampled-value functions, then converts x/z-only results to false once at the
assertion boundary as IEEE 1800-2023 §16.6 requires. `$past`, `$rose`, `$fell`,
and `$stable` return false at the first sampled tick; later `$rose`/`$fell`
use the four-state §9.4.2 transition table. Missing signals and unsupported E
expressions remain loud. The retained structured Slang AST path is unchanged.

## 2026-11-06 — typed-int `$clog2` localparams

The comb summary's constant-expression path now keeps `$clog2` in the same
32-bit signed `int` class for typed `int` localparams as for `integer`
localparams. Concrete guards cover both a positive and a zero result; the
source-shaped Sklansky generate-family walls remain the named obligations above.

## 2026-11-06 — exact generate-guard parameter lookup

Generate guards now read integer parameters from both the unbounded `vals`
table and the exact signed-32 `nvals` table. Signed 32-bit bitwise and shift
guards preserve the operand bit pattern, so parameter-dependent generate-if
conditions agree across both instantiation paths instead of refusing or
silently taking a different branch.

## 2026-11-06 — x-resolution timing design

The x-resolution design note now records the remaining open-choice axes and
requires the E relation to quantify over multiple-clock schedules, coincident
edges, stopped clocks, and asynchronous input arrival times while preserving
the defined sampling and NBA rules.

## 2026-11-07

- Literal counted procedural loops are now retained as source-shaped `For`
  nodes by default, matching parameter-bound loops; `--retain-loops` remains
  a compatibility spelling. Extraction no longer consults a literal-trip cap.

- Self-check concatenated blocking targets with dynamic selectors or aliasing
  leaves are now refused as `AssignmentExpression:target` instead of fixing
  a right-to-left order. Static disjoint leaves retain the explicit
  assignment-order parameter.

- Explicit drive strengths on continuous assignments are now refused in the
  single-file/self-check path as well as symbolic mode. Strength resolution,
  including `highz0`/`highz1`, is outside the flat store; no strength is
  erased into a time-zero write.

- `$timeunit`/`$timeprecision` symbolic queries no longer fold from raw
  source text. Until Slang scope time-scale metadata is threaded through,
  they remain loud `CallExpression` nodes, covering comments, module
  `timeunit` declarations, and inherited compilation-unit scales without a
  fabricated value.

- `always @*` lowering now refuses an external signal with a continuous
  time-zero driver under R3, preserving the distinction from `always_comb`
  until active-region ordering is modelled. The procedural extractor also
  keeps dynamic unpacked-array compound and ordinary targets equally loud.

- Self-check now refuses time-zero initial blocks with overlapping
  read/write or write/write state as `Initial:order` instead of selecting
  source order. Independent initial blocks remain admitted; the refusal is
  pinned by new kernel guards.

- Port-width extraction now preserves net input selects and narrower child
  outputs into wider parent NET targets, so `Hier2.connProcs` refuses the
  Xcelium/Icarus-width split as `PortConn:net-width`. Added a hierarchical
  clean-room refusal row.

- The legacy M0 JSON loader and runner now refuse two-clock and data-clocked
  designs (`Clock:multiple` / `Clock:implicit`) instead of firing every edge
  process on every implicit cycle. Clean-room refusal rows cover both shapes.

- Added the optional `Schedule:preemptive` profile guard. It keeps the
  source-shaped process-atomic E route unchanged while refusing designs whose
  cross-process read/write or write/write windows could expose an IEEE §4.7
  mid-process suspension. `runner2` rows opt in with `"preemptive": true`;
  `sem2/preempt_profile` records the loud refusal until ls-spec supplies the
  scheduler choice point.

- The comb-view exact-`int` leaf proofs now consume `IEnv.intVal?` directly,
  including signed-32 `nvals` bindings, and a symbolic range guard pins the
  canonicalization premise. This keeps proof reductions on the exact
  instantiation path without reopening the legacy unbounded lookup cases.

- Added `--retain-proc-rewrites` for the first WP-PROC source-structure twin:
  compound assignments remain `CompoundAssign` envelope nodes and load as a
  named `AssignmentExpression:compound` refusal because frozen `Stmt2` has no
  compound constructor. The established lowering remains the default.

- The same retain mode now keeps block-local declarations as lexical
  `LocalDecl` nodes and reports the frozen scoped-storage boundary at load;
  ordinary symbolic extraction continues to hoist static locals as before.

- Event-controlled plain `always` blocks now have a retain-mode `AlwaysEvent`
  envelope twin that keeps the event-control kind and body. The default E1
  `always @*`/event-list conversion to `AlwaysComb` is unchanged, and the
  retained node loads as a named event-list Unsupported boundary.

- The retain mode also keeps a single-driver `wire` as a `Net` declaration
  rather than applying N2's net-to-variable rewrite. The default one-driver
  conversion remains unchanged and the retained net stays a loud semantic
  boundary.

- Source-declared user-function calls now have a retain-mode `FunctionCall`
  envelope twin. They load as the named `CallExpression:user-function`
  boundary while the default pure-function inliner remains unchanged.

