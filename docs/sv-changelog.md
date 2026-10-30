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
