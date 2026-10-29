# Simulator disagreements

The cycle harnesses retain the IEEE behavior when a simulator disagrees
with a documented language rule. These cases report `DECLARED DISAGREEMENT`
and print both complete traces. Their count is separate from verified
simulator matches. The source programs, observation signals and stimuli
remain unchanged.

Each `oracle_disagreement` entry in `harness/sv/cases.json` or `cases2.json`
records the standard clause, observed simulator, declaration date,
retirement condition, both complete traces, and SHA-256 bindings for the
source, envelope, case and generated testbench. The case digest is canonical
JSON with sorted keys and compact separators, excluding only the declaration
itself and any `icarus_unavailable` declaration. Every other digest covers exact bytes. The common checker is
`harness/sv/oracle_disagreements.py`.

The unavailable-oracle checker replaces the DUT's exact absolute path with
`<source>` in both stdout and stderr before comparing diagnostics. This
keeps declarations independent of the checkout directory; all remaining
output, the exit status and the failing stage still have to match exactly.
A regression copies the real source and envelope to a second checkout.
Phase-2 failures also publish their complete diagnostic as a GitHub error
annotation, escaping workflow-command data so multiline output is retained.

The checker also reduces two pieces of HOST framing to one canonical text on
both sides of the comparison (2026-10-28), because the declarations were
recorded with Ubuntu's Icarus 12.0-2build2 and Homebrew's Icarus 12.0 on
macOS reports the same failures through a different C library and shell:
a vvp C `assert` (glibc `vvp: vvp_net.cc:1180: bool
vvp_vector4_t::set_vec(…): Assertion `…' failed.`, macOS `Assertion
failed: (…), function set_vec, file vvp_net.cc, line 1180.`) becomes one
form that keeps the file, line, function name and expression; and the
`/bin/sh` report of an aborted `ivl` pipeline stage (dash `Aborted (core
dumped)`, macOS bash's job report naming `ivlpp` `Done` and `ivl` `Abort
trap: 6`, with process ids and temporary names that change every run)
becomes one token. Nothing else is rewritten: a different assertion, the
same one at another line, an aborted preprocessor, another signal, a bare
`Aborted`, a different exit status or stage, or any extra line still fails
(`HostFramingTests` in `harness/sv/test_oracle_disagreements.py` mutates
each). Before this the sixteen crash declarations ERRORed on every macOS
run.

The entry applies only to its named simulator and single schedule. A changed
input or trace fails the harness. Agreement also fails while the entry is
live, requiring review and removal of the resolved declaration. Missing
tools and failed simulations cannot satisfy an entry. CI runs mutation and
reporting tests even on hosts without a simulator, and emits warnings for
measured disagreements.

The named simulator is `"iverilog"` or, since round 6 (2026-10-29), `"xcelium"`.
Xcelium is the REFERENCE simulator of ls-sv (docs/sv-xcelium-reference.md), so
a declaration that names it is a different statement from an Icarus one: the
reference itself departs from an explicit sentence of IEEE 1800-2023 and the
departure cannot be refused statically (the only such class so far is a
run-time-base part-select that leaves the vector, "Run-time part-select bases
that leave the vector" below). The model keeps the LRM reading and the row
reports the departure, never a match; the policy for the other cases, where the
shape CAN be refused, is to refuse (section "Refused where the oracles split",
item (R6a), and "Icarus propagates a copy inside the block's own run: the alias
rows are REFUSED"). An Xcelium declaration is checked in two places with the
same alarms: against a LIVE `xrun` run, like an Icarus one (a harness run
without Xcelium leaves the row to the Icarus comparison, which must agree with
the model), and against the PINNED trace of `harness/sv/xcelium_golden.json`
in `diff_test2.py --golden`, where the pin plays the simulator: the row
reports `XREF-DECLARED` (counted apart from `XREF-MATCH` and `XREF-DIFF`) when
the pinned and the model trace are the recorded ones, and the run FAILS when
the departure is resolved (the pin equals the model) or has changed. Without a
usable pin (stale, absent, failed) the input bindings are still checked. A row
carries one declaration, so a row where Icarus and Xcelium depart in different
cells needs a split. `harness/sv/declare_disagreement.py` writes a declaration
from the row's current inputs and the pinned (or a fresh Icarus) trace: the
digest recipe it uses is the checker's own (`binding_digests`).

## Unary plus

`unary_plus_directed` differs under Icarus 12.0-2build2 in hosted run
[39272617564](https://github.com/thomasnormal/lean-surfaces/actions/runs/39272617564),
and under Icarus 12.0 on Debian 13. The two known input cycles agree.
For `10xz` and `zzzz`, Icarus preserves the operand; Lean returns `xxxx`.

IEEE 1800-2023 §11.4.3, Table 11-6 and the arithmetic unknown rule on page
277 require the all-x result. The independent Xcelium 24.03-s004 observation
and its source-bound eleven-check fixture are recorded in
[Integral unary arithmetic](sv-unary-arithmetic.md#oracle).

## Partial variable initialization

Icarus 12.0 and 12.0-2build2 lower a partially continuously assigned four-state variable to
a net. Untouched bits then appear as z. IEEE 1800-2023 §6.8, Table 6-7
initializes these variables to x; §6.5 treats individual packed bits as
independent elements. Under §23.2.2.3 an explicitly typed `output logic`
defaults to a variable. The packed struct and union declarations in the
member cases are also variables.

The affected exact fixtures are `bit_select_assign`,
`noncanonical_bit_assign`, `packed_member_subrange`, `packed_member_bit`,
`packed_union_subrange`, `packed_union_bit`, `nested_member_bit`,
`nested_member_concat`, `typedef_nested_concat`,
`fixed_array_noncanonical_slice`, and `concat_undriven`. Their declarations
bind each observed pair separately. Xcelium 24.03-s004 confirms the model on all
eleven (2026-10-29, pinned in `harness/sv/xcelium_golden.json`, audit cluster D1
in `docs/sv-xcelium-audit.md`): the pinned trace equals the model's in every
cycle and only Icarus departs. In Xcelium a variable with a continuously
driven bit keeps the untouched bits at x, and a NET reads z there (measured on
`output wire`, an implicit-type `output [3:0]`, `wire`, `wire logic`, all z;
`output logic`, `output var`, struct and fixed-array members and concatenation
leaves, all x), which is the boundary the model's refusal of nets
(`PortSymbol:net-z`, `NetSymbol:net-z`) relies on. Yosys erases the
variable/net distinction (its netlist reads x for nets too), and Verilator is
two-state, so neither is a witness for x versus z.

`concat_undriven` (2026-10-28, `Examples/system-verilog/sem2/concat_undriven/`)
reaches the same lowering through a plain-vector concatenation target:
`assign {y[3:2], z} = x;` with `output logic [3:0] y` drives `y[3:2]` and
nothing drives `y[1:0]`. Icarus 12.0 reads `y = 10zz` for `x = 101`; the
model keeps the variable's x (`10xx`). Yosys 0.53 `prep; eval` reports
`y[1:0]` as used but undriven ("Missing value"), and its synthesized
netlist simulated in Icarus reads them as x. Declaration
`iverilog-concat-target-undriven-init`.

Out-of-range concatenation leaves have no Icarus oracle. In
`assign {y[4:3], z, y[2:0]} = x;` with `output logic [3:0] y` the leaf
`y[4:3]` overhangs the vector; the model writes its in-range bit `y[3]` and
drops `y[4]` (IEEE 1800-2023 §11.5.1), so `x = 101101` gives `y = 0101`,
`z = 1`. Icarus 12.0 warns "Part select y[4:3] is out of range" and then
refuses to compile ("uwire "y" must have a single driver, found (2)"), so
no row can carry the shape. Yosys 0.53 `prep; eval` agrees with `run2` on
all 64 two-state values of `x`, and so does its synthesized netlist on the
three points simulated (verifier probe `cx_oob2`, re-measured 2026-10-28).

A standalone Icarus diagnostic distinguishes variable initialization from
the partial continuous-assignment lowering:

```systemverilog
module init_probe;
  logic [7:0] untouched, continuous_partial, procedural_partial;
  wire [7:0] net_partial;
  assign continuous_partial[1] = 1'b1;
  assign net_partial[1] = 1'b1;
  initial begin
    procedural_partial[1] = 1'b1;
    #1;
    $display("%b %b %b %b", untouched, continuous_partial,
             procedural_partial, net_partial);
    $finish;
  end
endmodule
```

Icarus 12.0 prints `xxxxxxxx zzzzzz1z xxxxxx1x zzzzzz1z`. Its generated vvp
code declares `continuous_partial` as `.net` and `procedural_partial` and
`untouched` as `.var`. The standard result for `continuous_partial` is
`xxxxxx1x`; the existing model retains that variable behavior.

## Linearized packed-array indices

`array_oob_inner` (`Examples/system-verilog/sem2/array_oob_inner/`) selects
past the end of an INNER packed dimension: `m[0][4]` and the procedural
write `w[0][5] = 1'b1` over `logic [1:0][3:0]`. IEEE 1800-2023 §7.4.6 makes
an index outside its own dimension invalid (reads return x, writes perform
no operation) and §11.5.1 reads an out-of-range bit-select of the packed
element `m[0]` as x. slang's constant evaluator agrees: a localparam
initialized from the same select evaluates to `1'bx`. The model keeps this
per-dimension rule (`Param2.lean`, `arrayElemWindow`).

Icarus 12.0 instead linearizes the flat offset: `m[0][4]` reads `m[1][0]`
and the write lands in `w[1][1]` (`w_flat = 00100000`, `z = ~a[0]`). Yosys
0.53 (`prep; eval`) gives the same values as Icarus, so a synthesized
netlist of such a source disagrees with the model; a post-synthesis
equivalence check is the place this surfaces.

The same split covered PART selects, and a part-select TARGET overhanging the
LSB end of an inner dimension. `array_oob_part`
(`Examples/system-verilog/sem2/array_oob_part/`) reads, over
`logic [1:0][3:0] m` and the ascending `logic [0:1][0:3] q`, a range part
overhanging the msb end of a non-last element (`m[0][5:3]`), indexed parts
overhanging either end of an ascending dimension (`q[0][2 +: 3]`,
`q[1][-1 +: 2]`), an element label outside an ascending dimension
(`q[0][4]`), and writes `w[0][5:2] = a` (msb overhang); `array_oob_lsbwrite`
(`Examples/system-verilog/sem2/array_oob_lsbwrite/`) writes
`w[1][L +: 2] = a[1:0]` with `L = -1` over `logic [1:0][3:0] w`. The model (and
the LRM, §11.5.1: a part partly out of range reads x in exactly its
out-of-range bits and a write changes only its in-range bits) gave
`d_hi = xx0`, `r_lo = 11x`, `r_hi = x0`, `asc_oob = x`, clipped the first write
to `w[0][3:2]` and wrote only `w[1][0] = a[1]` in the second (slang's constant
evaluator agrees: `M[0][5:3] = 3'bxx0`, `Q[0][2 +: 3] = 3'b11x`,
`Q[1][-1 +: 2] = 2'bx0`). Icarus 12.0 and Yosys 0.53 (`prep; eval`) linearize
into the neighbouring element instead: `d_hi = 110`, `r_lo = 110`, `r_hi = 10`,
`asc_oob = 0`, the first write's top bits land in `w[1][1:0]`
(`w_flat = 00111100` for `a = 1111`), and the second writes `a[0]` into
`w[0][3]` (`00011000`; Icarus also prints `sorry: constant selects in always_*
processes are not currently supported (all bits will be included)`).

**Since round 6 (2026-10-29) those two rows are LOUD-REFUSAL rows**, and the
declarations on them are retired ("Declarations retired in round 6" below).
Xcelium 24.03-s004 does not linearize and does not read the whole vector either:
it treats every part-select that is only PARTLY in range as wholly invalid, so
it reads `d_hi`, `r_lo`, `r_hi` as all x (`xxx`, `xxx`, `xx`) and drops both
writes whole (`w_flat = 00000000`; the 1-D twin `v[L +: 3] = a[2:0]` too, which
the model, Icarus and Yosys write as `v[1:0] = a[2:1]`). The tools split three
ways (model/Icarus-on-1-D/Yosys-on-1-D/slang against Icarus-and-Yosys on the
inner dimension against Xcelium), and the model no longer chooses
(`ArraySel:partial-overhang`, item R6-1 below). What stays, as a declared
Icarus row, is the one shape on which Xcelium equals the model: the element
label OUTSIDE an ascending dimension, `q[0][4]` (row `array_oob_asc`,
declaration `iverilog-packed-asc-label-linearized`): the model and Xcelium read
x, Icarus and Yosys read `q[1][0]`.

Selects past the end of the LAST element do NOT agree in every tool, contrary to
what this page said until round 6: a part-select that overhangs either END of the
vector (the last element's msb, the first element's lsb) is read as all x and
written as a no-op by Xcelium (`array_oob`: `over = m[1][5:2]` is `xxxx`, the
write `m[1][5:2] = ...` is dropped; the 1-D rows `partsel*`), while the model,
Icarus and Yosys follow the LRM. Those rows are refusal rows too. A select WHOLLY
outside (`m[1][5:4]`, `m[1][6]`) is x in every tool and stays admitted.
The Xcelium confirmation of the declared bit-select row `array_oob_inner` is
above; it covers that BIT-select row only. Yosys linearizes like Icarus, and
Verilator (2-state) masks the index to `ceil(log2(dimension))` bits and
crashes in its DFG pass on a constant outer-OOB read without `-fno-dfg`;
Icarus cannot take a run-time OUTER index on a multidimensional packed array
(`Array index expressions must be constant here`). The svGolf post-synthesis
check sees the Yosys netlist disagree with the model on any source with an
inner-dimension out-of-range select.

## Single-element range direction

A packed range with one element, `[k:k]`, has no direction of its own.
slang's constant evaluator and Yosys 0.53 read it as descending, and so does
the model: `x[b -: w]` selects labels `b` down to `b-w+1`, `x[b +: w]`
labels `b+w-1` down to `b` (IEEE 1800-2023 §11.5.1), and every label other
than `k` reads x. Icarus 12.0 evaluates `x[b -: w]` over a single-element
range with a CONSTANT (elaboration-time) base `b` exactly as `x[b +: w]`,
counting UP from the same base, in reads and in writes. With a run-time
base Icarus reads labels `b` down to `b-w+1` as well and agrees with the
model and Yosys: over `input logic [3:3] y` (`y = 1`) and a 3-bit `i`,
`y[i -: 2]` reads `1x` at `i = 3` and `x1` at `i = 4` in all three
(verifier probe `vp_onedyn`, `i` over 0..7; re-measured beside the
constant `y[3 -: 2]`, which reads `x1` in Icarus). The rest of this entry
is about constant bases. Over `input logic [10:10] y` (`y = 1`),
`y[10 -: 4]` reads `xxx1` in Icarus and `1xxx` in the model, in Yosys (`prep; eval`) and in
slang (`C[10 -: 4] = 4'b1xxx` for `localparam logic [10:10] C = 1'b1`);
`y[10 +: 4]` reads `xxx1` and `y[7 +: 4]` reads `1xxx` everywhere. A sweep
of the base over `5..15` gives Icarus the same `-:` and `+:` result at
every base. A procedural write `t[10 -: 4] = 4'b1000` over
`logic [10:10] t = 0` leaves `t = 0` in Icarus and sets it in Yosys, and
`4'b0001` sets it in Icarus and leaves it 0 in Yosys. The two readings
agree only on a one-bit select and where both selects miss the element.
Ranges like this arise at parameter points: `logic [N-1:0] v` is `[0:0]` at
`N = 1`.

Row `array_param_labels_l7` (`Examples/system-verilog/sem2/array_param_labels/`
at `L = 7`, declaration `iverilog-single-element-minus-select`) pinned it: the
input `logic [7:L] u` becomes `[7:7]` and `w = u[L+1 -: 2]` reads labels
8..7, `{x, u[7]}` — `x1`, `x0`, `xx`, `xz` for `u = 1, 0, x, z` in the
model, `x1`/`x0` in Yosys (`chparam -set L 7; prep; eval`), `2'bx1` for
slang's `U[8 -: 2]` — while Icarus reads labels 9..8 and gives `xx` in every
cycle. Found by the verifier on probes `vr_one.sv` and `vh_prng.sv`;
re-measured on `vr_one.sv` and the base sweep (2026-10-28). Because Yosys
agrees with the model, a post-synthesis check does not see this split; an
Icarus simulation of the RTL does.

Xcelium 24.03-s004 (round 6, 2026-10-29) cannot adjudicate it by VALUE, and can
by DIAGNOSTIC. Its value trace on this row is `xx` in every cycle, equal to
Icarus's, but only because Xcelium reads every partly out-of-range part-select
as all x (cluster P1), which the model does not follow: on a one-label vector
every select of two or more labels has an out-of-range label under both readings
(a one-label `-:` and `+:` select is the same select), and Xcelium drops every
overhanging write, so no value probe exists. Its elaboration diagnostic does
separate them. An overhanging indexed part-select used as a continuous-assign
net TARGET is a hard `BNDIPERR` error that prints the evaluated label range:
`u[8 -: 2]` over `[7:7]` prints `[8:7]`, `u[7 -: 2]` prints `[7:6]`,
`u[8 +: 2]` prints `[9:8]` (38 of 38 `-:` cases over `[7:7]` and 38 of 38 over
`[0:0]`; with the parameter-dependent base of the row, `u[L+1 -: 2]` prints
`[8:7]`), never Icarus's `9:8`. So Xcelium's front end reads `-:` over a
single-element range as the LRM, the model, Yosys and Verilator do, and the
declaration stands. That is a diagnostic from a verifier run, not pinned data
(`xcelium_golden.json` holds traces). **The row is a loud-refusal row since
round 6**: `u[8 -: 2]` over `[7:7]` is partly out of range, so
`ArraySel:partial-overhang` refuses it, and the declaration is kept on the row
as the record of the Icarus lowering (nothing checks it while the row is
refused; the ordinary rows `array_param_labels`, `_n4_l2` and `_n3_l5` are
unchanged). The Icarus quirk is no longer reachable through an admitted select:
a select that stays in range on a one-label vector has width one, where `-:`
and `+:` coincide.

## Ascending full-width minus select

A second Icarus 12.0 reading of a constant-base `-:` select, this time over
a MULTI-element ascending range `[a:b]` (`a < b`): when the base is the
range's LEFT label `a` and the width is the element count `b-a+1`, Icarus
reads the whole vector `x[a:b]`, as if the select were `x[a +: w]`. IEEE
1800-2023 §11.5.1 selects labels `a` down to `a-w+1`, all but `a` out of
range: `{x…x, x[a]}`. The model, Yosys 0.53 and slang follow the LRM. Plain
literal declarations show it (Icarus `$display`, 2026-10-28): over `logic
[-1:0] t = 2'b10`, `t[-1 -: 2]` is `10` in Icarus, `x1` in the LRM, in
Yosys (`prep; eval`) and in slang (`C[-1 -: 2] = 2'bx1` for `localparam
logic [-1:0] C = 2'b10`); over `logic [0:1] u = 2'b10`, `u[0 -: 2]` is `10`;
over `logic [5:6] w = 2'b10`, `w[5 -: 2]` is `10`; over `logic [-1:1] k =
3'b100`, `k[-1 -: 3]` is `100`; over `logic [0:3] a = 4'b1000`, `a[0 -: 4]` is
`1000`. A narrower width, or another base, reads as the LRM says in Icarus
too: `k[0 -: 3]` is `x10`, `a[0 -: 2]` is `x1`, `[-1:2]`'s `g[-1 -: 2]` is
`x1`, `[-2:0]`'s `f[-2 -: 2]` is `x1`. Such a range arises at a parameter
point: `logic [K:0] t` is `[-1:0]` at `K = -1`.

Row `label_kminus_w1` (`Examples/system-verilog/sem2/label_kminus/` at
`W = 1`, declaration `iverilog-ascending-full-width-minus-select`) pins it:
`K = W - 2 = -1`, `t[-1] = b[0]`, `t[0] = b[1]`, and `p = t[K -: 2]` reads
`{x, t[-1]}` — `x1`, `x0`, `x1`, `x0`, `xz` for `b = 01, 10, 11, x0, 0z` in
the model and `x1`/`x0`/`x1` in Yosys (`chparam -set W 1; prep; eval`) —
while Icarus gives `10`, `01`, `11`, `0x`, `z0`. `q = t[K +: 2]` agrees in all
three, and the family's other rows (`W = 4, 3, 0, -1, 5`) passed against Icarus.
Found by the verifier on probes `vb2c.sv`, `vb2.sv` and `vi1.sv` (2026-10-28,
the static-label routing of WP1(b)); re-measured on the literal
declarations above.

Xcelium 24.03-s004 (round 6, 2026-10-29) equals neither side on `p`: it reads
`xx` in all five cycles (the partly out-of-range select is wholly invalid, audit
cluster P1), so the declaration could not be confirmed, and it equals the model
and Icarus on `q` (`10`, `01`, `11`, `0x`, `z0`: no departure at all). Every
row of the family has a partly out-of-range select at its point (`p` at
`W <= 2`, and `q = t[K +: 2]` over the descending `[K:0]` at `W >= 3`), so
**all six `label_kminus_w*` rows are loud-refusal rows since round 6**
(`ArraySel:partial-overhang`) and the declaration is retired ("Declarations
retired in round 6" below). What stays admitted is split into fixtures that
contain only the in-range select: `label_kminus_p` (`p = t[K -: 2]` at
`W = 4, 3, 5`: rows `label_kminus_p`, `_p_w3`, `_p_w5`) and `label_kminus_q`
(`q = t[K +: 2]` over the ASCENDING `[-1:0]` at `W = 1`), each equal in the
model, Icarus and Xcelium. The Icarus ascending `-:` reading is no longer
reachable through an admitted select.

## Run-time part-select bases that leave the vector (round 6, 2026-10-29)

`v[sel +: 4]` and `v[sel -: 4]` over `logic [7:0] v` with a SIGNAL as the base are
the one shape of the Xcelium part-select rule that cannot be refused statically:
whether the select leaves the vector depends on the value. IEEE 1800-2023 11.5.1
(printed page 296) reads such a select that is partly out of range as x in
exactly the out-of-range bits ("Part-selects that are partially out of range
shall, when read, return x for the bits that are out of range"), and the base
expressions are evaluated in a self-determined context. The model, Icarus 12.0,
Yosys 0.53 (on known bits) and slang follow it. Xcelium 24.03-s004 returns **all
x for the whole select** whenever at least one selected bit is out of range and at
least one is in range, and the LRM value in every other case (in range, wholly out
of range, x/z base): over the verifier's 195 cycles and 864 distinct cells every
partly-out read was all x and every other read equalled the LRM value, in
`assign`, `always_comb`, `always @*`, `always_ff`, a function return, a `?:`,
inside an expression, a testbench `initial` block and a `$display` argument, for
`+:` and `-:`, 2-bit and 4-bit widths, ascending and offset ranges, memory words
and packed-array slices. It prints no warning by default (`IIFAOB` / `IIRAOB`
under `-ii_warn -ii_rwarn` only), is not a time-zero race and does not depend on
the stimulus order. It is the same rule as the constant-base P1 and the write P3
(docs/sv-xcelium-audit.md, 6.1 item 1), which are refused
(`ArraySel:partial-overhang`, item (R6a) below); the model cannot refuse this
one, so it is **declared**, and the row is reported as a departure of the
reference from the standard, never as a match.

Rows (`Examples/system-verilog/sem2/partsel_dyn/`, the part of the former
`partsel` that stays admitted: the constant in-range selects `rev_up`, `rev_dn`,
`top`, the run-time selects `dyn_up`, `dyn_dn` and the run-time lane select
`dyn_lane`): `partsel_dyn`, `partsel_dyn_n2_w5`, `partsel_dyn_n6_w2`,
`partsel_dyn_n5_w1`, `partsel_dyn_n1_w4`, and `dyn32_part`
(`Examples/system-verilog/sem2/dyn32/`, the five 32-bit-base selects of `dyn32`
with a stimulus that keeps every base non-negative). Declaration
`xcelium-runtime-partial-part-select-all-x`, `"sim": "xcelium"`: the recorded
simulator trace is the PINNED Xcelium trace. On each `partsel_dyn*` row 6 of the 22
part-select cells are partly out of range (`dyn_up` at `sel = 5, 6, 7`, `dyn_dn` at
`sel = 0, 1, 2`), Xcelium is all x on those 6 and equals an independent LRM oracle
on the other 16, and the model equals the oracle on all 22; on `dyn32_part` 15 of 55,
with the same result. Icarus equals the model on every cycle of every one of the six
rows, so in a default (Icarus-only) run they are verified matches that name the
declared Xcelium departure on their line, and `diff_test2.py --golden` reports
`XREF-DECLARED`; with a live `xrun` the row is a declared disagreement.

Why a declaration and not "follow Xcelium": following it would put the model against
the LRM text, Icarus, Yosys and slang, and a consumer turns the all-x into defined
values (`if (|a[B+:4])`, `$countones`, `case`, `===` all take the other branch). Why
not "refuse": the base is a signal. svGolf is covered separately: its `fourstate`
stage refuses a run-time select whose index can leave its declared range
(`svgolf/README.md`), so a scored design never reaches this shape.
`-ii_val` does not make the reference follow the LRM here (module-level reads stay
all x), so no flag choice removes the declaration (docs/sv-xcelium-reference.md,
section 6).

**What is NOT declared.** Row `dyn32` keeps its 22 differing cells and is not declared:
8 of them are a different cause. Xcelium reads a 32-bit UNSIGNED base as unsigned
(`s - 2` at `s = 0, 1` is `32'hFFFFFFFE` and `32'hFFFFFFFF`, wholly out of range, all x;
`b32 = 32'hFFFFFFFE`, `32'hFFFFFFFF`), as the typing rules of 11.8.1 imply, and the
model, Icarus and Yosys read it as a two's-complement `int` (`Param2.lean`
`dynPartRead32`, the header of `dyn32.sv`). On a vector with a negative range the
difference is visible without the partial rule: `w[3:-4]` with an unsigned 32-bit
`bu = 32'hFFFFFFFE` gives `w[bu +: 4] = xxxx` in Xcelium and `1101` in Icarus, and a
signed `bi = -2` gives `1101` in both. That is the model's recorded decision
against the reference, not a departure of the reference from the standard, and round 6
is refusal-only, so it is an open item (docs/sv-xcelium-audit.md, 6.4).

## Select indices wider than 32 bits (2026-10-28, round 3 repair; REFUSED 2026-10-29, round 6)

`fold_pcase_wide` (`Examples/system-verilog/sem2/fold_pcase/`, `N = 40`)
reads `v[a - P]` over `logic [7:0] v` with a 42-bit `a` and `int P = -3`.
IEEE 1800-2023 §11.8.2 zero-extends `P` into the unsigned 42-bit index
expression and §11.5.1 reads an index outside `[7:0]` as x; the index is
the whole 42-bit value. The model did both (the round-3 repair, row
`fold_pcase_n40`), and so does Yosys 0.53 (`prep; eval`: `v[a]` at
`a = 2^32 + 2` is `1'x`). Icarus 12.0 reads such an index at its LOW 32
bits: `a` all ones gives index `2^42 - 2^32 + 2` and Icarus reads `v[2]`;
`a = 0` reads `v[3]`, `a = 2^40 + 1` reads `v[4]`. Verilator 5.042 does the
same on a plain `v[a]`. In-range indices (`a = 2^32 - 3`, `2^32 + 4`) and
out-of-range ones whose low 32 bits are also out of range (`a = 5`) agree.

This was a declared Icarus departure (`iverilog-wide-index-truncation`,
"Icarus alone, no licensed-simulator confirmation"). **Xcelium 24.03-s004
contradicts that premise** (docs/sv-xcelium-audit.md, T1): it truncates the
index to its low 32 bits too, and says so (`xmelab: *W,BIGWBS`, which fires
only above 32 bits), equal to Icarus on all 13 cells of a minimal repro and on
every read form probed (33, 40 and 64-bit index, signed index, procedural
block, part-select base, unpacked-array element). It also truncates a CONSTANT
wide index (`v[40'h1_0000_0002]` reads `v[2]`; Icarus and the model read x) and
a wide index of an lvalue (`w[a] = 1` at `a = 2^32 + 2` sets bit 2; Icarus drops
the write). Three simulators truncate, the LRM text and Yosys do not: the model
is alone with the standard, and a truncation would be one oracle against the
text, so **round 6 refuses**, as it already refused the part-select twin below.
A bit-select whose index is wider than 32 bits and is not a constant is loud
(`Select:wide-index`, `RangeGuard2.lean` `PDesign.wideIndexViolation`, at the
instance's own point; the extractor's `ElementSelectExpression:wide-index` where
the index is already wider at the default point), as is a constant index of
2^32 or more. The refusal sits BESIDE `name.sem` (the select guard family of
`RangeGuard2.lean`), not in `instExpr2`'s select arm, whose lemmas
(`instExpr2_bitSel_ident_dyn`) are stated for every environment. A constant
wider than 32 bits whose value fits (`v[40'd2]`) and an index of at most 32 bits
are unchanged (`wide_index_n8`, `wide_index_n30`). Rows `fold_pcase_n31`,
`fold_pcase_n40`, `fold_pcase_n40_pm1`, `fold_pcase_n40_p5` and
`fold_pcase_wide` (33- and 42-bit signal-dependent indices; they had matched
only because their stimulus never let the whole index and its low 32 bits
disagree) are loud-refusal rows; `fold_rself_n40`, whose index is a parameter
constant equal to 0, stays a verified row. The declaration is corrected
(Xcelium truncates too: three simulators, not an Icarus quirk) and retired by
this refusal ("Declarations retired in round 6" below). Fixtures `wide_index`
(the width depends on the point: Lean's guard), `wide_index_lit` (a 33-bit
index at the default point: Xcelium equals Icarus, both truncate, and an x bit
in the high half still reads a defined bit) and `wide_index_const`
(`v[40'h1_0000_0002]`: Xcelium reads `v[2]`, Icarus and the model x): the
extractor's refusals.

## Refused where the oracles split (2026-10-28)

Two select shapes, and (since the round 3 folds) one operand shape and one
instance-override shape, and (since round 4) one legality question, and
(since round 5) a second override shape and an untyped constant's width,
and (since round 6) an untyped constant's WIDTH whatever its value and a
third override shape, have no LRM-and-tools consensus to declare against:
Icarus 12.0 and Yosys 0.53 disagree with each other. The model refuses them loudly
rather than pick one, so none is a passing row. (1) A CONSTANT select label that
lands at or beyond `2^31` — in practice a 32-bit unsigned wrap such as
`v[UI - 1 +: 4]` with `parameter int unsigned UI = 0`, or `v[U - 1 +: 4]`
with `logic [3:0] U = 0` (the unsized `1` widens the label to 32 bits): Icarus
reads the label as `4294967295` (all x), Yosys as `-1` (`v[2:-1]`, partly in
range). The model computes the label width-exactly (`Param.lean`,
`evalSized`) and refuses it (`Param2.lean`, `partOffsetsWild`). (2) A
RUN-TIME part-select base wider than 32 bits: Icarus truncates it to its low
32 bits (a 40-bit `2^32 + 1` reads `v[4:1]`), Yosys reads the whole value
(all x) — refused (extractor `RangeSelectExpression:dynamic-wide-base`, Lean
`dynBaseRead`). Both tools read an EXACTLY 32-bit base as
a two's-complement `int`, and so does the model (rows `dyn32`). Measured on
the verifier probes `pa.sv`/`pb.sv`/`pc.sv`; a post-synthesis check would
otherwise surface these as model/netlist mismatches.

(3) (Round 3 folds, 2026-10-28.) A NEGATIVE genvar used as a simple operand
in an unsigned context wider than 32 bits: `a ^ g` with `g = -1` and a
42-bit `a`. Yosys 0.53 (`proc; opt`: `{a[41:32], ~a[31:0]}`), Verilator
5.042 and the LRM (IEEE 1800-2023 §27.4: the loop's implicit localparam is
an `integer`; §11.8.2: a simple operand is converted to the unsigned
context type before it is extended) ZERO-extend it, exactly as all three
and Icarus 12.0 do for an `int` PARAMETER in the same position; Icarus
12.0 SIGN-extends the genvar (`~a`). The model refuses
(`GenvarRef:unsigned-extension`, `Param2.lean`, `PExpr.negGenvarWidened`;
refusal row `fold_pgen_n40`), and admits every case the tools agree on: a
non-negative genvar, any genvar in a context of at most 32 bits (rows
`fold_pgen`, `fold_pgen_n30`, `fold_pgen_n40_g3`), and a negative
parameter (rows `fold_pneg*`, "Default-point folds, round 3" in
`docs/sv-envelope-schema.md`).

(4) (Round 3 repair, 2026-10-28.) A TYPED instance parameter override that is
a context-propagating expression: `fold_ovr_child #(.P(U + 8'd100))` with an
8-bit `U = 200` and `parameter logic [15:0] P` (the same for `int Q`). IEEE
1800-2023 §10.8 lists the override of a parameter with an explicit type
among the assignment-like contexts, so the sum is evaluated at 16 bits:
Icarus 12.0 gives 300. Yosys 0.53 (the synthesized netlist) and Verilator
5.042 evaluate it at its own 8 bits and give 44. The model refuses
(`InstanceSymbol:override-context`, extractor `_sym_override_root`; refusal
row `fold_ovr`): the constant tier evaluates an override in the
instantiating scope, without the child's parameter type, and could follow
neither reading at every point. Leaves, selects, comparisons and INT-class
overrides read alike in all three (rows `fold_ovr2*`).

(5) (Round 4 Lane A, 2026-10-28.) A declaration initializer on a variable
that an `always_comb` or `always_ff` writes: `logic [1:0] t = 2'b10;
always_comb t[0] = a;`, `output logic [1:0] y = 2'b10` with `always_ff
@(posedge clk) y[0] <= a;`, in any port form and in children. IEEE
1800-2023 §9.2.2.2 and §9.2.2.4 forbid any other process to assign such a
variable; §6.5 counts "a declared variable initialization" as a procedural
assignment, §10.5 calls it "a special case of procedural assignment", and
§4.2 lists procedural assignment statements among processes — but no clause
says outright whether an initializer is a writing process. The tools split
on it. Xcelium 24.03 rejects every such design at elaboration (`xmelab:
*E,MULAXX: Multiple drivers to always_comb output variable t detected`, and
`… always_ff output variable …`; 41 probes, every ANSI and non-ANSI port
form, flat and in a child, bit and whole-variable writes). Verilator 5.042
stops on `%Warning-MULTIDRIVEN: Variable written to in always_comb also
written by other process` for a whole-variable `always_comb` write and
accepts the rest; slang accepts all of them, Icarus 12.0 all but one it
does not parse (the non-ANSI `output var logic` declaration), Yosys 0.53
all but four it rejects for unrelated reasons (an inferred latch in
`always_comb`, two declarations it does not parse, one assertion on a
struct port). The extractor refuses the block
(`ProceduralBlockSymbol:initialized-variable`, `_sym_proc_initialized_write`
in `extractors/sv/extract.py`; rows `vg_initc`, `vg_initf`, `vg_initq`,
`vg_initqp*`, `pi_nonansi`, `pi_nonansi_hier`, `pi_nonansi_p*`,
`vh_initcomb`). Round 3 had admitted these as legal (row `vg_initc`); the
claim is withdrawn. A plain `always` writer is unrestricted (§9.2.2.1) and
every tool, Xcelium included, runs it: those designs stay admitted and
verified (rows `pi_ansi_forms`, `pi_ansi_multi`, `pi_nonansi_forms`,
`pi_nonansi_reg`, `pi_width_forms`, `pi_width_p*`, `pi_hier_plain`: Icarus
12.0 and Xcelium 24.03 give identical traces, Verilator 5.042 the same with
`x` read as 0, the Yosys 0.53 netlist the same initial values). A
variable declared inside the procedural block, or automatic, is the block's
own and is not counted.

(6) (Round 4 folds, Lane B, 2026-10-28.) A GENVAR INITIALIZER whose two
readings differ: `for (genvar g = U + 1'b1; g < 17; g++)` with `logic
[N-1:0] U = -1` at `N = 4`. A genvar initializer is an assignment to the
genvar's 32-bit `integer` (slang binds an `Implicit` conversion to
`integer` around it): slang's own elaboration at the point and the Yosys
0.53 netlist evaluate `U + 1'b1` at 32 bits, 16 (IEEE 1800-2023 §10.8,
§11.8.1), Icarus 12.0 at its own 4 bits, 0 — `g` starts at 0 and drives
every bit. The model followed Icarus silently (round 3 FOLDS verifier,
repro `rf_gv`); it now refuses where the readings differ
(`Constant:assignment-context`, `Param.lean` `evalSized`; the extractor
keeps the conversion, `_sym_genvar_init`; refusal rows `fold_rgv_n4_um1`,
`fold_rgv_n8_um1`, and `fold_rgv_n4_s7` for the signed twin `S + S` with a
4-bit `S = 7`: -2 against 14) and runs where they agree (rows `fold_rgv*`).

(7) (Round 4 folds, Lane B, 2026-10-28.) A genvar initializer whose value
is no 32-bit signed integer: `genvar m = U` with a 40-bit `U = 2^40 - 1`, a
33-bit `U = 2^33 - 1`, or a 32-bit unsigned `U = 2^32 - 1`. Here Icarus 12.0
and Yosys 0.53 AGREE — they keep the value whole, so `m < 4` never holds —
and slang's elaboration and IEEE 1800-2023 §27.4 (the genvar's value is an
`integer`) disagree with both: `m` starts at -1. The model refuses
(`Constant:assignment-context`; refusal rows `fold_rgvw_n40_um1`,
`fold_rgvw_n33_um1`, `fold_rgvw_n32_um1`) rather than follow the tools
against the LRM; a value that fits runs (rows `fold_rgvw*`). The check is
keyed on the 32-bit target, so an instance override of such a value into a
32-bit typed parameter is refused the same way — a recorded over-refusal.

(8) (Round 4 folds, Lane B, 2026-10-28.) An INT-CLASS instance override into
a typed parameter wider than 32 bits whose 32-bit arithmetic overflows:
`fold_rovr_child #(.P(N * 1024))` with `parameter logic signed [39:0] P` and
`N = 2^21`. Icarus 12.0 evaluates it at the parameter's 40 bits (§10.8: P =
2^31), the Yosys 0.53 netlist at its own 32 (P = -2^31) — the split of (4),
reached by an INT-class tree, which (4) still admits. The extractor keeps
the assignment as a root conversion of the parameter's width
(`_sym_override_root`), and the model refuses where the two readings
differ (`Constant:assignment-context`; refusal rows `fold_rovr_n2097152`,
`fold_rovr_n4194304`, `fold_rovr_nm2097153`) and runs where they agree
(rows `fold_rovr`, `_nm7`, `_n2097151`). Before, the model followed Icarus
there silently (the round 3 pushed-chain floor). [Round 5: the root
conversion is exact only for a parameter of FIXED width — into one whose
declared width depends on another parameter it carried the default
point's width and the refusal missed the split; such an override is
refused outright since round 5, item (10).]

(9) (Round 4 repair, Lane A, 2026-10-28.) A non-ANSI INPUT whose separately
declared variable or net carries an initializer: `module c(a, y); input
[1:0] a; logic [1:0] a = 2'b01;` (or `wire [1:0] a = 2'b01;`). slang keeps
it on the internal symbol, not the port, and is silent; IEEE 1800-2023 §6.5
counts the initialization as a procedural assignment and implies a
continuous assignment from the input connection, which makes the design
illegal (for a net it is a second continuous driver). Measured: in a child
connected to a parent PORT, Icarus 12.0 and Xcelium 24.03 resolve both
drivers (`y = x1, xx, 0x, x1` for `b = 11, 10, 00, x1`; rows `pi_in_init`,
`pi_in_net`); connected through a parent VARIABLE (`pi_in_init2`) or at the
top (`pi_in_top`), Icarus gives `y = b` and Xcelium still resolves; the
Yosys 0.53 netlist keeps `01` everywhere (and drives the input); Verilator
5.042 gives the input at every sampled cycle for the variable forms and
rejects the net form (`%Error-ASSIGNIN`). The `Port` used to drop the initializer,
so the model read the connection alone and silently followed Icarus on
`pi_in_init2`/`pi_in_top`. Refused, top and children
(`PortSymbol:initialized-input`, `convert_port_sym`). An ANSI input's
initializer is a port default on the port symbol and is unaffected.

(10) (Round 5 folds, Lane B, 2026-10-28.) An INT-CLASS context-propagating
instance override into a child parameter whose declared WIDTH depends on
another parameter: `fold_ovrw_c #(.W(N + 40), .P(N << 40))` with `parameter
logic signed [W-1:0] P`, default `N = 0`. At `N = 1` P is 41 bits: Icarus
12.0 (and IEEE 1800-2023 §10.8, and slang's elaboration at the point)
evaluate the shift at 41 bits, P = -2^40; the Yosys 0.53 netlist at 32, P
= 0 (at `N = 24`: 24·2^40 against 0). Item (8)'s root conversion carried
the DEFAULT point's 40 bits, where both readings are 0, so the model ran
silently (verifier repro `vq_ovr2`). The extractor refuses such an
override at every point (`InstanceSymbol:override-context`,
`_sym_override_root` with `_sym_param_type_fixed`; refusal rows
`fold_ovrw`, `fold_ovrw_n1`, `fold_ovrw_n24`); a leaf override, an operator
into a fixed-width parameter (item (8)) and into an `int` stay admitted
(rows `fold_ovrwl*`, where the tools agree); a dependent type whose
parameters are literal at every point (`.W(40)`) counts as fixed.

(11) (Round 5 folds, Lane B, 2026-10-28; round 3 verifier minor 4.) An
UNTYPED parameter default or localparam whose self-determined value wraps:
`localparam Y = SB + 1'b1` with `logic [N-1:0] SB = 255` (N = 8). Its
type is its expression's (IEEE 1800-2023 §6.20.2), and slang, the LRM and
the Yosys 0.53 netlist give 0; Icarus 12.0 evaluates an untyped parameter
value losslessly (its default `-gno-strict-expr-width`) and gives 256.
Measured shapes: Icarus widens through `+ - * / **`, unary `-` and the arms
of `?:` (`Z - 1'b1` at `Z = 0`: 511 against 255; `SB * SB`: 65025 against
1; `(SB + 1'b1) / 2'd2`: 128 against 0; `-(SB + 1'b1)`: 256 against 0;
`SS + SS` with a signed 8-bit `SS = 127`: 254 against -2) and stops at a
shift, a comparison, a cast and a select (`(SB + 1'b1) >> 1`, `SB << 4`,
`(SB + 1'b1) == 8'd0`, `$signed(SB + 1'b1)` agree). The model refuses
where the own-type value differs from its reading at 64 more bits with
shifts kept at their own width (`Constant:untyped-overflow`, `Param.lean`
`evalUntyped`; refusal rows `fold_uovf_sb255`, `fold_uovf_n16_sbm1`,
`fold_uovf_sb200`, `fold_uovf_n4_sb15`; rows `fold_uovf`, `_sb100`,
`_n16`, `_n4_sb3` run). The test over-refuses `-SB` and `~SB` (Icarus
keeps their 8 bits), loudly. The width itself differs too: `localparam X =
U + N * 1024` (40-bit `U`, `N = -2097153`) has `$bits(X)` 65 in Icarus and
40 in Yosys, so a 40-bit output that agrees does not show the tools agree.
*(Round 6 correction: the value test did not refuse every measured split —
the WIDTH splits where no value wraps, in the INT class too, and a wrap
beyond 64 extra bits (`2 ** SB` at `SB = 100`: Icarus 1, Yosys 0 for `> 5`)
escaped. Item (12) replaces it as the first refusal; the rows above now
carry `Constant:untyped-width`, the four former PASS rows as recorded
over-refusals.)* *(Round 7 correction: "stops at a shift" holds for a
right shift and for a sized left operand (`SB << 4`); a left shift of an
unsized or INT-class operand widens, item (14).)*

(12) (Round 6 folds, Lane B, 2026-10-29; round 5 FOLDS verifier major 3 and
minor 4.) An UNTYPED parameter default or localparam built with `+ - * **`
on its context chain, WHATEVER ITS VALUE. Icarus 12.0 (default
`-gno-strict-expr-width`) gives it the lossless width of its expression,
slang, the LRM (§6.20.2) and the Yosys 0.53 netlist its own type. Measured
with `$bits` (scratch probes `gaps5/folds/p/uw`): `SB + 1'b1` (8-bit `SB`)
9 against 8, `SB * 2'd2` 10, `SB ** 2'd2` 16, `N + 1` and `5 + 1` (INT
class) 33 against 32, `N * 2` 64, `2 ** N` 32 at `N = 8` and 42 at `N =
40`; carried through `/ % & | ^`, unary `- ~ +` and both `?:` arms
(`(N + 1) / 2`, `M ? N : N + 1`: 33), stopped by a shift, a comparison, a
cast, a select and a concatenation part (`(N + 1) >> 1` 32, `$signed(N +
1)` 32, `{SB + 1'b1}` 8). Observable without any wrap: `(Y + 8'd255) >> 1`
into 8 bits with `Y = SB + 1'b1`, `SB = 5`: Icarus 130, Yosys 2 (verifier
repro `vs_uw`); `{a, B}` with `B = N + 1`: `0x1e00000009` against
`0xf00000009`; `a + C` with `C = N - 9 = -1` into 64 bits: `0x20000000e`
against `0x10000000e`; `{a, E}` with `E = 2 ** N` at `N = 40`: `a·2^42 +
2^40` against `a·2^32`. Before, the model followed Yosys silently (the
INT-class `2 ** N` passed `int32Agrees`, since the 32-bit materialization
hid the unbounded value). Refused at every point, `Constant:untyped-width`
(`Param.lean` `PExpr.icarusWidens` in `evalUntyped`; refusal rows
`fold_uwid*`, `fold_uwidp*`, `fold_uwint*`). Recorded over-refusals: points
where every read context is wide enough (`fold_uwid_n16`), an untyped
parameter overridden by an integer (`fold_uwidp_y6*`, `_y250`: the load gate
refuses the design at its defaults first), the former PASS rows of
`fold_uovf`, and the cv32e40p `register_file_ff` row, whose `NUM_TOT_WORDS`
is read only in dimension and generate bounds. Admitted shapes run (rows
`fold_uwok*`: a shift, a division, a comparison, a reference).
*(Round 7 correction: "stopped by a shift" holds for a RIGHT shift only. A
left shift widens in Icarus — item (14) — and is now refused too; the
`fold_uwok*` shift is a right shift.)*

(13) (Round 6 folds, Lane B, 2026-10-29.) An INT-class override built with
`+ - * **` into an UNTYPED child parameter: the parameter takes the
override's type (§6.20.2), 32 bits in slang and the Yosys 0.53 netlist and
the lossless 33 in Icarus 12.0 (`.W(N + 1)` read as `{a, W}`:
`0x1e00000009` against `0xf00000009` at `N = 8`, `a = 15`). Before, the
model followed Yosys silently. Refused by the extractor
(`InstanceSymbol:override-untyped-width`, `_sym_override_root` with
`_sym_param_untyped` and `_sym_icarus_widens`; refusal rows
`fold_uwovr*`); a leaf override and one into a typed parameter run (rows
`fold_uwovl*`).

(14) (Round 7 folds, Lane B, 2026-10-29; round 6 FOLDS verifier blocker 3.)
An UNTYPED constant built with a LEFT shift. Icarus 12.0 widens `<<` and
`<<<` by the shift amount where the left operand is or contains an unsized
or INT-class operand; slang, the LRM (§6.20.2) and the Yosys 0.53 netlist
keep the 32-bit `int`. Measured with `$bits` (verifier probes
`gaps5/vfolds/w/w3.sv`, `w4.sv`): `1 << N` is 40 bits at `N = 8` and 72 at
`N = 40`, where the value is 2^40 against Yosys's 0; `1 << 3` 35, `7 << 1`
33, `(N | 1) << 2` 34; `1 <<< N`, `'d1 << N`, `2 << N` widen the same way,
and `(1 << N) | 1`, `(1 << N) / 2` (2^39 against 0 at `N = 40`) carry it. A
sized left operand keeps its width (`SB << 4` is 8 bits). Read as
concatenation parts the two tools' traces split at every point measured
(rows `fold_shl*`: `{a, C}` with `localparam C = 1 << 3` is `a·2^35 + 8`
against `a·2^32 + 8`). Before, the model followed Yosys silently
(verifier logs: lean equals the netlist, the netlist differs from Icarus,
on `vw_shl`, `vw_shp`, `vw_sho`). Refused at every point: a left shift
counts as widening in `PExpr.icarusWidens` (`Constant:untyped-width`;
rows `fold_shl*`, `fold_shp*`) and in the extractor's `_sym_icarus_widens`
(`InstanceSymbol:override-untyped-width`, `.W(1 << N)` into an untyped
child; rows `fold_sho*`). `SB << 4` is refused too, a recorded
over-refusal.

(15) (Round 7 folds, Lane B, 2026-10-29; round 6 FOLDS verifier blocker 2.)
An ENUM member initializer with an unbased-unsized literal. IEEE 1800-2023
§5.7.1 fills `'1` to the enum's base width, and slang does: `typedef enum
logic [N-1:0] {EA = '1, EB = 0}` has EA = 15 at `N = 4`, 255 at `N = 8`,
2^33 - 1 at `N = 33`. Icarus 12.0 and the Yosys 0.53 netlist both give
EA = 1 at every point, the default included (`{a, EA}` at `a = 15` is 241
in both), and in a module with one point. The envelope carried slang's
default-point 15, which the model bound at every point, so it followed
neither side at `N = 8`. Refused at every point and in every scope,
package enums included (`EnumValueSymbol:unsized-literal-member`,
extractor `_sym_enum_unsized_member`; rows `fold_enw*`, `fold_enu`): a
member of an enum any of whose initializers contains `'0`, `'1`, `'x`,
`'z` (also inside `~'0`). `'0` gives 0 in every tool (the enum's `KB` in
`fold_enw` is 1 everywhere) and is refused too, a recorded over-refusal.

(16) (Round 7 folds, Lane B, 2026-10-29.) An ENUM member value that does
not fit the base width at a non-default point. `typedef enum logic [N-1:0]
{SA = 9, SB = 2}` (default `N = 4`) at `N = 3`: slang reports
`EnumValueOutOfRange`, Icarus 12.0 refuses to elaborate ("Enumeration name
SA has a value that is too large"), and the Yosys 0.53 netlist truncates
SA to 1 — the value the model computed, since it truncates the default
point's member values to the point's base width (`Param.lean`
`enumMemberVals`). At `N = 1` (`{T0, T1, T2}`) Icarus also reports the
overflow and the duplicate value, and Yosys reads T2 = 0. Refused: every
member of an enum whose base width depends on the point
(`EnumValueSymbol:default-point-value`; rows `fold_enb*`), at the points
where the members fit too (the tools agree there on SA = 9, T2 = 2 — a
recorded over-refusal).

(Lane A round 5, 2026-10-29; refusal-only. Each shape below was admitted
after round 4 with one side of the split, or with no oracle. Probes under
the session scratchpad `gaps5/init/d/`.)

(A1) An UNSIZED SIGNED based literal (`'sb1`, `'sh8`, `'shF`, `'so7`):
Icarus 12.0 sizes it to its DIGITS and sign-extends, in every context
measured — `logic [7:0] t = 'sb1` and `assign e = 'sb1` read `11111111`,
`'sh8` `11111000`, `'shF` into 40 bits forty ones, `a + 'sb1` is `a - 1`,
`localparam P = 'sh8` is -8, `V['sb1]` selects bit -1 (x), `'sb1 ==
32'hffffffff` is 1, a `case` item `'sb1` misses `s = 1`, `'sb1 >>> 1` is
all ones. Verilator 5.042, Yosys 0.53 (`prep` and netlist), Xcelium 24.03
(initializers, INIT2 verifier) and IEEE 1800-2023 §5.7.1 (an unsized
literal has at least 32 bits, its digits zero-padded) give `00000001`,
`00001000`, `0...01111`, `a + 1`, 8, bit 1, 0, a match, 0. `'sd…` decimals
and digits whose top bit is 0 (`'sb01`) agree. The model followed the LRM
(at 2e8c8b28 in expressions; in round 4 also in initializers, which were a
loud `SignedResize` before). Refused wherever such a token appears in the
sources (`IntegerLiteral:unsized-signed`, a syntax scan) and on the
declaration itself (`Initializer:unsized-signed`); rows
`pi_unsized_signed`, `pi_unsized_signed_n32`, `ux_signed`. Over-refuses the
agreeing `'sd`/top-bit-0 forms, recorded.

(A2) An unsized x/z literal widened inside an INPUT PORT ACTUAL (INIT2
verifier repro `p8`): `.i('hx0)` into a 40-bit port is `00000000` then 28
x then `0000` in Icarus 12.0 ("Padding 8 high bits of the port" — the
actual sized self-determined, item "Port connection width context" below),
36 x then `0000` in Xcelium 24.03 and Yosys 0.53 (`40'hxxxxxxxxx0`, the
netlist too), which §10.8/§23.3.3 support. `'bz` into 36 bits, `'hz1` into
48, `s ? 'hx0 : 'h5` and `'hx0 | a` (8-bit `a`) split the same way. The
model followed Icarus at 2e8c8b28 (a zero-extending `Resize`) and
Xcelium/Yosys after round 4; refused (`PortConnection:unsized-xz`, row
`pa_unsized_xz`). An actual whose own width reaches the port (`s ? 'hx0 :
40'd5`, `'hx0 ^ b` with a 40-bit `b`) agrees in every tool and is refused
with them (recorded over-refusal); a narrowing or 32-bit port is unchanged.
[CORRECTED, round 5 repair, 2026-10-29: the refusal fired only where the
port was wider than the literal at the BOUND point (the defaults, the
first generate-for iteration). A `W = N` port is 32 bits at a 32-bit
default and 40 bits at `N = 40`, where the model zero-extended the 32-bit
literal with Icarus against the netlist (`vp1`, `vp2`), and an 8-bit
default folded the actual to 8 bits, wrong against both tools at `N = 40`
(`vp7`). An actual holding an unsized x/z-top literal is now refused at
ANY port width; a narrowing or 32-bit port is a recorded over-refusal
(probe `gaps5/init2/d/ov4.sv`: `.i('hx0)` into 32 bits and `.i('hz1)` into
8 bits agree in Icarus and the netlist). Rows `pa_unsized_xz_p*`,
`pa_unsized_xz_g`, `pa_unsized_xz_n*`.]

(A3) An unsized x/z literal widened in a CONSTANT position: `localparam
logic [39:0] LP = 'hx0` reads 36 x then `0000` in Icarus 12.0 and
`40'h00xxxxxxx0` in Yosys 0.53 (`prep` and the synthesized netlist) and in
slang's own constant; an instance override `#(.P('hz1))` into `parameter
logic [39:0] P` likewise (36 z then `0001` against `00` then 28 z then
`0001`); an UNTYPED `localparam LQ = 'hx0` read in a 40-bit context the
other way round (Icarus zero-extends the 32-bit value, Yosys
`40'hxxxxxxxxx0`). All three were loud in the model at 2e8c8b28, in round
4 and now: the Lean constant tier refuses every x/z constant ("x/z literal
in a constant context"). The shape that was NOT loud is a `case` item:
`case (b) 'hx0:` over a 40-bit `b`. Icarus 12.0 and Yosys's `prep` pad the
item with x, but the synthesized netlist reads the x as a don't-care (`b
= 00000000` then 28 x then `0000`: Icarus 2, netlist 1; item 2 of
"Synthesis-side divergences" below); 2e8c8b28 zero-padded the item (`b =
x…0000`: model 2, both tools 1) and round 4 followed Icarus. Every
`_SymPos` position (parameter values, overrides, `case` items, selects,
generate headers) is now `ConversionExpression:unsized-xz-constant` in the
extractor (row `ux_const`, which carries all three shapes).

(A4) An unsized x/z literal as an UNPACKED-ARRAY assignment-pattern element
(`logic [39:0] m [0:1] = '{'hx0, 'hz1}`, INIT2 verifier `ap`): Icarus 12.0
refuses the declaration ("sorry: Assignment to an entire array or to an
array slice is not yet supported") and Yosys 0.53 does not parse it, so no
value is checkable; at 2e8c8b28 each element was a zero-extending `Resize`
that `instDecl` refused, and round 4 padded them into admitted literals.
Loud again (`Initializer:unsized-xz-element`, row `ux_array`).

(Lane A round 5 repair, 2026-10-29; refusal-only. Repros of the verifier of
the round-5 INIT repair, `gaps5/vinitA/d/`; Icarus and netlist traces in
its `o1`-`o5`.)

(A5) An x/z literal in a scope whose context widths differ between points
(a module with an overridable parameter, a generate-for body). This is not
a tool split but a model bug: the envelope fixed the literal's value at
the default point. `assign y1 = 'hx0` into `[N-1:0]` with `N = 32` by
default carries no conversion, and at `N = 40` the model zero-extended the
32-bit literal (8 zeros, 28 x, `0000`) where Icarus 12.0 and the Yosys 0.53
netlist give 36 x then `0000` (`vp3`; the child form `vp4`, silent in
`name.sem`; the `case` item `'hz1` at `N = 40`, `vp9`: model 2, both tools
1). With `N = 8` by default slang folds the literal to `xxxx0000`, and the
sized `12'hxF0` to `11110000` (`vp6`, `vp8`: the cross-check reports the
silent default-point fold; at `N = 40` Icarus and the netlist give 28
zeros then `xxxx11110000`). Identical envelopes at 2e8c8b28, round 4 and
round 5. Refused by the scan `_sym_xz_literal_scan`
(`IntegerLiteral:unsized-xz-parametric`,
`ConversionExpression:xz-literal-parametric`; rows `ux_pdep*`,
`ux_pdep_child`, `ux_pdep_narrow*`, `ux_pdep_sized*`, `ux_pdep_case*`),
except a declaration initializer `_sym_decl_init` decides from the literal.

(A6) `$unsigned` of an unsized x/z-top literal widened by its context
(`ex3`): `assign y1 = $unsigned('hz1)` into 40 bits is 8 zeros, 28 z,
`0001` in Icarus 12.0 (the self-determined 32-bit value zero-extended),
36 z then `0001` in the Yosys 0.53 netlist; `$unsigned('hx0)`,
`$unsigned('bz)` and `$unsigned('hz1) | a` split the same way. The model
followed Icarus at 2e8c8b28 and since (identical envelopes). Refused in any
scope (`CallExpression:unsized-xz-cast`, row `ux_unsigned_cast`). In the
same probes `$signed('hz1)` (36 z then `0001`) and `$unsigned($signed('hz1))`
(8 zeros, 28 z, `0001`) agree in both tools; the first is unchanged, the
second is refused with the class (recorded over-refusal; probe
`gaps5/init2/d/ov3.sv`).

(R6a, cited elsewhere as R6-1) (Round 6 lane A, 2026-10-29; Xcelium 24.03-s004 as reference, audit
`docs/sv-xcelium-audit.md`.) Three shapes on which Xcelium departs from the
explicit IEEE 1800-2023 text while the model, Icarus 12.0, Yosys 0.53 and slang
follow it, or (the third) three simulators depart from it together. Per the
2026-10-29 policy — where the tools split, or where the model would follow one
oracle against the LRM, refuse loudly — none is declared and none is followed;
each is a fixture with a loud-refusal row (`measured` names the Xcelium
value). (i) A constant part select PARTLY out of range, read or write, either
side: the LRM reads x in exactly the out-of-range bits and writes exactly the
in-range ones, Xcelium reads the whole select as x and drops the write
(`ArraySel:partial-overhang`, `Select:partial-overhang`; "Linearized packed-array
indices" above; rows `overhang_read_n4`, `overhang_write_n4`,
`overhang_legacy_k6` and 33 flipped rows). A select wholly outside (x read,
no-op write) and a single-bit select agree in every tool and are unchanged;
a RUN-TIME base that leaves the vector cannot be refused statically (audit P2).
(ii) A NET formal fed by a bare, narrower NET actual: zero-extended by the
model and four tools, z-filled by Xcelium (`PortConn:net-width`, "Port
connection width context" above; rows `net_width_min`, `hier_width*`). (iii) A
bit-select index wider than 32 bits: whole in the LRM text, the model and Yosys
`prep; eval`, truncated to 32 bits by Xcelium (BIGWBS), Icarus and Verilator
(`Select:wide-index`, "Select indices wider than 32 bits" above; rows
`wide_index_n40`, `fold_pcase_*`; only code the point instantiates is judged,
rows `wide_index_dead_n40`, `wide_index_dead_n40_live`; a wide WRITE target at the
default point reaches the envelope as `AssignmentExpression:target`, row
`wide_index_wr`). Recorded gaps: the net-to-net output twin,
a part- or bit-select of a net actual, and a wide index judged only where the
point's width table knows the index (a generate-local declaration is not
judged).

## Refused where the tools agree but `name.sem` cannot follow (2026-10-28)

Two shapes have a single answer in Icarus 12.0 and Yosys 0.53 that the
proof-facing family `name.sem` (`PDesign.instantiate2`) does not compute,
so the differential runner refuses them loudly instead of recording a
disagreement; neither is a row. (1) A 32-bit `int` overflow in INT-class
constant arithmetic: `v[(N*N) >> 30 +: 4]` with `parameter int N = 65536`
selects `v[3:0]` in both tools (`N*N` wraps to 0) and `v[7:4]` on the
model's unbounded constant tier. `PDesign.int32Agrees` rebuilds the point
with exact 32-bit arithmetic (`IEnv.int32`); the runner and
`load_design_sv2` (at the defaults) refuse a point where the designs
differ. (2) A value-position read of an untyped parameter with a non-`int`
default (`parameter P = 3'd5`) at a point where an integer override makes it
an `int` (IEEE 1800-2023 §6.20.2): the envelope's operators around it were
typed by slang at the default's type (`(P - 6 > 0)` is unsigned there,
signed after `.P(5)`, and the tools agree on `0011` while the tree's
unsigned `>` gives `1100`), so the read is `ParamRef:override-type`. At the
default point, where the type is the default's, it is modelled exactly
(rows `param_types*`).

(3) (Round 4 repair, Lane A, 2026-10-28; refusal rows.) An UNSIZED unsigned
literal whose high-order bit is x or z, widened into a parameter-dependent
context: `assign y = a ? 'hz1 : 'b0;` into `logic [N-1:0] y`. IEEE
1800-2023 §5.7.1, Icarus 12.0, Xcelium 24.03 and Yosys 0.53's reading of
the source agree (36 z then `0001` at `N = 40`, `zzzz0001` at `N = 8`), but
the padded value depends on the context width and the literal's own 32 bits
take part in sizing its expression, so no symbolic tree is exact at every
point: `ConversionExpression:unsized-xz` (rows `ux_expr_p`, `_n8`). In a
module with one point the literal is padded exactly (row `ux_expr`). (4) The
initializer twin: an x/z literal initializer whose extension depends on a
parameter-dependent declared width (`output logic [N-1:0] y = 2'bx1`, or
`= 'hz1`) — `Initializer:x-literal-parametric-width`, "non-literal
initializer" (rows `pi_lit_px*`, `pi_uxz_px*`); an unsized literal of ONE
repeated x/z bit is the same bit at every width and runs (`Fill`, rows
`pi_unsized_xz_p*`).

(5) (Round 7 folds, Lane B, 2026-10-29; round 6 FOLDS verifier blocker 1;
refusal rows.) A CAST whose size or type depends on the point, inside a
localparam initializer or an instance override: `localparam int X1 =
M'(255)`, `X6 = M'(300)`, `.W(M'(300) + 1)`. Icarus 12.0, the Yosys 0.53
netlist and slang's own elaboration at the point agree at every point
measured (X1 = 255 and X6 = 300 at `M = 16`, 40 and 64; X6 = -4 at `M = 4`;
0 at `M = 1`), but slang binds the cast's size away, so the envelope can
only carry its DEFAULT-point fold (-1 and 44 at `M = 8`), which the model
read at every `M`. Refused in a family with more than one point,
`ConversionExpression:default-point-fold` (extractor `_sym_conversion`,
`_sym_bound_syntax_point_dependent`; rows `fold_szc*`, `fold_szo*`; the
default point, where the fold is exact, too). (6) (Round 7 folds; refusal
rows.) A 2-state target narrower than its initializer at the default
point, over a division whose divisor wraps to 0 at the operand's OWN width
but not at the target's: `localparam shortint H1 = 4'd8 / (U + 1'b1)` at a
4-bit `U = 15`. slang, Icarus and the Yosys netlist agree on 0 (the
16-bit context), and so did the round 6 model; round 5 refused it, and the
round 5 rule admits no shape that was loud, so the own-width reading is
required to be defined (`Param.lean` `evalAt`, `PExpr.isSquash2`; rows
`fold_sqd_n4_u15`, `_n7_u127`, `_n8_u255`). A recorded over-refusal.

## Port connection width context (2026-10-28)

A module port connection is a continuous assignment (IEEE 1800-2023
§23.3.3), so the LRM evaluates an input actual at the wider of the port and
the actual — slang binds it that way and Verilator 5.042 agrees. Icarus 12.0
and Yosys 0.53 instead evaluate the actual SELF-determined and zero-pad it
("Padding 2 high bits of the port"). Measured on `p + q` (two 2-bit
operands, `p = 2, q = 3`) into a 4-bit port: `0101` in Verilator, `0001` in
Icarus and Yosys; `~p` (`p = 01`) into a 4-bit port: `0010` in Icarus and
Yosys where the context reading gives `1110`. The two readings agree when
the actual is at least as wide as the port (truncation commutes with the
operators) and when widening cannot change a bit (rigid operands, `& | ^`
and `?:` over them, comparisons, unsigned conversions). The flattening
(`LeanModels/Sv/Hier2.lean`, `PExpr.portSafe`/`portInOk`) refuses every
other narrower actual loudly (`PortConn:context-width`) rather than pick a
reading — a post-synthesis check against Yosys would otherwise surface the
LRM reading as a mismatch, and the LRM-faithful one would be the one Yosys
"disagrees" with. Not a row.

Unbased-unsized fills (`'0 '1 'x 'z`) are the exception, and here Icarus
12.0 stands alone. A fill takes the width of its context (§5.7.1), so the
LRM reading of `a ^ '1` (2-bit `a`) into a 4-bit port is `{2'b11, ~a}`, and
Verilator 5.042 and Yosys 0.53 (`prep; flatten; eval`) both give it. Icarus
sizes a fill NESTED under an operator self-determined and zero-pads the
actual (`{2'b00, ~a}`): `a ^ '1`, `a | '1`, `s ? '1 : a`, `a | 'x`,
`a ^ 'z`, `s ? 'z : a`, `'1 & '1`, `(a ^ '1) | b`, `'1 ^ '0` and
`s ? '1 : '0` all differ in their upper bits. The model keeps the LRM
reading, admitting fills anywhere in a port-safe actual. Row
`hier_fill_ctx` (`Examples/system-verilog/sem2/hier_fill_ctx/`, those ten
shapes, exhaustive over the two-state inputs plus x/z points) is the
declared Icarus disagreement `iverilog-port-fill-self-determined`; on its
32 two-state points Yosys agrees with the model on all ten outputs and
Verilator on the seven two-state ones (Verilator rejects the `'x`/`'z`
operands as tristate constructs). A bare fill, and fills whose widened bits
are masked (`a & '1`, `a & 'x`, `s ? '0 : a`, `(a ^ '1) & b`), agree in
every tool: row `hier_fill`, a verified Icarus match, Yosys agreeing on
every two-state point. Xcelium 24.03-s004 (round 6, 2026-10-29) agrees with the
model on `hier_fill_ctx` in all 36 cycles (pinned in
`harness/sv/xcelium_golden.json`; `xmelab` warns `CUVMPW`, port sizes differ, and
still extends the fill to the port width), so only Icarus departs; a verifier
design with a 3-bit actual into an 8-bit port and 14 actual shapes found
Icarus differing on seven of the shapes in 41 of 41 samples, on the `?:` shape in
20 of 41 and on the `+` shape in 6 of 41, and Verilator and the Yosys netlist
matching Xcelium on all 41 samples (the controls outside a port actual agree in
all four tools).

UNSIZED BASED literals with an x/z high-order bit (`'hx0`, `'bz`) in an
input actual narrower than the port split the same way, but with Yosys on
the LRM side (round 5 Lane A, 2026-10-29): Icarus 12.0 zero-pads the
port, Xcelium 24.03 and Yosys 0.53 extend the x/z. Unlike the fills they
are refused, not declared: the model had followed each side in turn
(2e8c8b28 Icarus, round 4 Yosys) without a row, and a declaration is a
lead decision. `PortConnection:unsized-xz`, item (A2) above, row
`pa_unsized_xz`. [Round 5 repair: at any port width, since the port can be
wider at a point other than the bound one; rows `pa_unsized_xz_p*`,
`pa_unsized_xz_g`, `pa_unsized_xz_n*`.]

NET TO NET (round 6, lane A, 2026-10-29; REFUSED). The rule above reads
a narrower input actual as zero-extended, and for a bare reference to a
NET fed into a NET formal that is where Xcelium 24.03-s004 stops agreeing
(docs/sv-xcelium-audit.md, cluster H1; rows `hier_width`, `hier_width_n2`,
`hier_width_n6`, minimal repro `net_width_min`): with
`child(input logic [5:0] i, ...)` and a 2-bit input port `s`, `.i(s)` gives
`i = 000001` at `s = 01` in the model, Icarus 12.0, Verilator 5.042, Yosys 0.53
(`assign p = { 4'h0, s }`) and slang (an implicit `logic[1:0] -> logic[5:0]`
conversion, diagnostic PortWidthExpand), but `zzzz01` in Xcelium: it binds the
two nets bit for bit and leaves the formal's high bits undriven (warning
`CUVMPW`; §23.3.3.7 permits collapsing nets and says nothing of widths; §23.3.3,
§23.3.3.8 and §10.7 imply the zero-extension). The audit's `~i` observable
turned the z into x. An `input logic [W-1:0]` without `var` is a net
(§23.2.2.3); the shape that z-fills is a net formal fed by a whole net
identifier (a `wire`, a tri net, an input port, the output of another
instance), measured on 31 + 21 isolated cases. What zero-extends in Xcelium
too, and stays admitted: a VARIABLE actual (assign-, comb- or always-driven
`logic`), a proper part-select, a constant, any expression (`{s}`, `s ^ 2'b10`,
`?:`, `+`), a `var` formal or a 2-state formal even with a net actual (row
`net_width_ok`). Round 6 repair (verifier finding): an OUTPUT port of the
instantiating module is a net only without an explicit data type — `output wire`
and an implicit-type `output` are nets (Xcelium z-fills them, `pw = zzzz01` for a
vector and `zzz0` for a scalar; rows `net_width_outwire` and `net_width_outwire1`,
which the model refuses, see below), while `output logic`, `output reg` and `output var logic` are VARIABLES
(23.2.2.3) that every tool zero-extends, Xcelium included (rows `net_width_outvar`
and `net_width_outvar1`, admitted: the Xcelium 24.03-s004 trace equals Icarus 12.0
in every cycle). Net OUTPUT actuals are refused earlier than the net-to-net rule: a
VECTOR net declaration by the cross-check (`unrecoverable packed dimensions`: the
symbolic tier does not recover the packed dimensions of a `wire [1:0]`, row
`net_width_outwire`), a SCALAR net output by the model (`assign target 'ow'
undeclared`, row `net_width_outwire1`), so `PortConn:net-width` is reached through
slang-Variable ports (`input logic`); the extractor's mark on an output net stays as
the guard for the day those become admissible. slang reports an
`output logic` with the same header and empty `var` as an `input logic`, so the
extractor decides by the direction token (`_sym_symbol_net_kind`). The extractor
marks the connection (`"net": true` on a
CONNECTED input `PortConn`, `_sym_net_bound_actual`: net formal, 4-state, bare
net actual, widths not both fixed with the formal not wider) and the flattening
is loud where the actual is narrower than the port at the instance's own point
(`PortConn:net-width`, `Hier2.lean` `connProcs`). Recorded gaps, not
refused: a full-range part-select and a constant bit-select of a net actual
(Xcelium z-fills those too), and the OUTPUT twin (a narrower output formal into
a wider whole NET target leaves z in Xcelium, `zzzz11`, while a wider variable
target zero-extends; no row exercises it and `PConn.output` carries no net
information).

Unconnected input ports read z for a net (`input logic a`, `input wire`)
and x for a `var` variable in Icarus 12.0, which the model follows (rows
`hier_nested*`); Verilator is two-state (0) and Yosys leaves the port
undriven (its `eval` reports nothing for it), so neither is an oracle for
that shape.

A CONNECTED `input var` port is an Icarus 12.0 divergence (verifier probe
2026-10-28, re-measured): with `module uc (input var logic [3:0] v, output
logic [3:0] yv)` connected as `.v(a)` to the parent's own input `a`, Icarus
warns "input port v is coerced to inout" and then reads the parent's input
`a` itself as `xxxx` in every cycle (at `a = 0101`: `a`, `zv` and a parallel
`assign b = a` all read `xxxx` inside the DUT). The LRM makes a variable
input port a variable driven by one continuous assignment from its actual
(§23.3.3), and the model flattens it to exactly that (`zv = a`); Verilator
5.042 agrees with the model. No row carries the shape; a future one must be
declared as an Icarus disagreement, or it will read as a model bug.

## Ambiguous conditional with z on both arms (2026-10-28)

When the condition of `?:` is x or z, the result merges the two arms bit by
bit (IEEE 1800-2023 §11.4.11, Table 11-20), and the table merges z with z to
**x**. Icarus 12.0 keeps z there: `c ? a : {s, c}` at `c = z`, `a = 3'bx1z`,
`s = 2'b00` gives `xxz` in Icarus and `xxx` in the model (which implements
the table, `Logic.merge` in `LeanModels/Sv/Basic.lean`); at `c = x`,
`a = 3'bzzz`, `{s, c} = 3'bzzx`, Icarus gives `zzx` and the model `xxx`.
Found by the verifier on the repros `w_dyn` (through an instance port) and
its flat twin `w_dyn_flat` — so the divergence is not hierarchy-specific —
and re-measured on a two-assignment probe. No current row reaches a z/z bit
under an x/z condition; one that does is an Icarus disagreement to declare,
not a model bug.

## Synthesis-side divergences (Yosys 0.53)

svGolf proves designs correct about `run2` and scores the netlist Yosys
synthesizes from the same source, so the shapes on which Yosys reads the
source differently from the model are the ones a player can win on with a
design whose proved behaviour is not the scored hardware's. The svGolf
post-synthesis check (simulate the netlist against `run2` and the spec)
is where they surface, and it must FLAG a design that
relies on one of them, not discard the mismatch as noise. Each shape below
is measured on the RTL in Icarus 12.0, under Yosys 0.53 `prep; eval`, and
on the netlist of `synth -flatten; abc -g gates` simulated in Icarus
(2026-10-28; verifier probes `ac_uniq`, `ac_casew`, `v4.sv`, re-measured as
`uq`/`pq`/`u0q`/`uqd`/`xq`/`zq`).

**Lean = Icarus = IEEE, Yosys differs.** Both are `always_comb` shapes the
symbolic tier and the always_comb proof API accept (`lowerComb` is `some`
on each probe); neither is refused.

1. **`unique case` / `priority case` with no matching item.** IEEE 1800-2023
   §12.5.3 makes a no-match a violation report and executes no item, so in
   `y = 4'b0; unique case (s) 2'd0: y = a; 2'd1: y = b; endcase` the output
   keeps the value the block gave it: `y = 0000` at `s = 2` and `s = 3` in
   the model and in Icarus. Yosys reads `unique` and `priority` as
   `full_case`: `prep; eval` gives `y = xxxx` there, and the synthesized
   netlist resolves the don't-care to `y = a` (`0011` for `a = 0011`).
   `unique0 case` (parallel but not full) agrees in every tool, and so does a
   `unique case` with a `default` item.
2. **x or z bits in a plain `case` item constant.** Plain `case` matches with
   `===` (§12.5.1), so the item `2'bx1` matches only a subject that is
   literally `x1`: in `case (s) 2'b11: y = 3; 2'bx1: y = 4; default: y = 6;`
   the model and Icarus give `y = 6` at `s = 01`. Yosys's `proc` compares an
   item with `$eq`, which is x when the constant has x or z bits: `prep;
   eval` gives `y = 01x0` at `s = 01` (the bitwise merge of 4 and 6) and the
   synthesized netlist gives `y = 4`, the x bit read as a wildcard. A z bit
   behaves the same way (`2'bz0: y = 5`: `01xx` under `eval` and `0101` in the
   netlist at `s = 00` and `s = 10`, where the model and Icarus give 6).
   Only `casez`, `casex` and `case inside` make such bits wildcards in the
   language (`casez (s) 2'b?1:` is refused by the symbolic tier,
   `CaseStatement:WildcardJustZ`).
   [Round 5 repair note, Lane A, 2026-10-29. This item stands: a sized x/z
   item (`2'bx1`) stays admitted, and so do x/z constants under operators,
   which the netlist also reads as don't-cares (`a == 'hx0`, verifier
   `pf` `yc11`; `'hx0 | a`; `$signed('hx0) | a` into 40 bits, Icarus 8
   zeros, 24 x, then the OR, the netlist forty ones; at `a = 11111111`,
   `a ^ 4'bx1z0` into 16 bits is `…1111x0x1` in Icarus and `…111100x1` in
   the netlist, and `a[0] ? 8'bzz01xx10 : 8'h0f` is `…zz01xx10` and
   `…00010010`; probes `gaps5/init2/d/ov1.sv`, `ov3.sv`; `a[0] ? 'bx : 'h5`,
   Icarus x, the netlist `5`, measured as a port actual in `ov4.sv` and
   refused there by (A2)). The `case` item refusal of (A3) and the x/z refusals of
   (A2), (A5) and (A6) are NOT a policy of refusing this reading: each
   refuses a shape for its own reason (a split between Icarus and Xcelium,
   a value fixed at the default point, a zero- versus x/z-extension), and
   that a refused shape is also read as a don't-care by the netlist makes
   the refusal a superset of this item there (an over-refusal, recorded).
   Whether the general netlist reading of x/z constants should itself be
   refused is routed to the lead as ONE recorded decision; it is not
   decided shape by shape.]

3. **Operators in a plain `case` item** (round 3 repair, 2026-10-28; rows
   `fold_lshr*`). §12.5 and §11.6.1 (Table 11-21) evaluate the case
   expression and every item at the widest of them, so in `case (s)
   2'b11 + 2'b01: o3 = 1; 2'b10 + 2'b11: o3 = 2;` with a 4-bit `s` the items
   are 4 and 5: the model, Icarus 12.0 and Verilator 5.042 give `o3 = 1` at
   `s = 4` and `o3 = 0` at `s = 0`. Yosys 0.53 evaluates each item at its
   own 2 bits (0 and 1): `prep; eval` gives `o3 = 01` at `s = 0` and `10`
   at `s = 1`, and so does the synthesized netlist. Where the case is no
   wider than its items (`fold_lshr_n1`, `fold_lshr_n2`) every tool agrees.
   The same reading explains the existing row `case_width` at `N = 33` and
   `N = 40`: the item `-1` matches an all-ones subject wider than 32 bits in
   the model and Icarus (the negation runs at the case width), while the
   netlist compares the 32-bit `-1` zero-extended and does not match.
   Rows `fold_rcase_n31`, `_n40`, `_n40_p5` (round 4) show it on `-P` and
   `~P` items (`int P`): the model and Icarus zero-extend `P` into the wide
   case before the operator; the netlist matches the 32-bit `-P` zero-
   extended (`3` at `P = -3`) instead.

**The other directions, recorded elsewhere.** Yosys agrees with the model
and Icarus does not on a single-element range (above) and on nested
unbased-unsized fills in port actuals (`hier_fill_ctx`, above); a
post-synthesis check cannot see those. Yosys agrees with Icarus and the
model does not on out-of-range inner packed-array selects (above, "Linearized
packed-array indices"); a post-synthesis check surfaces those as mismatches.
Shapes where Icarus and Yosys disagree with each other are refused (above).
A self-reading `always_comb` (`if (c) t = a; y = t; t = b;`) was the one
place where the MODEL departed from IEEE and Icarus on purpose, because `run2`
settles it the way Yosys synthesizes it (declared divergence `sv-div-3`).
Since 2026-10-28 (WP4) it is refused instead, like the other shapes where
the tools split: Icarus 12, Xcelium 24.03/26.09 and mox-sim give the stale
value, Verilator 5.042, Yosys 0.53 and the settle semantics the
combinational one, so no answer is safe. See "Self-reading `always_comb`:
refused" below; `sv-div-3` is retired (`docs/sv-declared-divergences.json`),
its guards still watched by `harness/sv_divergence_probe.py`.

### Self-reading `always_comb`: refused (2026-10-28, WP4)

IEEE 1800-2023 §9.2.2.2.1 leaves out of an `always_comb` block's implicit
sensitivity list "any expression that is also written within the block", so
an event-driven simulator runs the block once per wake-up and the read of a
bit the block writes LATER sees the previous run's value. `Sem2` re-runs the
block until nothing changes. The two answers differ exactly when, on some
control path, a bit is read before that path writes it and the path writes
it later — the rule the guard refuses (`LeanModels/Sv/CombGuard2.lean`,
applied in `instProcess2` at every parameter point; loud
`AlwaysComb:self-read`). Measured on the rows' own stimulus (each row's `measured` field in
`harness/sv/cases2.json`): Icarus 12.0 through the harness testbench,
Xcelium 24.03 and Verilator 5.042 (`--binary --timing`) on one batched
testbench of all the fixtures; "settle" is `run2` before the guard. Yosys
0.53 `prep; eval` gives the settle answer on EVERY two-state input point of
every shape (4 to 64 points each, 0 mismatches):

| Row | Shape | Icarus `y` | Xcelium `y` | Verilator = settle `y` |
| --- | --- | --- | --- | --- |
| `rbw_comb` | `y = t; t = a;` | 00 00 01 10 | xx 00 01 10 | 00 01 10 11 |
| `rbw_held` | `if (c) t = a; y = t; t = b;` | 01 01 11 | xx 01 11 | 01 10 11 |
| `rbw_bits` | `t[0] = a; y = t[1]; t[1] = b;` | 0 0 1 1 0 | x 0 1 1 0 | 0 1 1 0 0 |
| `rbw_cond` | `if (t) y = a; else y = b; t = c;` | 0 0 1 1 1 | 0 0 1 1 1 | 0 1 0 1 0 |
| `rbw_case_item` | `case (s) t: y = a; default: y = b; endcase t = c;` | 1 1 1 1 | 0 1 1 1 | 1 0 1 0 |
| `rbw_dyn` | `y = t[s]; t = a;` | 0 0 0 1 0 | x 0 0 1 0 | 0 1 1 0 1 |
| `rbw_part` | `t[1:0] = a; y = t[3:2]; t[3:2] = b;` | 00 00 01 10 | xx 00 01 10 | 00 01 10 11 |
| `rbw_nested` | `if (c) begin if (d) t = a; else t = b; end y = t; t = e;` | 0 0 0 1 0 | x 0 0 1 0 | 0 1 0 0 1 |
| `rbw_compound` | `y = a; y += t; t = b;` | 00 00 10 11 | xx 00 10 11 | 00 01 11 01 |

From cycle 1 on, Icarus and Xcelium agree with each other and read the
previous run's value; at cycle 0 they order the block's time-zero run
against the first stimulus differently — a second reason no answer is safe.
Icarus 12 also warns `constant selects in always_* processes are not
currently supported (all bits will be included)` on `rbw_bits`, `rbw_part`
and `acg_bits_ok`: its bit-level sensitivity is approximate, which did not
change any admitted row's trace. `rbw_compound` is refused earlier, by the
extractor (`AssignmentExpression:compound`); lowered to `y = y + t` the guard
refuses it. Admitted and verified against Icarus 12.0 (rows `acg_*`, plus
the earlier `latch_comb`, `fa_comb_proc`, `mux4_case`, `onehot_dec`,
`addsub_comb*`): a latch that reads its own held value, a temporary written
on every path, two temporaries, bit-disjoint reads/writes, part-selects
covering a variable before a whole read, a `case` writing every arm, a
condition read after the write, run-time indices after a whole write, nested
`if`/`case`. One Xcelium 24.03 run (fleet gate `refsim` on `vip-ng`) of the
ten admitted designs (`acg_*`, `latch_comb`) in one testbench gave exactly
Icarus's trace — hence the model's — on all 60 cycles.

### Icarus propagates a copy inside the block's own run: the alias rows are REFUSED (2026-10-29, WP4 round 6 lane B; mechanism measured 2026-10-28, rounds 3 and 4)

The self-read guard is about ONE block re-run on its own result. A block that
reads a DIFFERENT variable which is a continuous copy of one it writes
(`assign w = t; always_comb begin y = w; t = a; end`, the same through a
chain of assigns, a child's input port (a net) and output port tied to one
parent variable, or a copy made by a child's own `assign`) passes it, and
there Icarus 12.0 and the other tools part. Rounds 3
and 4 recorded the rows as declared Icarus departures; on 2026-10-29 Thomas
decided to refuse the shape instead (the Xcelium audit, cluster D4,
`docs/sv-xcelium-audit.md`), and the two declarations are retired (below).

**The mechanism (measured, round 3 verifier, re-measured rounds 4 and 6).**

* The copy stays in the sensitivity list. `iverilog -g2012` compiles
  `acg_alias_assign`'s block to `.event anyedge, w, a` (`w` a `BUFZ` functor
  of `t`) and `acg_alias_port`'s to `.event anyedge, i, a` (`i` a net on the
  variable node of the output port `o`, both connected to the parent's `w`).
* Icarus applies the update synchronously, INSIDE the block's run. The write
  of `t` (`o`) changes `w` (`i`) before the block reaches its event control, so
  the change wakes nothing and the read that came first keeps the previous
  value. The distinguishing probe (`mech_buf`) is `assign w = t; always_comb
  begin y = w; t = a; z = w; end`: Icarus gives `y = 00, z = 01` at `a = 01` --
  `z`, read after the write in the same run, already sees the new `w`, and
  `y` is never refreshed. With `assign w = ~t;` (a `NOT` functor, which Icarus
  schedules) the block is woken and Icarus agrees with every other tool.
* Xcelium 24.03-s004 defers the update until the process has returned to its
  event control and RE-RUNS the block (a `$display` in the block shows two runs
  per change in Xcelium and one in Icarus; `w` read right after `t = a` is
  still old); Verilator 5.042 also runs the block twice; the model's settle
  semantics gives the same answer, `y = a`. Yosys 0.53 `prep; eval` gives
  `y = a`.
* The LRM leaves both orders open. IEEE 1800-2023 §4.7: "At any time while
  evaluating a procedural statement, the simulator may suspend execution and
  place the partially completed event as a pending event in the event region";
  §4.8's own example (`assign p = q; … q = 0; $display(p);`) says "The
  simulator is correct in displaying either a 1 or a 0" (Icarus prints 0,
  Xcelium 1, Verilator 0). §9.2.2.2.1 (the copy is read and not written by the
  block, so it is in the implicit sensitivity list) and §4.3/§4.5 lean towards
  re-triggering, but §4.8
  licenses a different value at an observation point, not a skipped trigger,
  and the classic `always @(w, a)` with the same alias is stale in Icarus under
  rules the LRM permits. The honest classification is an LRM gap with the two
  event-faithful tools on opposite sides; Verilator and Yosys do not model
  event order (on the direct self-read `y = t; t = a` Verilator gives `y = a`
  and the Yosys netlist is `assign y = a`, where §9.2.2.2.1 (b), Xcelium and
  Icarus all give the stale value), so their agreement with the model is not
  evidence.

**The refusal.** The tools split, so by the policy "refuse where the tools
split" the block is refused: loud `AlwaysComb:alias-read`
(`LeanModels/Sv/CombAlias2.lean`; proved sound for control paths in
`CombAlias2Sound.lean`). A body is refused when, on some control path, a
statement reads a bit that is DOWNSTREAM, through at least one continuous
assignment of the flat design, of a bit the path writes at that statement or
later. Details that matter:

* "Continuous assignment" is every `Process2.assign` of the flattened design.
  After `Hier2.lean`'s flattening these include the port connections, so a
  port loop exists only at that level, and the guard runs on the flattened
  design once (a child's signals are `u.w`, `u.t`; the message names the
  instance). The path may leave the block's module and come back:
  `acg_alias_thru` has the parent's block read `w`, the child copies its input
  to its output, the parent ties the input to the variable the block writes
  and the output to `w` (three continuous assignments, none in the parent;
  Icarus stale, Xcelium settled).
* It is TRANSITIVE (the round-3 verifier's probe `assign w = t; assign v = w;
  always_comb begin y = v; t = a; end` is stale 48/48 in Icarus), and it
  follows the dependency path, NOT the functor kind: `assign w = ~t` is refused
  although every tool agrees on it (`acg_alias_not`), because `assign w = t`
  (the same block) does not.
* Bit granularity is the self-read guard's (`Expr2.rdW`, `Stmt2.mayW`,
  `readsViol`): a copy of `t[0]` read before a write of `t[1]` is admitted
  (`acg_alias_bits_ok`), a copy of all of `t` is refused
  (`acg_alias_bits`). A run-time index covers its whole signal.
* NOT refused, because every tool agrees (measured): write then read
  (`acg_alias_wr`, `acg_alias_port_wr`, `acg_alias_hier_ok`); a SEPARATE
  `always_comb` copy, which is a process and is woken like any other
  (`acg_alias_copy`); a copy of a variable the block does not write
  (`acg_alias_far`); and a cross-process pair of `always_comb` blocks.
* It sits BESIDE `name.sem`, like the legacy-select range guard
  (`RangeGuard2.lean`): `load_design_sv2` at the defaults and at every point of
  the probe sidecar, the differential runner at each row's point, and
  `PDesign.aliasReport` for any other tool. `name.sem` itself is the
  unguarded settle family: the recorded lemmas `PDesign.instantiate2_eq`,
  `PDesign.assemble2_processes`, `PDesign.instantiateG2_of_ok`,
  `PDesign.instantiateGD2_of_ok`, `PDesign.instantiateGD2_eq_driverGuard`,
  `Design2.driverGuard_of_ok`, `PDesign.instantiateH_of_rec`, the ∀-N proofs of
  `ripple_add`, `mul2d`, `partsel`, `ripple_fa` and `CombViewMain.lean` (which
  unfolds `instantiateGD2`) are stated for the unguarded family, so a guard
  inside `instantiate2`/`instantiateG2`/`instantiateGD2` would falsify them.
  RECORDED RESTRICTION: `name.sem N` at a parameter point other than the
  defaults and the probed ones does not carry the refusal (the self-read guard
  is in `instProcess2` and does carry it). A ∀-N proof discharges the guard
  with `Design2.aliasGuard_of_noComb` (a design without `always_comb`:
  `ripple_add`, `mul2d`, `ripple_fa`), `Design2.aliasGuard_of_noAssign` (no
  continuous assignment: the proof API's designs, `CombAlias2Example.lean`,
  `as_aliasGuard N` at every width) or `Design2.aliasGuard_of_admits`. `partsel`
  is the one ∀-N family with `always_comb` blocks (two, reading only `b` and
  writing `w_hi`/`w_lo`, which no assign reads): the census finds it admitted
  at every row's point, but no ∀-N statement of that is recorded (a gap).
* What is proved (`CombAlias2Sound.lean`): the fan-out is closed under the flows
  and contains every downstream bit; on EVERY control path of an admitted body no
  read touches a bit downstream of a window written at or after it
  (`Stmt2.aliasViol_epaths`); the guard is idempotent and the identity on
  the designs above. NOT proved: that a simulator which applies the copy inside
  the run reads the same values as one which defers it. `Sem2.lean` has no
  intra-block propagation semantics to prove it against; the argument is the
  measured mechanism above.

| Row | Shape | Stimulus | Icarus `y` | Xcelium = settle `y` | Verilator `y` (two-state) | Verdict |
| --- | --- | --- | --- | --- | --- | --- |
| `acg_alias_assign` | `assign w = t; always_comb begin y = w; t = a; end` | a = 11 10 00 11 00 11 1x 11 | 11 11 10 00 11 00 11 1x | 11 10 00 11 00 11 1x 11 | 11 10 00 11 00 11 10 11 | REFUSED (Icarus stale) |
| `acg_alias_port` | child `always_comb begin y = i; o = a; end`, `.i(w), .o(w)` | a = 00 01 10 01 01 11 00 10 | 00 00 01 10 10 01 11 00 | 00 01 10 01 01 11 00 10 | 00 01 10 01 01 11 00 10 | REFUSED (Icarus stale) |
| `acg_alias_wire` | `wire w; assign w = t;` (one bit), same block | a = 0 1 0 1 1 x 0 1 | 0 0 1 0 0 1 x 0 | 0 1 0 1 1 x 0 1 | 0 1 0 1 1 0 0 1 | refused EARLIER, `NetSymbol:net-z` (not by this guard; the tools split on it too) |
| `acg_alias_chain` | `assign v = w; assign w = t;`, `y = v; t = a;` | a = 11 10 00 11 00 11 1x 11 | 11 11 10 00 11 00 11 1x | 11 10 00 11 00 11 1x 11 | 11 10 00 11 00 11 10 11 | REFUSED (Icarus stale) |
| `acg_alias_not` | `assign w = ~t;`, same block | a = 11 10 00 11 00 11 1x 11 | 00 01 11 00 11 00 0x 00 | 00 01 11 00 11 00 0x 00 | 00 01 11 00 11 00 01 00 | REFUSED, tools agree (guard keyed on the path, not the functor) |
| `acg_alias_bits` | `assign t[0] = b; assign w = t;`, `y = w; t[1] = a;` | (a, b) = 0/0 1/0 1/1 0/1 1/1 x/1 0/0 1/1 | 00 00 11 11 01 11 x0 01 | 00 10 11 01 11 x1 00 11 | 00 10 11 01 11 01 00 11 | REFUSED (Icarus stale) |
| `acg_alias_hier` | the `acg_alias_assign` shape inside a child instance `u` | a = 11 10 00 11 00 11 1x 11 | 11 11 10 00 11 00 11 1x | 11 10 00 11 00 11 1x 11 | 11 10 00 11 00 11 10 11 | REFUSED (Icarus stale) |
| `acg_alias_thru` | the copy is made by a CHILD (`assign o = i;`), the parent ties `i` to `t` and `o` to `w`: `y = w; t = a;` | a = 11 10 00 11 00 11 1x 11 | 11 11 10 00 11 00 11 1x | 11 10 00 11 00 11 1x 11 | 11 10 00 11 00 11 10 11 | REFUSED (Icarus stale) |
| `acg_alias_wr` | `assign w = t;`, `t = a; y = w;` (write, then read) | a = 11 10 00 11 00 11 1x 11 | 11 10 00 11 00 11 1x 11 | 11 10 00 11 00 11 1x 11 | 11 10 00 11 00 11 10 11 | admitted, Icarus = Xcelium = model |
| `acg_alias_copy` | `always_comb w = t;` beside `y = w; t = a;` | a = 11 10 00 11 00 11 1x 11 | 11 10 00 11 00 11 1x 11 | 11 10 00 11 00 11 1x 11 | 11 10 00 11 00 11 10 11 | admitted, Icarus = Xcelium = model |
| `acg_alias_far` | `assign w = a;`, `y = w; z = b;` (a copy of what the block does not write) | (a, b) = 11/00 10/01 00/10 01/11 11/00 x0/11 00/1x 11/01 | 11 10 00 01 11 x0 00 11 | 11 10 00 01 11 x0 00 11 | 11 10 00 01 11 00 00 11 | admitted, Icarus = Xcelium = model |
| `acg_alias_bits_ok` | `assign t[0] = b; assign w = t[0];`, `y = w; t[1] = a;` | (a, b) = 0/0 1/0 1/1 0/1 1/1 x/1 0/0 1/1 | 0 0 1 1 1 1 0 1 | 0 0 1 1 1 1 0 1 | 0 0 1 1 1 1 0 1 | admitted, Icarus = Xcelium = model |
| `acg_alias_port_wr` | child `always_comb begin o = a; y = i; end`, `.i(w), .o(w)` | a = 00 01 10 01 01 11 00 10 | 00 01 10 01 01 11 00 10 | 00 01 10 01 01 11 00 10 | 00 01 10 01 01 11 00 10 | admitted, Icarus = Xcelium = model |
| `acg_alias_hier_ok` | write-then-read inside a child instance | a = 11 10 00 11 00 11 1x 11 | 11 10 00 11 00 11 1x 11 | 11 10 00 11 00 11 1x 11 | 11 10 00 11 00 11 10 11 | admitted, Icarus = Xcelium = model |

Icarus is stale (one change behind) on every refused row except `acg_alias_not`,
and the guard refuses all of them but `acg_alias_wire` (below: an earlier refusal
takes that one); the model equals Xcelium on every admitted
row and Icarus, Xcelium and the model agree there (rows PASS against Icarus;
the Xcelium pins are in `harness/sv/xcelium_golden.json`).

**An internal `wire` never reaches the guard.** The fixture `acg_alias_wire`
(`wire w; assign w = t;`, one bit) is refused EARLIER, by the extractor:
`wire w;` is `Unsupported` `NetSymbol:net-z` (2026-10-28: an undriven net
reads z while the tier initializes every declaration to x, so every internal
net is refused), and so are `wire [1:0] w;` (`unrecoverable packed
dimensions`) and `wire w = t;` (`non-literal initializer`). The row pins that
refusal (`"refusal": "NetSymbol:net-z"`), not the alias guard's; the tools
split on it exactly as on `acg_alias_assign` (measured above), and the guard,
which follows the continuous assignments and never the kind of declaration,
would refuse it were nets admitted. The nets the tier does admit are INPUT
ports (an `input logic` without `var` is a net, §23.2.2.3), and a copy
through one is the port loop `acg_alias_port` (the refusal reads `u.i`, a
net) and the child's copy in `acg_alias_thru`.

**Census (2026-10-29, one Lean process per sweep, `PDesign.aliasReport`).**
Over every sv-0.2 envelope in the tree (494: 294 in `Examples/system-verilog`
and 200 of svGolf's tasks, references and attacks; 150 of them with a probe
sidecar, every probed point checked) at the defaults the guard refuses
exactly six (`acg_alias_assign`, `_port`, `_chain`, `_not`, `_bits`,
`_hier`); the seventh refusal row, `acg_alias_thru`, was added after that
sweep and is refused in the row sweep. Over every row of `harness/sv/cases2.json`
at the row's own parameter point (676 rows): 7 refused (those seven, all
carrying `"refusal": "AlwaysComb:alias-read"`), 662 pass the guard (whatever else
refuses them), and 7 points
that could not be built for an unrelated reason (the `fold_shp*`/`fold_uwidp*`
rows' `Constant:untyped-width`, themselves loud-refusal rows). No simulated
row and no svGolf envelope is
refused (none of the 200 svGolf envelopes, none of the 150 sidecars' points): no
previously admitted design changed behaviour.

### Icarus leaves a partly written variable out of the sensitivity list (2026-10-28, WP4 round 3; corrected round 4)

`acg_xproc_bits` (`always_comb t[0] = a;` beside `always_comb begin t[1] =
b; y = t; end`) is a different case, and there Icarus does depart from a
documented rule. IEEE 1800-2023 §9.2.2.2.1 puts "the expansions of the
longest static prefix of each … select expression that is read" in the
implicit sensitivity list, except "any expression that is also written
within the block": the second block reads `t` (expansion `t[1]`, `t[0]`)
and writes only `t[1]`, so `t[0]` belongs in its list. Icarus 12.0 leaves
ALL of `t` out (`iverilog -g2012` netlist: the block's event is `.event
anyedge, b` alone), without a diagnostic, so a change of `t[0]` does not
wake the block and `y` keeps the previous `t[0]` until `b` changes:

| Row (declaration) | Shape | Stimulus | Icarus `y` | model = Xcelium `y` |
| --- | --- | --- | --- | --- |
| `acg_xproc_bits` (`iverilog-comb-bit-split-sensitivity`) | `always_comb t[0] = a; always_comb begin t[1] = b; y = t; end` | `(a, b)` = 00 10 11 01 11 x1 00 | 00 00 11 11 11 11 00 | 00 01 11 10 11 1x 00 |

The design is LEGAL. Round 3 said §9.2.2.2 forbids it at variable
granularity; the 2023 text says the opposite: "multiple assignments made to
independent elements of a variable are allowed as long as their longest
static prefixes do not overlap … an unpacked structure or array can have
one element assigned by an always_comb procedure and another element
assigned continuously or by another always_comb procedure", and §6.5 makes
each bit of a packed type an independent element. That is exactly ls-sv's
bit-granular one-driver rule (`procExclusiveOk`, `Hier2.lean`), and Xcelium
24.03 and Verilator 5.042 accept it without a report. A variable-granular
refusal would be an over-refusal of a legal design; the declaration is the
right record, and its retirement condition is Icarus keeping the unwritten
bits in the list.

**Which reads Icarus drops (round 6, lane B, 2026-10-29; from the Xcelium
audit's D4 triage and its verifier, minimal repros over a 48-step stimulus).**
The Icarus gap is WHOLE-VECTOR reads only: `y = t` and the constant
part-select `y = t[1:0]` are stale (25 of 48 steps each; 15 of 48 with the
writer on bit 1 and 11 of 48 with `assign t[0] = a`), while the read of the
unwritten bit `y = t[0]` and the concatenation `y = {t[1], t[0]}` are NOT
(Icarus prints `sorry: constant selects in always_* processes are not
currently supported (all bits will be included)` and includes every bit);
`always @*` in place of the second `always_comb` is fine in Icarus. Xcelium
24.03-s004, Verilator 5.042 and Yosys 0.53 give `y = {b, a}` on every shape.
Only Icarus departs, from §9.2.2.2.1 read with §6.5 ("each bit in a packed
type is also an independent element"), so the row stays a declared Icarus
departure and the model is unchanged (it equals Xcelium's pinned trace on
all 7 cycles). This is NOT the alias guard's business: the second block
reads `t` and writes `t[1]`, and no continuous assignment is involved; the
alias guard (above) neither refuses nor changes this row.

**The class reaches further than the row.** The round-3 WP4 verifier found
two more admitted designs on which the model's trace equals Xcelium 24.03's
on every cycle (and Verilator 5.042's with `x` read as 0) while Icarus 12.0
is stale, by the same cause (re-checked in round 4: their second block's
event lists name no bit of `t`):

* `x_dyn`: `always_comb t[0] = a; always_comb begin t[1] = b; y = t[s];
  end` — a run-time read; differs at the cycle with `a = 0, b = 1, s = 0`
  (Icarus `y = 1`, model and Xcelium `y = 0`).
* `x_child`: a child output port drives `t[0]`, and the parent has
  `always_comb begin t[1] = b; y = t; end`; differs at cycles 1, 4 and 5
  (cycle 1, `a = 0, b = 1`: Icarus `y = 11`, model and Xcelium `y = 10`).

So does `assign t[0] = a;` in place of the first block. Each of these is
admitted by `load_design_sv2`, and a differential row of any of them would
fail undeclared against Icarus: such a row needs its own declaration. No
disagreement was found for unpacked-element, packed-2D or struct-member
splits, or for a read of a constant bit (`y = t[0]`), which Icarus does put
in the list.

## Declarations retired in round 6 (2026-10-29)

A declaration is checked only on a row that simulates. These rows became loud-refusal
rows in round 6 (the tools split and the model no longer chooses), so their declarations
were removed from `harness/sv/cases2.json` rather than left behind as data nothing
checks. The records:

| id | row | what it declared | why retired |
|---|---|---|---|
| `iverilog-packed-inner-part-linearized` | `array_oob_part` | Icarus 12.0 and Yosys 0.53 linearize part-selects and indexed parts that overhang an inner dimension of a non-last element, a label outside an ascending dimension, and the write `w[0][5:2] = a` | the row is refused (`ArraySel:partial-overhang`); Xcelium equals neither the model nor Icarus on the part-selects and the write. The one shape on which Xcelium equals the model, `q[0][4]`, is the new declared row `array_oob_asc` (`iverilog-packed-asc-label-linearized`) |
| `iverilog-packed-inner-lsb-write-linearized` | `array_oob_lsbwrite` | Icarus and Yosys write `a[0]` into `w[0][3]` for `w[1][-1 +: 2] = a[1:0]` | refused; Xcelium drops the whole write on the inner dimension and on the 1-D twin. The in-range twin `array_oob_lsbwrite_l1` is unchanged |
| `iverilog-ascending-full-width-minus-select` | `label_kminus_w1` | Icarus reads `t[-1 -: 2]` over the ascending `[-1:0]` as the whole vector | refused; Xcelium reads `xx`, equal to neither side. The in-range halves live on as `label_kminus_q` and `label_kminus_p*` |
| `iverilog-comb-assign-alias-sensitivity` | `acg_alias_assign` | Icarus 12.0 propagates the update of `w` (`assign w = t`) synchronously inside the `always_comb` block's run, so the wake-up is lost and `y` lags `a` by one change (an LRM-permitted tool split, IEEE 1800-2023 §4.7/§4.8); the model, Xcelium, Verilator and Yosys settle | the row is refused (`AlwaysComb:alias-read`, `LeanModels/Sv/CombAlias2.lean`): the design-level alias guard exists, which was the declaration's own second retirement condition. The admitted counterparts (`acg_alias_wr`, `acg_alias_copy`, `acg_alias_far`, `acg_alias_bits_ok`) agree in every tool; see "Icarus propagates a copy inside the block's own run" |
| `iverilog-comb-port-loop-sensitivity` | `acg_alias_port` | the same mechanism through a child's input and output ports tied to one parent variable (the loop exists only after flattening) | refused by the same guard, which runs on the flattened design; the admitted twin `acg_alias_port_wr` (write, then read) agrees in every tool |
| `iverilog-wide-index-truncation` | `fold_pcase_wide` | Icarus (Verilator on a plain `v[a]` too) truncates a bit-select index wider than 32 bits to its low 32 bits where the model and Yosys read the whole value; "no licensed-simulator confirmation is claimed" | CONTRADICTED: Xcelium, the reference, truncates too (`BIGWBS`), so the model is alone with the LRM text against three simulators; refused (`Select:wide-index`), see "Select indices wider than 32 bits" |

`iverilog-single-element-minus-select` (`array_param_labels_l7`) is the one declaration
kept on a refused row, at the lead's decision: it records the Icarus lowering of `-:` over
a single-element range, which Xcelium's elaboration diagnostic corroborates ("Single-element
range direction"); nothing checks it while the row is refused.

## Unavailable oracles

Icarus 12.0-2build2 cannot provide traces for twenty-three current fixtures:

| Group | Cases | Observed failure |
| --- | ---: | --- |
| Indexed packed-member targets | 5 | compiler assertion in `elab_net.cc` |
| Noncanonical packed-member targets | 11 | compiler rejection, or a runtime assertion in `vvp_net.cc` |
| Whole fixed-array initializer | 1 | assignment to an entire array is unsupported |
| Fixed-array streaming targets and packed streaming sources | 5 | streaming concatenation is unsupported |
| Packed aggregate in an array | 1 | compiler assertion in `elab_expr.cc` |

These cases still run through Lean and attempt Icarus compilation/simulation.
An `icarus_unavailable` entry in `cases2.json` binds the source, envelope,
stimulus and testbench, and enumerates measured failures. Each failure
records its stage, exact exit status, stdout and stderr. Only the source
filename is replaced by `<source>` for portability. Repeated Ubuntu 24.04
probes, including sixteen repeats per noncanonical source, capture the
observed diagnostic variants. Unknown errors remain hard failures. A failure
that disagrees with a declaration also prints its complete observed stage,
status, stdout and stderr for review. Homebrew Icarus 12.0 on macOS fails on
the same twenty-three fixtures: the seven compiler rejections match their
declarations byte for byte, and the sixteen crashes (the `elab_net.cc`,
`elab_expr.cc` and `vvp_net.cc` assertions) match through the host-framing
canonicalization described at the top of this page (measured on the full
`diff_test2.py` suite, 2026-10-28).

The harness prints `UNAVAILABLE ORACLE`, retains the diagnostic, emits a CI
warning, and counts the case as skipped if no other simulator verifies it.
It never counts a missing trace as agreement. A run consisting entirely of
unavailable oracles exits with failure. A successful Icarus run also fails
while the declaration is live, requiring its retirement before normal
comparison resumes. Xcelium continues to execute and compare these cases
when admitted by its readiness probe.

These entries record gaps in oracle coverage. They do not establish
simulator agreement for the affected source programs or exclude the
constructs from the language tier's scope.
