# The tools-split audit (2026-10-31)

Status: measured 2026-10-31 on branch `wprc` (from `svgolf-prep` 05e59add), revised the same day after an adversarial
review (see "Corrections" below). This page audits every register row (`docs/sv-refusals.json`) whose `never` reason is
"the tools split" (principles `P-NO-SILENT-PICK` and `P-DETERMINISM`) and the six rows of section A (the frontend rejects
the program), against Thomas's rulings of 2026-10-31. The register carries the verdicts; this page carries the evidence.
Reproduce with `harness/sv/tools_split_audit/` (README there). The 18 `rbw_*` / `acg_alias_*` rows were re-run in all
four simulators for this revision and reproduce exactly.

**Corrections after the review.** The first draft (a) moved `gu-self-read` to `later` on the nondeterminism ruling: wrong,
the LRM's answer for that shape is deterministic, so it is a simulator-versus-synthesizer split (class (c)) and the row is
`never` again; (b) moved `gu-comb-loop` to `later` on the strength of settling loops, which `run2` already admits and which
are refused downstream by svGolf's `fourstate`: reverted, with a measured state-holding loop that shows why that refusal is
load-bearing; (c) left the `"\xHH"` string escape as an open hole: now refused by the extractor (`lit-string-hex`); (d) filed
two writers of one bit as plainly illegal: true only when one writer is `always_comb`/`always_ff`; (e) printed an empty `run2`
column: measured in section 7. The class table, the per-row evidence and the appendix are updated.

## 1. The rulings the audit applies

1. If slang reports a program illegal, that is a good reason to reject it (Thomas's words). The audit reads "slang reports"
   as the full `slang` driver: parse, elaboration AND analysis (a proposal; section 5, finding 2, shows the extractor,
   `fourstate` and `banlist` do not read the analysis errors). LRM is the IEEE 1800-2023 Language Reference Manual.
2. A refusal because "the tools split" needs a split among the PIPELINE tools: slang / ls-sv (the proof's reading),
   Yosys (the score's reading), Verilator and Xcelium (the simulators). If those agree and only Icarus (or another
   non-pipeline tool) differs, the construct is admissible and the Icarus behaviour is a declared departure
   (hash-bound `oracle_disagreement` row). Icarus is bad at this; it is an optional witness.
3. LRM-legal nondeterminism is modelled in Lean. A golfer who uses such a construct proves that the circuit's final
   output is the same in every legal run, unless the task does not need it. See
   `svgolf/design/nondeterminism/NOTE.md`. The audit distinguishes nondeterminism the LRM leaves open (4.7) from a
   simulator-versus-synthesizer mismatch whose LRM answer is deterministic; the ruling covers only the first.
4. Classes (and the rest of the non-synthesizable subset) are out of scope while the scored frontend is Yosys
   `read_verilog -sv`, which has no classes. A different synthesis frontend (mox-synth) may change that later.
5. Host access (reading files and the like) is disallowed; Mathlib is allowed in submissions (not audited here).

The audit classifies each row into one of five classes.

| class | meaning | consequence |
|---|---|---|
| (a) | ILLEGAL: slang reports an error, or the LRM forbids it | permanent reject; cite the clause |
| (b) | LEGAL; slang, Yosys, Verilator and Xcelium agree; only Icarus differs | admissible; Icarus becomes a declared departure |
| (c) | LEGAL; the pipeline tools genuinely split (this includes a simulator-versus-synthesizer mismatch whose LRM answer is deterministic) | keep refusing; name what would lift it |
| (d) | LEGAL and nondeterministic by the LRM (or a loop with no completed run) | candidate for the run-set model of the NOTE (a loop with no completed run: nothing to lift) |
| (e) | LEGAL; slang and the simulators read it; the scored frontend (Yosys, often Verilator too) cannot | conditional (`later`): refuse while Yosys `read_verilog -sv` is the frontend, as for classes |

## 2. Method

* **Tools.** slang = pyslang 11.0.0 through its `Driver` (the `slang` command-line pipeline, so the analysis pass that
  reports `multiple-always-assigns`, `mixed-var-assigns` and the always-deadlock error is included; `getAllDiagnostics()`
  alone does NOT contain them, see section 5); Yosys 0.53 (`read_verilog -sv`, then `proc; flatten; synth` and the pinned
  scoring flow `svgolf/score/score.py --no-gate`); Verilator 5.042 (`--binary --timing`, 2-state: x and z stimulus digits
  become 0); Icarus 12.0; Xcelium `xrun(64) 24.03-s004` through the fleet gate `refsim` on vip-ng, one run at a time.
* **Stimulus and observation.** Every fixture runs under the cycle testbench of `harness/sv/gen_tb2.py` (inputs at 3k,
  sampled at the negedge), the one the Xcelium pins use. The Yosys column simulates the synthesized netlist in Icarus with
  the same testbench. Fixtures are the `sem2/*` rows the register cites (comments stripped, as the source gate does:
  Verilator reads `// Verilator ...` as a pragma) plus hand-written probes.
* **ls-sv.** The extractor column is a fresh run of `extractors/sv/extract.py --top T` (the `Unsupported` kinds it emits).
  The Lean-layer rows (drivers, guards, context width, loops) are measured with `run2` through the shared Lean slot (section
  7); the `run2` column of the appendix is empty for the cases that batch did not include (the `fold_*`, `pi_*`, `dc_*`,
  `vg_initc` family and the `rbw_*` / `acg_alias_*` rows other than one each, whose refusal the register already records).
* **svGolf.** The "svGolf fourstate" column is a fresh run of `svgolf/score/fourstate.py` (slang elaboration errors plus
  Yosys `check`): whether the existing checker already rejects the design before the language tier is consulted.

## 3. The audit table

Cells are what the tool does on the row's trigger and the fixtures the register cites. "accepts" means no error; values
are given where they decide the class. `=` between tools means identical traces on the fixture's stimulus.

| row | slang | Yosys | Verilator | Xcelium | Icarus | ls-sv | class | verdict |
|---|---|---|---|---|---|---|---|---|
| `pr-init-var` | accepts, no diagnostic even with `-Weverything` | accepts; initializer overwritten by the writer (`y = {1,a}`); fourstate passes | accepts, same values, no error on the cited fixtures; the WHOLE-variable form (`init_whole`) draws `%Warning-MULTIDRIVEN` citing IEEE 9.2.2.2, and a procedural write over an initializer the lint warning `PROCASSINIT` | **REJECTS** `*E,MULAXX` "Multiple drivers to always_comb / always_ff output variable" on 7 of 7 designs (`init_whole` included), the FPGA idiom `logic r = 0; always_ff r <= d;` included; accepts the same shapes with a plain `always @*` writer | accepts, values = Yosys | refuses `ProceduralBlockSymbol:initialized-variable` | (c) | Xcelium rejects, Verilator warns on one form, slang, Yosys and Icarus accept; the LRM is silent on whether an initializer is a writing process. Stays `never`, flagged for Thomas (section 6) |
| `hi-init-driver` | variable + `assign`: **ERROR** `mixed-var-assigns`; instance output into an initialized variable: **ERROR**; non-ANSI input with a separate initialized variable: **ERROR** "cannot assign to input port"; net forms: accepts (`pi_in_net`: warning `port-coercion`) | variable + `assign`: warns "Drivers conflicting with a constant", keeps the initializer (`y = 10`); instance form: ERROR "driving constant bits"; input and net forms keep the constant `01` | variable + `assign`: accepts silently (`y` follows `a`); input net form: ERROR `ASSIGNIN`; other input forms accept (the input wins) | variable + `assign` and instance form: **REJECT** `*E,ICDDIV`; input and net forms accept and RESOLVE both drivers (`x1 xx 0x x1`; net init + assign: `01 0x 0x 01`) | variable + `assign`: REJECT "Unable to assign to unresolved wires"; input and net forms resolve (= Xcelium) | refuses `ContinuousAssignSymbol:initialized-*`, `PortConnection:initialized-*`, `PortSymbol:initialized-input` | (a) for the variable and input-variable forms; (c) for the net forms (legal contention nets, not synthesizable) | stays `never`; principle becomes `P-SAME-PROGRAM`; LRM 6.5 says the initializer IS a procedural assignment and the mixture "shall be an error" |
| `dc-port-init` | `output wire y = 8'd3`: **ERROR** `DisallowedPortDefault` ("only 'output' variable port declarations may have an initializer expression") | net initializer accepted (`y = 3`) | net initializer accepted | net initializer accepts (`y = 3`; with a second `assign`, `000000x1`) | net initializer: REJECT ("not a valid l-value") | refuses `PortSymbol:initializer` | **(a)** | stays `never`, principle `P-SAME-PROGRAM`; LRM 23.2.2.4: "Defaults can be specified only for input ports and only in ANSI style declarations" (checked in the local copy of IEEE 1800-2023) |
| `dc-port-explicit` (split from `dc-port-init`) | explicit port expression `.q(y)` (23.2.1): accepts | **syntax error** | **syntax error** | accepts, values = Icarus | accepts | refuses `PortSymbol:explicit-expression` | **(e)**: legal, the scored frontend cannot read it | `never` to `later` (proposal): conditional on a frontend that reads it, as for classes; the probe is `pi_explicit` (the earlier `dc_port_explicit` mixed ANSI and non-ANSI ports, a slang error for the wrong reason, and is gone) |
| `lit-string` | `\a \v \f` = 7, 11, 12 (IEEE Table 5-1) | = LRM | = LRM | **`\a \v \f` = 0x61 0x76 0x66** (the plain letters) | LRM | refuses `\a \v \f` (`StringLiteral:named-control-escape`) | (c) for `\a \v \f`: Xcelium alone dissents | category unchanged, flagged (section 6) |
| `lit-string-hex` (split from `lit-string`) | `\x41` = 0x41; `\x4` = 0x04 (Table 5-1 `\xdd`) | **`\x41` = 0x31** (reads `x`, `4`, `1`); `\x4` = 0x34 | `\x41` = 0x41; `\x4` is a compile error ("Unknown escape sequence") | **`\x41` = 0x31**, `\x4` = 0x34 | = LRM | **admitted until this audit's fix**; now `StringLiteral:hex-escape` | (c): Yosys against slang, so `P-SAME-PROGRAM` | `never`, closed (section 5, finding 1; probe `hex_guard` confines the difference to `a == 16'hBEEF`) |
| `hi-override-context` | `override-context`: LRM value (`P = 300` for `U + 8'd100` into a 16-bit `P`; `-2^40` at N=1) | 44 (own 8 bits); 0 at N=1 and N=24 | = Yosys | = slang = Icarus (300; `-2^40`) | = slang | refuses `InstanceSymbol:override-context` | (c): Yosys and Verilator against slang and Xcelium | `never`, principle `P-SAME-PROGRAM` |
| | `override-untyped-width`: `W = 9`, `logic signed [31:0]` | `{a, W}` is 32-bit `W` | = Yosys | = Yosys (`0x0f...09`) | **33-bit `W`** (`0x1e...09`) | refuses `InstanceSymbol:override-untyped-width` | **(b)** Icarus alone | split into the new row `hi-override-untyped-width`, `later` |
| `le-portconn-context-width` | context width: the connection expression `p + q` is a `logic[3:0]` binary op with operands converted | self-determined, zero-pad (`p+q` mod 4: `0001` for p=2,q=3; `~p` = `0010` for p=1) | context width (`0101`; `1110`) | context width (= Verilator, `CUVMPW` warning) | self-determined (= Yosys) | `PortConn:context-width` in `Hier2.connProcs`; no `cases2` row | (c), the core `P-SAME-PROGRAM` case | stays `never`, principle `P-SAME-PROGRAM`; admitted subset `PExpr.portSafe` unchanged |
| `gu-self-read` | accepts, no diagnostic | settled (`y = a`; netlist `assign y = a`) on every point | settled | **stale**: = Icarus from cycle 1 on in 9 of 9 rows (cycle 0 reads `xx` on 8 of them: the block's time-zero run is ordered before the first stimulus) | **stale** | `AlwaysComb:self-read` | (c): the event-driven simulators against the synthesizers. The LRM's answer is DETERMINISTIC and stale (9.2.2.2.1(b) keeps the block's own writes out of its sensitivity list), so this is neither Icarus-only nor LRM nondeterminism | stays `never`, principle `P-NO-SILENT-PICK`. The first draft's move to `later` is withdrawn: a run set cannot lift a genuine self-read, because `Computes` quantifies over every run and the stale run gives `y_k = a_(k-1)`. Thomas's question 1 (NOTE section 10) decides |
| `gu-alias-read` | accepts | settled (= Xcelium) | settled | **settled** on 7 of 7 refused rows (pinned for `acg_alias_assign`, `_port` only) | **stale** (one change behind) | `AlwaysComb:alias-read` | **(b)**: Icarus alone. IEEE 4.7/4.8 arguably make Icarus's order legal as well, which is why two routes exist | `never` to `later`, two routes for Thomas (NOTE question 2): declare Icarus, or model the lost-wake-up run; pin the five missing Xcelium traces first |
| `le-driver-procs` | **ERROR** `multiple-always-assigns` (two `always_comb`, two `always_ff`, or one of them plus ANY other process: `two_plain_ac`, `init_comb_proc`) | warns "multiple conflicting drivers", garbage | warns `MULTIDRIVEN` for the `always_comb` pairs (silent on the `always_ff` pair), accepts | **REJECTS** `*E,MULAXX` | accepts; keeps the FIRST block's value (`drv_pw_lit`: `y = 11`) | Lean `driversOk` clause 4 `PortConn:driver`; no extractor refusal | **(a)** | stays `never`, principle `P-SAME-PROGRAM`; LRM 9.2.2.2, 9.2.2.4. Two PLAIN `always @*` writers (`two_plain`) are NOT this row: legal, slang-clean, four tools give four traces (section 4) |
| `two_plain` (new probe) | accepts, no diagnostic | multiple conflicting drivers; the netlist is `y = a` | `MULTIDRIVEN` warning; `y = b` | `y = 0 1 0 0 1 0` (neither `a` nor `b`) | `y = 1 1 0 0 1 1` | extractor: `TimedStatement:ImplicitEventControl` (`always @*` is loud) | (d): legal text, a genuine race | not a register row today (nothing admits it); NOTE section 2 |
| `gu-comb-loop` (oscillating) | accepts, silent | the scoring flow accepts and prices it (`a = en ? ~a : 1'b0`: `AND`+`NAND` ring, 2.333 GE depth 2); fourstate REJECTS ("found logic loop") | a true oscillator aborts "did not converge after 100 tries" | a true oscillator terminates with an arbitrary value (`a = 0 1 0`) | hangs | `run2` answers `timeout` (no completed run) | (d): no completed run, so nothing to lift | stays `never`, principle `P-DETERMINISM` (reverted from the first draft's `later`) |
| settling loops (NOT an ls-sv refusal) | accepts | priced (mux feedback `y = s ? d : y`: one `$_MUX_`, 2.333 GE depth 1; NOR latch 3.333 GE depth 2); a structural loop is optimized away; fourstate REJECTS every loop ("found logic loop") | `UNOPTFLAT` warning, same values | identical traces (mux feedback, structural loop); the NOR latch agrees except at the (1,1) then (0,0) race, where Verilator and Xcelium end in different states | identical traces except that race (hangs there) | `run2` COMPLETES them (`loop_mux`, `loop_fn`, `loop_sr`; `assign a = ~a` settles at `x`) | loop | refused downstream by svGolf's `fourstate` (`sg-fs-conflict`), which stays: the state-holding loop below |
| `loop_lat_if` (state-holding loop, new probe) | accepts | RTL `y = 0`; the scored netlist is `$_AND_(a, y) -> y`, 1.333 GE depth 1, with two stable states at `a = 1` (Yosys `sat`); netlist simulation reads `x x 0 0 0 0` | `UNOPTFLAT`; RTL `y = 0` | RTL `y = 0` | RTL `y = 0` | `run2` answers constant 0 (section 7); no extractor refusal | loop | not a register row; it is the reason `sg-fs-conflict` stays and the reason `gu-comb-loop` cannot move (NOTE section 7) |
| `pr-always-nocontrol` | **ERROR** "'always' procedure does not advance time" (and "always_ff procedure must have one and only one event control") | `always y = a;` accepted as a wire; `always_ff y <= a;` rejected | `always y = a;` accepted | `always y = a;` hangs at run time (timeout); `always_ff` REJECT `*E,SVFFMT` | `always` REJECT; `always_ff` REJECT | refuses `ProceduralBlockSymbol:NoEventControl` | **(a)** | stays `never`, principle `P-SAME-PROGRAM`; LRM 9.2.2.1 (deadlock), 9.2.2.4 |
| `st-invalid` | **ERROR** undeclared identifier; expression not a statement | `y = zzz` accepted (implicit wire, undriven); `a == b;` syntax error | REJECT | REJECT `*E,UNDIDN`, `*E,MISEXX` | REJECT | `InvalidStatement` | **(a)** | LRM 6.10 (implicit nets only for LHS of assigns and port connections) |
| `ex-invalid` | **ERROR** undeclared identifier | accepted (implicit wire) | REJECT | REJECT `*E,UNDIDN` | REJECT | `ContinuousAssignSymbol:InvalidExpression` | **(a)** | LRM 6.10 |
| `ex-op-invalid-compilation` | **ERROR** (any unrelated error) | accepted, `a / b` synthesized | REJECT | REJECT | REJECT | `Division:invalid-compilation` and `InvalidExpression` | **(a)** | a slang error rejects the program whatever the operator |
| `hi-uninstantiated` | **ERROR** unknown module `nomod` | ERROR "not part of the design" | REJECT `MODMISSING` | REJECT `*E,CUVMUR` | REJECT | `UninstantiatedDefSymbol` | **(a)** for no definition; an UNTAKEN generate branch with an undefined module: all five tools accept | stays `never`; the untaken-branch case is recorded as measured-agreeing |
| `le-driver-mixed` | **ERROR** `mixed-var-assigns` | warns, garbage (`x0`) | warns `MULTIDRIVEN`, accepts | REJECT `*E,ICDPAV` | REJECT "Bit 0 is already driven" | Lean `driversOk` clause 2 | **(a)** | LRM 6.5 |
| `le-driver-input` | **ERROR** "cannot assign to input port" (assign, procedural, instance output) | accepts, "Drivers conflicting with a constant" | REJECT `ASSIGNIN` | accepts `assign` and instance forms (LRM 23.3.3.1 allows coercing a net input to inout, with a warning); REJECT procedural | assign accepted; others REJECT | Lean `driversOk` clause 3 | **(a)** | LRM 23.3.3.2 for variable inputs; slang rejects the net form too |

The svGolf checker already rejects most section-A shapes and driver-rule shapes before the language tier runs:
`fourstate` reports the slang elaboration errors and Yosys `check` ("multiple conflicting drivers", "Drivers conflicting
with a constant", "cannot read the design", "found logic loop"). The shapes `fourstate` passes and only the loader
refuses are: the initialized-variable writers (`vg_initc`, `vg_initf`, `vg_initq`, `vh_initcomb`, `pr_init_fpga`,
`init_whole`), self-read and alias-read `always_comb`, `always y = a;`, `ctx_pq`, the `lit_str_*` escapes, and the override
rows. The shape that the extractor and `fourstate` both admit although slang reports it is `initial y = 0; always_comb y = a;`
(`init_comb_proc`): `run2` refuses it, but only because the loader has no `Initial` process kind (section 5, finding 2).

## 4. Per-row evidence and the proposed verdict

**`gu-alias-read` (b), proposed `never` to `later`.** Seven refusal rows (`acg_alias_assign`, `_port`, `_chain`, `_not`,
`_bits`, `_hier`, `_thru`) re-measured today: Icarus is one change behind on every row except `_not`; Xcelium, Verilator
(2-state) and the Yosys netlist give the settled value (`y = a`) on all of them (Xcelium equals the Yosys netlist on every row,
and equals Verilator wherever its output has no x digit), and the model's settle semantics agrees. The admitted twins
(`acg_alias_wr`, `acg_alias_copy`) agree in all four. So the pipeline tools agree and only Icarus differs. The earlier decision
to refuse (Thomas, 2026-10-29) predates the ruling that Icarus-only splits are declared departures. Whether Icarus's order is
ALSO legal is an inference, not a quoted sentence: IEEE 4.7 says a procedural statement need not execute as one event ("the
simulator may suspend execution ... the order of interleaved execution is nondeterministic"), and a change that lands while the
block is running is lost to an event control it is not waiting on; I call that order "arguably legal". That is why there are two
routes, and the register states both instead of committing: (A) declare Icarus (Thomas's Icarus-only ruling applies directly;
the model stays settled-only, so Icarus's order is then not a run that binds the golfer), or (B) model the lost-wake-up run
(NOTE option O2). Either needs the Xcelium traces pinned: `harness/sv/xcelium_golden.json` holds `acg_alias_assign` and
`acg_alias_port` (left from when they were simulated), not `_chain`, `_not`, `_bits`, `_hier`, `_thru`, and
`xcelium_batch.py` skips rows that carry a `refusal`, so the pins arrive with the lift. Prerequisite for route A: re-add the two declarations retired
in round 6 (`iverilog-comb-assign-alias-sensitivity`, `iverilog-comb-port-loop-sensitivity`) on the now-simulated rows, disable
`AlwaysComb:alias-read` for them, and keep the guard's soundness lemma (`CombAlias2Sound`) for the admitted fragment.

**`gu-self-read` (c), stays `never`; the first draft's proposal to move it to `later` is withdrawn.** `rbw_comb`, `rbw_held`,
`rbw_bits`, `rbw_cond`, `rbw_case_item`, `rbw_dyn`, `rbw_part`, `rbw_nested`, `rbw_child` re-measured (and `rbw_comb`
re-run on its own with `a = 00,01,10,11`: Icarus `y = 00,00,01,10`; Xcelium `xx,00,01,10`; Verilator and the Yosys netlist
`00,01,10,11`). IEEE 9.2.2.2.1(b) excludes "any expression that is also written within the block" from the implicit
sensitivity list, and 9.2.2.2 triggers the block once at time zero. So `y = t; t = a;` does not re-run on its own write of `t`,
and the LRM's simulation answer is DETERMINISTIC: `y` is one change behind. Icarus 12 and Xcelium 24.03 follow it (Xcelium reads
`xx` at cycle 0 on 8 of the 9 rows: the block's time-zero run precedes the testbench's first assignment); Verilator and the Yosys
netlist compute the settled `y = a`. That is a simulator-versus-synthesizer split, not an Icarus-only split and not LRM
nondeterminism. Thomas's nondeterminism ruling therefore does not move the row, and a run-set model could not lift it: the task's
`Computes` quantifies over EVERY run, the stale run gives `y_k = a_(k-1)` where the task demands `fn(a_k)`, so a genuine
self-read is unprovable under any run set that contains the LRM's run. What a lift would admit is the guard's recorded
over-refusal residue (dead reads, infeasible path combinations), which a sharper guard admits for far less. The decision is
Thomas's (NOTE question 1): follow the LRM's simulation (then only the residue), or follow the synthesizers (a declared
departure from explicit LRM text for Icarus AND Xcelium, which the 2026-10-29 policy "where the model would follow one oracle
against explicit LRM text, refuse" forbids unless amended).

**`gu-comb-loop`, stays `never` (oscillators only); settling loops are not an ls-sv refusal.** Measured with six loops.
`assign a = ~a` does not oscillate in a 4-state simulator (the undriven start is `z`, `~z = x`, a fixpoint: Icarus `z`, Xcelium and
the netlist `x`), only in Verilator; `run2` completes it with `x`. A true oscillator (`a = en ? ~a : 1'b0`, `en` 0 then 1) hangs
Icarus and the netlist simulation, aborts Verilator ("did not converge") and terminates Xcelium at an arbitrary value; `run2`
answers `timeout`. Such a design has no completed run, so it can never satisfy `Terminates2` and there is nothing to lift. A
loop that settles (`y = s ? d : y`, a structural loop computing `a = b = d`) gives identical traces in all five tools, is accepted
AND PRICED by the pinned scoring flow (2.333 GE, depth 1 for the mux feedback), is completed by `run2`, and is REJECTED
today by svGolf's `fourstate` (Yosys `check`: "found logic loop"). The cross-coupled NOR latch agrees except at `(s,r) = (1,1)`
then `(0,0)`, a true race (Verilator and Xcelium end in different states, Icarus hangs). The first draft concluded that
settling loops could move to `later`; the new probe shows why `fourstate`'s refusal is load-bearing. `loop_lat_if`:

```systemverilog
always_comb begin if (y) t = a; else t = 1'b0; end
always_comb y = t;
```

Icarus, Verilator and Xcelium simulate the RTL as `y = 0` for every stimulus (a 4-state `if` with an `x` condition takes the else
branch, so the loop is resolved at the start); the Yosys netlist simulation reads `x x 0 0 0 0` from an unknown start; the scored
netlist is `y = y & a` (one `$_AND_`, 1.333 GE, depth 1) and Yosys `sat` finds both `y = 1` and `y = 0` consistent at `a = 1`: the
circuit remembers. `run2` answers constant 0 (section 7), so `Computes` with `fn = const 0` and `Terminates2` both hold in the
model, `postsynth` cannot see the memory (Verilator gets `--x-initial 0` and `randReset(0)`), and no stage but `fourstate`
refuses it; the extractor emits no `Unsupported` for it. See NOTE section 7.

**`hi-override-context`, proposed split.** `override-context` (`fold_ovr`, `fold_ovrw` at N=1 and N=24): slang evaluates the
override at the parameter's type (IEEE 10.8 lists "a parameter value override in the instantiation of a module" and "a
port connection" as assignment-like contexts) and so do Icarus and Xcelium; Yosys and Verilator evaluate at the operands'
own width. Class (c), the core `P-SAME-PROGRAM` case (proof reads slang's value, the score reads Yosys's): stays `never`.
`override-untyped-width` (`fold_uwovr`, `fold_sho_*`): an untyped child parameter takes the override's type (IEEE 6.20.2),
32 bits: slang, Yosys, Verilator and Xcelium agree; Icarus keeps the lossless 33-bit width. Class (b), proposed
`later`: the new row `hi-override-untyped-width`. Prerequisite: the extractor's `_sym_icarus_widens` refusal is lifted for
this tag (the model followed Yosys here before round 6), a declared Icarus departure row is added, and the Xcelium traces of
`fold_uwovr`, `fold_uwovr_n0`, `fold_sho_n1`, `fold_sho_n40` are pinned (none is in `xcelium_golden.json`; the pins come
with the lift, since `xcelium_batch.py` pins simulated rows only).

**`le-portconn-context-width` (c).** `ctx_pq` (`p + q` and `~p` into a 4-bit port, exhaustive over 2-bit `p`, `q`): slang binds the
connection at 4 bits (both operands are conversions to `logic[3:0]`), Verilator and Xcelium agree (`0101`, `1110`); Yosys and
Icarus zero-pad the self-determined value (`0001`, `0010`). Yosys is the dissenter, so the rule-2 admission does not apply and the
score would read a different program than the proof: stays `never`. The register's older second trigger shape, an INT-class
constant into a port wider than 32 bits, is NOT part of this row: `ctx_const40` (`-1` into 40 bits) is sign-extended by all five
tools, so there is no tools split. It is refused anyway, by the extractor as `PortConnection:int-width` (row
`hi-port-int-width`, `later`) and, measured by `run2`, by this row's Lean tag `PortConn:context-width` too: an over-refusal of
the Lean guard relative to this row's reason.

**`le-driver-procs`, `le-driver-mixed`, `le-driver-input` (a).** slang's analysis pass reports each as an ERROR
(`-Wmultiple-always-assigns` for `always_comb` and `always_ff` pairs and for one of them plus ANY other process, including an
`initial` block or a plain `always`; `-Wmixed-var-assigns`; "cannot assign to input port"), the LRM says so (6.5; 9.2.2.2 and
9.2.2.4: "shall not be assigned by any other process"; 23.3.3.2), and Xcelium rejects the first two. Icarus runs `drv_pw_*` and
keeps the first block's value (`drv_pw_lit`: `y = 11`; Verilator's second block gives `10`, Yosys `00`), so the register's old
reason ("Icarus gives the first block's value, Sem2 the last") was about a program that is simply illegal. Two PLAIN `always @*`
writers of one bit (`two_plain`) are different: legal text, slang-clean, a real race with four distinct traces in four tools
(section 3), which is what Thomas's nondeterminism ruling is about; nothing admits it today because the extractor refuses
`always @*` (`TimedStatement:ImplicitEventControl`) and `fourstate` rejects the netlist (Yosys `check`: multiple conflicting
drivers). The recorded over-refusal of a plain `always @(posedge clk or negedge rn)` does not reproduce for ONE process
(`drv_pw_plain_always` runs); the Lean rule `Process2.exclusive` still counts `alwaysFFR` as exclusive, so the over-refusal needs a
second writer of the same bit, a program `fourstate` rejects anyway. The extractor and `fourstate` admit `initial y = 0; always_comb
y = a;` (a slang error); `run2` refuses it only for lack of an `Initial` process kind (finding 2 below).

**`pr-always-nocontrol` (a).** `always y = a;` is legal text that deadlocks (IEEE 9.2.2.1: "a simulation deadlock
condition"); slang reports it as an error, Icarus refuses it, Xcelium hangs; Yosys and Verilator silently turn it into a
wire. `always_ff y <= a;` violates 9.2.2.4 (slang, Icarus, Xcelium and Yosys reject). The principle was
`P-DETERMINISM`; it is `P-SAME-PROGRAM` (slang rejects, and Yosys reads a different program).

**`dc-port-init` (a) and `dc-port-explicit` (e), split.** A net-port initializer is a slang ERROR (`DisallowedPortDefault`: "only
'output' variable port declarations may have an initializer expression"); the LRM sentence is 23.2.2.4, "Defaults can be
specified only for input ports and only in ANSI style declarations" (checked in the local copy of IEEE 1800-2023; 6.8 covers the
variable initialization that is allowed). Xcelium, Verilator and Yosys accept the net form as a continuous driver, Icarus rejects
it. The explicit port expression `.q(y)` (23.2.1) is legal and slang, Icarus and Xcelium read it with equal values (`pi_explicit`),
but Yosys and Verilator cannot parse it. Because the scored frontend cannot read it, the second half is the same kind of
refusal as a class declaration, and the proposal is the same: a conditional category (`later`, prerequisite: a frontend that
reads it). The first draft's probe `dc_port_explicit` mixed ANSI and non-ANSI ports (a slang error for the wrong reason) and
is removed.

**`hi-init-driver`.** The variable forms are illegal under the sentence "a declared variable initialization ... is
considered a procedural assignment" (IEEE 6.5) and the rule "it shall be an error to have ... a mixture of procedural and
continuous assignments"; slang, Xcelium and Icarus reject, Yosys and Verilator accept SILENTLY with different values
(Yosys keeps the initializer, Verilator follows the driver): this is exactly what the source of `P-SAME-PROGRAM` guards
against. The net forms (`vg_initn`, `pi_in_net`) are legal contention nets: Xcelium and Icarus resolve the two drivers,
Yosys and Verilator keep one constant; a resolved net with two drivers is not hardware the scored flow can synthesize.

**`pr-init-var` (c).** An initializer plus ONE `always_comb`/`always_ff` writer: IEEE 6.5 counts the initializer as a procedural
assignment only for the continuous-versus-procedural mixture rule, and 9.2.2.2 forbids assignment by "any other process"; the
LRM does not say whether an initializer is such a process (`docs/sv-oracle-disagreements.md` item 5). Xcelium rejects every
variant (`*E,MULAXX`), the FPGA idiom `logic r = 0; always_ff r <= d;` included; Verilator accepts the cited fixtures but lints
the whole-variable form (`init_whole`) with `%Warning-MULTIDRIVEN`, citing 9.2.2.2, and any procedural write over an initializer
with `PROCASSINIT`; slang, Yosys and Icarus accept with identical values. Not an Icarus-only split; stays `never` for Thomas.

**`lit-string` and `lit-string-hex`.** IEEE 5.9.1 Table 5-1 lists `\a \v \f` and `\xdd`. For `\a \v \f`: slang, Icarus 12, Verilator
5.042 and Yosys 0.53 follow the table; Xcelium 24.03 reads each as its plain letter. The pipeline tools that matter for the score
(slang, Yosys) agree; the reference simulator dissents. That is the policy of 2026-10-29 ("where Xcelium departs from explicit
LRM text and the others follow it, refuse"), so the refusal stands, but it is an Xcelium-only dissent and not a split between
proof and score. For `\xdd` the dissenter is Yosys: slang, Icarus and Verilator give the byte, Yosys and Xcelium read the letter
`x` and the digits (`"\x41"` is 0x31 in the scored netlist, `y = 8'h31`, and 0x41 in the model; `"\x4"` is 0x34 against 0x04).
`_disputed_string_escape` refused only `\a`, `\v`, `\f`, so the extractor, the source gate and `fourstate` all admitted it, and only
the post-synthesis check could catch it, on vectors that reach the constant; the probe `hex_guard`
(`assign y = (a == 16'hBEEF) ? "\x41" : 8'h41;`) confines the difference to one input value, the attack the `fourstate`
docstring describes. Fixed in this branch: the extractor refuses a hex escape as `StringLiteral:hex-escape` (row
`lit-string-hex`, `P-SAME-PROGRAM`), with unit tests that fail without the fix (`extractors/sv/test_selected_types.py`). The
octal escape `\101` and an escaped backslash before `x` are plain in every tool and stay admitted. Non-ASCII literals
(`:encoding`, `:width`) are refused by the source gate before the extractor in svGolf.

## 5. Findings outside the audited rows

1. **The `\xHH` hole is closed** (above). It was a one-line extension of `_disputed_string_escape` plus a register row, done in
   this branch after the review pointed out that a sampled post-synthesis check is not the safety net the first draft said it was.
2. **`getAllDiagnostics()` does not contain slang's analysis-pass errors, and one slang error is refused only by accident.**
   `multiple-always-assigns`, `mixed-var-assigns`, "cannot assign to input port" and "'always' procedure does not advance
   time" appear only when the analysis manager runs (the `slang` driver does; `Compilation.getAllDiagnostics()`, which
   `fourstate.py`, `banlist.py` and the extractor use, returns nothing for `assign a = b` on an input, two `always_comb`
   writers, `always y = a;` and mixed variable assigns). So ruling 1 holds at svGolf today only because Yosys `check` and the
   Lean guards catch the same shapes, and the measured exception is `initial y = 0; always_comb y = a;` (`init_comb_proc`):
   slang ERROR (`multiple-always-assigns`) and Xcelium `*E,MULAXX`, while the extractor emits no `Unsupported` (it emits an
   `Initial` node), `fourstate` passes it (Yosys accepts the netlist), and `run2` refuses it only with `envelope: module:
   Initial: unknown process kind "Initial"` (section 7), i.e. because `initial` is out of tier today. It becomes a real gap
   the day `initial` is admitted (R1 inch 4a) unless `driversOk` counts `initial` as another process by then. A front-door rule that runs the pyslang
   `Driver` (or `AnalysisManager`) and rejects on any error would subsume section A, the three driver rows and this gap in
   one place. Recorded in the register `holes`; not implemented here (a checker change, outside package C).
3. **Yosys silently accepts undeclared identifiers** (`assign y = zzz;` becomes an undriven implicit wire). Only the slang
   error stands between such a design and a score.
4. **Section A is not one rule in the extractor.** The extractor continues past slang errors and marks the affected nodes
   loud (`InvalidStatement`, `InvalidExpression`, `*:invalid-compilation`, `UninstantiatedDef`); svGolf's `fourstate`
   already rejects every slang elaboration error and Yosys `check` finding for every task. So the collapse of the six
   rows into one front-door rule is a documentation change today, with the analysis-pass blind spot of finding 2.
5. **Other `refused-now` rows have the same Icarus-only shape and should be re-audited with an Xcelium column**:
   `lit-unsized-xz` (Icarus zero-pads, Xcelium and Yosys extend), `le-genvar-unsigned-ext`, `le-assign-context`,
   `le-untyped-width`, `le-untyped-overflow`, `sel-array-index-range`, `sel-dyn-wide-base`, `le-const-select`. Not
   changed here.
6. **What `read_verilog -sv` really fails on** (`harness/sv/tools_split_audit/yosys_frontend.py`, Yosys 0.53), for the wording
   of `P-SYNTHESIZABLE`:

   | construct | Yosys `read_verilog -sv` | slang |
   |---|---|---|
   | class declaration | **rejects**: syntax error, unexpected ';', expecting '(' or '[' | clean |
   | queue variable | **rejects**: Non-constant range in declaration of \q | clean |
   | dynamic array variable | **rejects**: syntax error, unexpected ']' | clean |
   | associative array variable | **rejects**: syntax error, unexpected ']', expecting SIGNED or UN | clean |
   | string variable | **rejects**: syntax error, unexpected ';', expecting '(' or '[' | clean |
   | string parameter (typed) | **rejects**: syntax error, unexpected ID, expecting ',' or '=' or ')' | clean |
   | real variable | **rejects**: syntax error, unexpected REAL | clean |
   | real constant in a localparam | reads | clean |
   | fork/join | **rejects**: syntax error, unexpected ID | clean |
   | program block | **rejects**: syntax error, unexpected ID | clean |
   | explicit port expression .q(y) | **rejects**: syntax error, unexpected ID, expecting '.' | clean |

   So the principle names class declarations, queues, dynamic and associative arrays, `string` variables and parameters, `real`
   variables, fork/join and program blocks, not "reals" in general: a constant `real` in a parameter expression is read.
7. **A loop the model calls constant that the netlist makes a latch** (`loop_lat_if`, above): not a register row but the reason
   `sg-fs-conflict` stays and `gu-comb-loop` cannot move.
8. **Xcelium pins.** The 2026-10-29 rule says Xcelium facts are pinned, hash-bound data. The Xcelium evidence behind this audit
   is measured but mostly NOT pinned: `harness/sv/xcelium_golden.json` holds `acg_alias_assign` and `acg_alias_port` (their traces
   equal a fresh run) and no row for `acg_alias_chain`, `_not`, `_bits`, `_hier`, `_thru`, for `fold_uwovr`, `fold_uwovr_n0`,
   `fold_sho_n1`, `fold_sho_n40`, or for the nine `rbw_*` refusal rows (refusal rows are not simulated by the differential
   harness). `xcelium_batch.py` pins only SIMULATED rows (a row with a `refusal` is skipped), so these pins cannot be made while the rows
are refused: they arrive with the lift. The two `later` rows that depend on Xcelium agreeing with the model say so in their
prerequisite.

## 6. Rows left unchanged because the classification needs Thomas

* **`pr-init-var`**: class (c) with Xcelium the only simulator that rejects (Verilator lints one form; slang, Yosys, Icarus run
  it with identical values). Whether one reference-simulator lint blocks a construct that the other tools read alike is a
  policy question, not a measurement. If the answer is no, the row, including the FPGA idiom
  `logic q = 0; always_ff ... q <= ...` the register records as an over-refusal, becomes `later`.
* **`lit-string`** (`\a \v \f`): class (c) with Xcelium (24.03 predates the 2009 escapes) the only dissenter.
* **`gu-self-read`**: which reading the proof follows (NOTE question 1). The row stays `never` until he answers.
* **`gu-alias-read`**: declare Icarus or model the lost-wake-up run (NOTE question 2). Stays `later` either way.
* **`dc-port-explicit`**: moved to `later` by analogy with his classes ruling; he has not ruled on this construct. Proposal.

## 7. ls-sv run2 column

Measured on 2026-10-31 with `harness/sv/tools_split_audit/lean_batch.sh` (one acquisition of the shared Lean slot for 39 cases;
`lean_parse.py` turns the output into the appendix column; the raw output is reproduced by the command in the README). A cell
says `runs` (completed, CYCLE lines printed) or the first loud refusal. What it settles:

| question | answer |
|---|---|
| Does the Lean `driversOk` refuse the section-A probes? | Yes, all four: `a_drv_mix_plain`, `a_drv_input_assign`, `a_drv_input_proc`, `a_drv_input_inst` give `PortConn:driver` (clause 2 for the mixture, clause 3 for the input). So `le-driver-mixed` and `le-driver-input` are verified by run and lose `unverified`. |
| And the pair rows of `le-driver-procs`? | `drv_pw_lit`, `drv_pw_gv`, `drv_pw_par_k0`, `drv_pw_ff` give `PortConn:driver` (clause 4), `drv_mix_k0` clause 2: verified, `unverified` flipped. |
| Is the single plain async-reset `always` over-refused? | No: `drv_pw_plain_always` runs (`q = 0 1 0`). The recorded over-refusal needs a second writer of the same bit. |
| `initial y = 0; always_comb y = a;` (`init_comb_proc`)? | Refused, but only with `envelope: module: Initial: unknown process kind "Initial"`: the loader has no `Initial` process kind. The extractor emits an `Initial` node and `fourstate` passes it, so "a program slang rejects is rejected" holds for this shape by accident, and stops holding when `initial` is admitted unless `driversOk` counts `initial` as another process. |
| Plain `always @*` pairs (`two_plain`, `two_plain_ac`)? | Refused: `TimedStatement:ImplicitEventControl` (`always @*` is loud before any driver rule). |
| `ctx_pq`? | Refused: `PortConn:context-width` (the register was right; the old pages said "not a row"). `ctx_const40` (no tools split) is refused by the same Lean tag as well. |
| Settling loops? | They RUN: `loop_mux` (`y = 1 1 0 0`), `loop_fn` (`a = b = d` at every cycle), `loop_sr` (completes, `q qn = 10 10 01 01 00 10` across the `(1,1)` then `(0,0)` race), and `assign a = ~a` (`loop_osc`, `y = x`). So they are not an ls-sv refusal. |
| The oscillator? | `loop_osc2`: `run2: timeout (fuel exhausted / comb loop)`, no completed run. |
| **The state-holding loop** (`loop_lat_if`, `loop_lat_if_b`)? | **Both RUN and answer constant `y = 0`**, for the stimulus that starts with `a = 1` and the one that starts with `a = 0`. `Terminates2` and `Computes` with `fn = const 0` therefore hold in the model of a circuit that remembers (NOTE section 7). |
| Self-read, alias-read? | `rbw_comb`: `AlwaysComb:self-read`; `acg_alias_assign`: `AlwaysComb:alias-read`. |
| `\x41` (`lit_str_x41`, `hex_guard`)? | `StringLiteral:hex-escape`, from the extractor fix of this audit (before it, both ran and the model computed 8'h41 against the netlist's 8'h31). |
| Section A rows? | `a_st_invalid`: `InvalidStatement`; `a_ex_invalid`: `ContinuousAssignSymbol:InvalidExpression`; `a_hi_uninst`: `UninstantiatedDef`. `a_hi_uninst_gen` (undefined module in an UNTAKEN generate branch) RUNS at the default point (`y = 0 1`), although the extractor flags it: all five tools accept that program. |

Not run (no Lean needed or the answer is in the extractor column): the `fold_*` override rows, the `rbw_*` and `acg_alias_*` rows
other than the two above (the register already records their refusals), `pi_*`, `dc_*`, `vg_initc` and friends.

## Appendix: the per-case matrix

Generated by `report.py` (the harness). "trace A..D" cells name distinct output traces of the same fixture; identical
letters across tools mean identical traces. Sequences are per stimulus cycle.

### Section A: the frontend rejects

| case | slang | Icarus | Verilator | Yosys | Xcelium | ls-sv extractor | fourstate | run2 |
|---|---|---|---|---|---|---|---|---|
| `a_st_invalid` | ERROR: use of undeclared identifier 'zzz' | reject | reject | A | reject | `InvalidStatement` | REJECT | REFUSES:  run2: unsupported: unsupported statement 'InvalidStatement' [InvalidStatement: begin y = zzz; |
| `a_st_invalid2` | ERROR: expression is not allowed as a statement | reject | reject | reject | reject | `InvalidStatement` | REJECT |  |
| `a_ex_invalid` | ERROR: use of undeclared identifier 'zzz' | reject | reject | A | reject | `ContinuousAssignSymbol:InvalidExpression` | REJECT | REFUSES:  run2: unsupported: unsupported process 'ContinuousAssignSymbol:InvalidExpression' [Continuous |
| `a_ex_op_invalid` | ERROR: use of undeclared identifier 'zzz2' | reject | reject | A | reject | `ContinuousAssignSymbol:InvalidExpression`, `Division:invalid-compilation` | REJECT |  |
| `a_hi_uninst` | ERROR: unknown module 'nomod' | reject | reject | reject | reject | `UninstantiatedDefSymbol:UninstantiatedDef` | REJECT | REFUSES:  run2: unsupported: unsupported process 'UninstantiatedDefSymbol:UninstantiatedDef' [Uninstant |
| `a_hi_uninst_gen` | ok | A | A | A | A | `UninstantiatedDefSymbol:UninstantiatedDef` | pass | runs |
| `a_drv_mix_plain` | ERROR: cannot mix continuous and procedural assignments to variable | reject | A | B | reject | - | REJECT | REFUSES:  PortConn:driver: signal 'y' of module 'a_drv_mix_plain' is driven both continuously (an `assi |
| `a_drv_input_assign` | ERROR: cannot assign to input port 'a' | A | reject | B | A | - | REJECT | REFUSES:  PortConn:driver: input port 'a' of module 'a_drv_input_assign' is driven inside the module (i |
| `a_drv_input_proc` | ERROR: cannot assign to input port 'a' | reject | reject | A | reject | - | REJECT | REFUSES:  PortConn:driver: input port 'a' of module 'a_drv_input_proc' is driven inside the module (its |
| `a_drv_input_inst` | ERROR: cannot assign to input port 'a' | reject | reject | A | B | - | REJECT | REFUSES:  PortConn:driver: input port 'a' of module 'a_drv_input_inst' is driven inside the module (its |

Traces (one value per stimulus cycle; a letter names one distinct trace of the case):

* `a_st_invalid`: **A** = `y=x,x`
* `a_ex_invalid`: **A** = `y=x,x`
* `a_ex_op_invalid`: **A** = `y=0100`
* `a_hi_uninst_gen`: **A** = `y=0,1`
* `a_drv_mix_plain`: **A** = `y=01,10`; **B** = `y=00,11`
* `a_drv_input_assign`: **A** = `y=0,x`; **B** = `y=0,0`
* `a_drv_input_proc`: **A** = `y=0,0`
* `a_drv_input_inst`: **A** = `y=0,0`; **B** = `y=0,x`

### le-driver-procs / le-driver-mixed

| case | slang | Icarus | Verilator | Yosys | Xcelium | ls-sv extractor | fourstate | run2 |
|---|---|---|---|---|---|---|---|---|
| `drv_pw_lit` | ERROR: variable 'y[0]' driven by always_comb procedure cannot be wr | A | B | C | reject | - | REJECT | REFUSES:  PortConn:driver: signal 'y' of module 'drv_pw_lit' is written on one bit by an `always_comb`/ |
| `drv_pw_gv` | ERROR: variable 'y[0]' driven by always_comb procedure cannot be wr | A | B | C | reject | - | REJECT | REFUSES:  PortConn:driver: signal 'y' of module 'drv_pw_gv' is written on one bit by an `always_comb`/` |
| `drv_pw_par_k0` | ERROR: variable 'y[0]' driven by always_comb procedure cannot be wr | A | B | A | reject | - | REJECT | REFUSES:  PortConn:driver: signal 'y' of module 'drv_pw_par' is written on one bit by an `always_comb`/ |
| `drv_pw_ff` | ERROR: variable 'y[0]' driven by always_ff procedure cannot be writ | A | B | ok(net.v:14: error: 'y_reg[0]' has already ) | reject | - | REJECT | REFUSES:  PortConn:driver: signal 'y' of module 'drv_pw_ff' is written on one bit by an `always_comb`/` |
| `drv_mix_k0` | ERROR: cannot mix continuous and procedural assignments to variable | reject | A | B | reject | - | REJECT | REFUSES:  PortConn:driver: signal 'y' of module 'drv_mix' is driven both continuously (an `assign` or a |
| `drv_pw_plain_always` | ok | A | A | A | A | - | pass | runs |
| `two_plain` | ok | A | B | C | D | `TimedStatement:ImplicitEventControl` | REJECT | REFUSES:  run2: unsupported: unsupported process 'TimedStatement:ImplicitEventControl' [TimedStatement: |
| `two_plain_ac` | ERROR: variable 'y' driven by always_comb procedure cannot be writt | A | B | C | reject | `TimedStatement:ImplicitEventControl` | REJECT | REFUSES:  run2: unsupported: unsupported process 'TimedStatement:ImplicitEventControl' [TimedStatement: |
| `init_comb_proc` | ERROR: variable 'y' driven by always_comb procedure cannot be writt | A | A | A | reject | - | pass | REFUSES:  envelope: module: Initial: unknown process kind "Initial" |

Traces (one value per stimulus cycle; a letter names one distinct trace of the case):

* `drv_pw_lit`: **A** = `y=11`; **B** = `y=10`; **C** = `y=00`
* `drv_pw_gv`: **A** = `y=x1`; **B** = `y=00`; **C** = `y=x0`
* `drv_pw_par_k0`: **A** = `y=x0`; **B** = `y=01`
* `drv_pw_ff`: **A** = `y=x1`; **B** = `y=00`
* `drv_mix_k0`: **A** = `y=01`; **B** = `y=x0`
* `drv_pw_plain_always`: **A** = `q=0,1,0`
* `two_plain`: **A** = `y=1,1,0,0,1,1`; **B** = `y=1,1,0,0,0,1`; **C** = `y=0,1,1,0,1,0`; **D** = `y=0,1,0,0,1,0`
* `two_plain_ac`: **A** = `y=0,1,0,0`; **B** = `y=1,1,0,0`; **C** = `y=0,1,1,0`
* `init_comb_proc`: **A** = `y=1,0,1`

### pr-init-var

| case | slang | Icarus | Verilator | Yosys | Xcelium | ls-sv extractor | fourstate | run2 |
|---|---|---|---|---|---|---|---|---|
| `vg_initc` | ok | A | B | A | reject | `ProceduralBlockSymbol:initialized-variable` | pass |  |
| `vg_initf` | ok | A | B | A | reject | `ProceduralBlockSymbol:initialized-variable` | pass |  |
| `vg_initq` | ok | A | B | A | reject | `ProceduralBlockSymbol:initialized-variable` | pass |  |
| `vh_initcomb` | ok | A | B | A | reject | `ProceduralBlockSymbol:initialized-variable` | pass |  |
| `pr_init_fpga` | ok | A | A | A | reject | `ProceduralBlockSymbol:initialized-variable` | pass | REFUSES:  run2: unsupported: unsupported process 'ProceduralBlockSymbol:initialized-variable' [Procedur |
| `pr_init_comb_plain` | ok | A | A | A | A | `TimedStatement:ImplicitEventControl` | pass | REFUSES:  run2: unsupported: unsupported process 'TimedStatement:ImplicitEventControl' [TimedStatement: |
| `init_whole` | ok | A | A | A | reject | `ProceduralBlockSymbol:initialized-variable` | pass | REFUSES:  run2: unsupported: unsupported process 'ProceduralBlockSymbol:initialized-variable' [Procedur |

Traces (one value per stimulus cycle; a letter names one distinct trace of the case):

* `vg_initc`: **A** = `y=11,10,1x,1z`; **B** = `y=11,10,10,10`
* `vg_initf`: **A** = `y=11,10,1x`; **B** = `y=11,10,10`
* `vg_initq`: **A** = `y=11,10,1x,11`; **B** = `y=11,10,10,11`
* `vh_initcomb`: **A** = `y=11,10,1x`; **B** = `y=11,10,10`
* `pr_init_fpga`: **A** = `q=1,0,1,1`
* `pr_init_comb_plain`: **A** = `y=01,10,11,00`
* `init_whole`: **A** = `y=01,00,01,00`

### hi-init-driver

| case | slang | Icarus | Verilator | Yosys | Xcelium | ls-sv extractor | fourstate | run2 |
|---|---|---|---|---|---|---|---|---|
| `vg_init` | ERROR: cannot mix continuous and procedural assignments to variable | reject | A | B | reject | `ContinuousAssignSymbol:initialized-variable` | REJECT | REFUSES:  run2: unsupported: unsupported process 'ContinuousAssignSymbol:initialized-variable' [Continu |
| `vh_init` | ERROR: cannot mix continuous and procedural assignments to variable | reject | A | reject | reject | `PortConnection:initialized-variable` | REJECT | REFUSES:  run2: unsupported: unsupported process 'PortConnection:initialized-variable' [PortConnection: |
| `vg_initn` | ok | A | B | B | A | `ContinuousAssignSymbol:initialized-net` | REJECT |  |
| `pi_in_init` | ERROR: cannot assign to input port 'a' | A | B | C | A | `PortSymbol:initialized-input` | REJECT | REFUSES:  run2: unsupported: unsupported process 'PortConn:port' [PortConn:port: connection 'a' names n |
| `pi_in_init2` | ERROR: cannot assign to input port 'a' | A | B | C | D | `PortSymbol:initialized-input` | REJECT |  |
| `pi_in_top` | ERROR: cannot assign to input port 'a' | A | B | C | D | `PortSymbol:initialized-input` | REJECT |  |
| `pi_in_net` | ok (warn) | A | reject | B | A | `PortSymbol:initialized-input` | REJECT |  |

Traces (one value per stimulus cycle; a letter names one distinct trace of the case):

* `vg_init`: **A** = `y=11,10,10`; **B** = `y=10,10,10`
* `vh_init`: **A** = `y=10,11,11`
* `vg_initn`: **A** = `y=01,0x,0x,01`; **B** = `y=01,01,01,01`
* `pi_in_init`: **A** = `y=x1,xx,0x,x1`; **B** = `y=11,10,00,01`; **C** = `y=01,01,01,01`
* `pi_in_init2`: **A** = `y=11,10,00,x1`; **B** = `y=11,10,00,01`; **C** = `y=01,01,01,01`; **D** = `y=x1,xx,0x,x1`
* `pi_in_top`: **A** = `y=11,10,00,x1`; **B** = `y=11,10,00,01`; **C** = `y=01,01,01,01`; **D** = `y=x1,xx,0x,x1`
* `pi_in_net`: **A** = `y=x1,xx,0x,x1`; **B** = `y=01,01,01,01`

### dc-port-init / dc-port-explicit

| case | slang | Icarus | Verilator | Yosys | Xcelium | ls-sv extractor | fourstate | run2 |
|---|---|---|---|---|---|---|---|---|
| `dc_port_net_init` | ERROR: only 'output' variable port declarations may have an initial | reject | A | A | A | `PortSymbol:initializer` | REJECT |  |
| `dc_port_net_init2` | ERROR: only 'output' variable port declarations may have an initial | reject | A | B | C | `ContinuousAssignSymbol:initialized-net`, `PortSymbol:initializer` | REJECT |  |
| `pi_explicit` | ok | A | reject | reject | A | `PortSymbol:explicit-expression` | REJECT |  |

Traces (one value per stimulus cycle; a letter names one distinct trace of the case):

* `dc_port_net_init`: **A** = `y=00000011,00000011`
* `dc_port_net_init2`: **A** = `y=00000001,11111111`; **B** = `y=00000011,00000011`; **C** = `y=000000x1,xxxxxx11`
* `pi_explicit`: **A** = `y=11,10,1x`

### lit-string / lit-string-hex

| case | slang | Icarus | Verilator | Yosys | Xcelium | ls-sv extractor | fourstate | run2 |
|---|---|---|---|---|---|---|---|---|
| `lit_str_a` | ok | A | A | A | B | `StringLiteral:named-control-escape` | pass |  |
| `lit_str_v` | ok | A | A | A | B | `StringLiteral:named-control-escape` | pass |  |
| `lit_str_f` | ok | A | A | A | B | `StringLiteral:named-control-escape` | pass |  |
| `lit_str_n` | ok | A | A | A | A | - | pass |  |
| `lit_str_x41` | ok | A | A | B | B | `StringLiteral:hex-escape` | pass | REFUSES:  run2: unsupported: unsupported expression 'StringLiteral:hex-escape' [StringLiteral:hex-escap |
| `lit_str_x4` | ok | A | reject | B | B | `StringLiteral:hex-escape` | pass |  |
| `hex_guard` | ok | A | A | B | B | `StringLiteral:hex-escape` | pass | REFUSES:  run2: unsupported: unsupported expression 'StringLiteral:hex-escape' [StringLiteral:hex-escap |
| `lit_str_o101` | ok | A | A | A | A | - | pass |  |
| `lit_str_nonlatin` | ok | A | A | A | A | `StringLiteral:width` | REJECT |  |
| `lit_str_nonlatin2` | ok | A | A | A | B | `StringLiteral:width` | REJECT |  |

Traces (one value per stimulus cycle; a letter names one distinct trace of the case):

* `lit_str_a`: **A** = `y=00000111`; **B** = `y=01100001`
* `lit_str_v`: **A** = `y=00001011`; **B** = `y=01110110`
* `lit_str_f`: **A** = `y=00001100`; **B** = `y=01100110`
* `lit_str_n`: **A** = `y=00001010`
* `lit_str_x41`: **A** = `y=01000001`; **B** = `y=00110001`
* `lit_str_x4`: **A** = `y=00000100`; **B** = `y=00110100`
* `hex_guard`: **A** = `y=01000001,01000001`; **B** = `y=00110001,01000001`
* `lit_str_o101`: **A** = `y=01000001`
* `lit_str_nonlatin`: **A** = `y=10101001`
* `lit_str_nonlatin2`: **A** = `y=1100001110101001`; **B** = `y=1111111110101001`

### hi-override-context

| case | slang | Icarus | Verilator | Yosys | Xcelium | ls-sv extractor | fourstate | run2 |
|---|---|---|---|---|---|---|---|---|
| `fold_ovr` | ok | A | B | C | A | `InstanceSymbol:override-context` | pass |  |
| `fold_ovrw_n1` | ok | A | B | B | A | `InstanceSymbol:override-context` | pass |  |
| `fold_ovrw_n24` | ok | A | B | B | A | `InstanceSymbol:override-context` | pass |  |
| `fold_uwovr` | ok | A | B | B | B | `InstanceSymbol:override-untyped-width` | pass |  |
| `fold_uwovr_n0` | ok | A | B | B | B | `InstanceSymbol:override-untyped-width` | pass |  |
| `fold_sho_n1` | ok | A | B | B | B | `InstanceSymbol:override-untyped-width` | pass |  |
| `fold_sho_n40` | ok (warn) | A | B | B | B | `InstanceSymbol:override-untyped-width` | pass |  |

Traces (one value per stimulus cycle; a letter names one distinct trace of the case):

* `fold_ovr`: **A** = `o1=1111111011010011,0000000100101100,1110001011000101,0111010001111000,0010000101100011,0x001xx000x11x00;o2=1111111011010011,0000000100101100,1110001011000101,0111010001111000,0010000101100011,0x001xx000x11x00`; **B** = `o1=1111111111010011,0000000000101100,1110001111000101,0111010101111000,0010000001100011,0000100100111100;o2=1111111111010011,0000000000101100,1110001111000101,0111010101111000,0010000001100011,0000100100111100`; **C** = `o1=1111111111010011,0000000000101100,1110001111000101,0111010101111000,0010000001100011,0x001xx100x11x00;o2=1111111111010011,0000000000101100,1110001111000101,0111010101111000,0010000001100011,0x001xx100x11x00`
* `fold_ovrw_n1`: **A** = `o1=1111111111111111111111110000000000000000000000000000000000000000,1111111111111111111111110000000000000000000000000000000000000000,1111111111111111111111110000000000000000000000000000000000000000`; **B** = `o1=0000000000000000000000000000000000000000000000000000000000000000,0000000000000000000000000000000000000000000000000000000000000000,0000000000000000000000000000000000000000000000000000000000000000`
* `fold_ovrw_n24`: **A** = `o1=0000000000000000000110000000000000000000000000000000000000000000,0000000000000000000110000000000000000000000000000000000000000000,0000000000000000000110000000000000000000000000000000000000000000`; **B** = `o1=0000000000000000000000000000000000000000000000000000000000000000,0000000000000000000000000000000000000000000000000000000000000000,0000000000000000000000000000000000000000000000000000000000000000`
* `fold_uwovr`: **A** = `o1=0000000000000000000000000001111000000000000000000000000000001001,0000000000000000000000000000000000000000000000000000000000001001,0000000000000000000000000000111000000000000000000000000000001001`; **B** = `o1=0000000000000000000000000000111100000000000000000000000000001001,0000000000000000000000000000000000000000000000000000000000001001,0000000000000000000000000000011100000000000000000000000000001001`
* `fold_uwovr_n0`: **A** = `o1=0000000000000000000000000001111000000000000000000000000000000001,0000000000000000000000000000000000000000000000000000000000000001,0000000000000000000000000001111000000000000000000000000000000001`; **B** = `o1=0000000000000000000000000000111100000000000000000000000000000001,0000000000000000000000000000000000000000000000000000000000000001,0000000000000000000000000000111100000000000000000000000000000001`
* `fold_sho_n1`: **A** = `o1=00000000000000000000000000000000000000000001111000000000000000000000000000000010,00000000000000000000000000000000000000000000000000000000000000000000000000000010,000000000000000000000000000000000000000000000000000000000000000000000000000`; **B** = `o1=00000000000000000000000000000000000000000000111100000000000000000000000000000010,00000000000000000000000000000000000000000000000000000000000000000000000000000010,000000000000000000000000000000000000000000000000000000000000000000000000000`
* `fold_sho_n40`: **A** = `o1=00001111000000000000000000000000000000010000000000000000000000000000000000000000,00000000000000000000000000000000000000010000000000000000000000000000000000000000,000000100000000000000000000000000000000100000000000000000000000000000000000`; **B** = `o1=00000000000000000000000000000000000000000000111100000000000000000000000000000000,00000000000000000000000000000000000000000000000000000000000000000000000000000000,000000000000000000000000000000000000000000000010000000000000000000000000000`

### le-portconn-context-width

| case | slang | Icarus | Verilator | Yosys | Xcelium | ls-sv extractor | fourstate | run2 |
|---|---|---|---|---|---|---|---|---|
| `ctx_pq` | ok | A | B | A | B | - | pass | REFUSES:  run2: unsupported: unsupported process 'PortConn:context-width' [PortConn:context-width: inpu |
| `ctx_const40` | ok | A | A | A | A | `PortConnection:int-width` | pass | REFUSES:  run2: unsupported: unsupported process 'PortConn:context-width' [PortConn:context-width: inpu |

Traces (one value per stimulus cycle; a letter names one distinct trace of the case):

* `ctx_pq`: **A** = `y=0000,0001,0010,0011,0001,0010,0011,0000,0010,0011,0000,0001,0011,0000,0001,0010;z=0011,0011,0011,0011,0010,0010,0010,0010,0001,0001,0001,0001,0000,0000,0000,0000`; **B** = `y=0000,0001,0010,0011,0001,0010,0011,0100,0010,0011,0100,0101,0011,0100,0101,0110;z=1111,1111,1111,1111,1110,1110,1110,1110,1101,1101,1101,1101,1100,1100,1100,1100`
* `ctx_const40`: **A** = `y=1111111111111111111111111111111111111111`

### gu-self-read

| case | slang | Icarus | Verilator | Yosys | Xcelium | ls-sv extractor | fourstate | run2 |
|---|---|---|---|---|---|---|---|---|
| `rbw_comb` | ok | A | B | B | C | - | pass | REFUSES:  run2: unsupported: unsupported process 'AlwaysComb:self-read' [AlwaysComb:self-read: always_c |
| `rbw_held` | ok | A | B | B | C | - | pass |  |
| `rbw_bits` | ok | A | B | B | C | - | pass |  |
| `rbw_cond` | ok | A | B | B | A | - | pass |  |
| `rbw_case_item` | ok | A | B | B | C | - | pass |  |
| `rbw_dyn` | ok | A | B | B | C | - | pass |  |
| `rbw_part` | ok | A | B | B | C | - | pass |  |
| `rbw_nested` | ok | A | B | B | C | - | pass |  |
| `rbw_child` | ok | A | B | B | C | - | pass |  |

Traces (one value per stimulus cycle; a letter names one distinct trace of the case):

* `rbw_comb`: **A** = `y=00,00,01,10`; **B** = `y=00,01,10,11`; **C** = `y=xx,00,01,10`
* `rbw_held`: **A** = `y=01,01,11`; **B** = `y=01,10,11`; **C** = `y=xx,01,11`
* `rbw_bits`: **A** = `y=0,0,1,1,0`; **B** = `y=0,1,1,0,0`; **C** = `y=x,0,1,1,0`
* `rbw_cond`: **A** = `y=0,0,1,1,1`; **B** = `y=0,1,0,1,0`
* `rbw_case_item`: **A** = `y=1,1,1,1`; **B** = `y=1,0,1,0`; **C** = `y=0,1,1,1`
* `rbw_dyn`: **A** = `y=0,0,0,1,0`; **B** = `y=0,1,1,0,1`; **C** = `y=x,0,0,1,0`
* `rbw_part`: **A** = `y=00,00,01,10`; **B** = `y=00,01,10,11`; **C** = `y=xx,00,01,10`
* `rbw_nested`: **A** = `y=0,0,0,1,0`; **B** = `y=0,1,0,0,1`; **C** = `y=x,0,0,1,0`
* `rbw_child`: **A** = `y=0,0,1,1,0`; **B** = `y=0,1,1,0,0`; **C** = `y=x,0,1,1,0`

### gu-alias-read

| case | slang | Icarus | Verilator | Yosys | Xcelium | ls-sv extractor | fourstate | run2 |
|---|---|---|---|---|---|---|---|---|
| `acg_alias_assign` | ok | A | B | C | C | - | pass | REFUSES:  AlwaysComb:alias-read: always_comb block of module 'acg_alias_assign' reads bits [1:0] of 'w' |
| `acg_alias_port` | ok | A | B | B | B | - | pass |  |
| `acg_alias_chain` | ok | A | B | C | C | - | pass |  |
| `acg_alias_not` | ok | A | B | A | A | - | pass |  |
| `acg_alias_bits` | ok | A | B | C | C | - | pass |  |
| `acg_alias_hier` | ok | A | B | C | C | - | pass |  |
| `acg_alias_thru` | ok | A | B | C | C | - | pass |  |
| `acg_alias_wr` | ok | A | B | A | A | - | pass |  |
| `acg_alias_copy` | ok | A | B | A | A | - | pass |  |

Traces (one value per stimulus cycle; a letter names one distinct trace of the case):

* `acg_alias_assign`: **A** = `y=11,11,10,00,11,00,11,1x`; **B** = `y=11,10,00,11,00,11,10,11`; **C** = `y=11,10,00,11,00,11,1x,11`
* `acg_alias_port`: **A** = `y=00,00,01,10,10,01,11,00`; **B** = `y=00,01,10,01,01,11,00,10`
* `acg_alias_chain`: **A** = `y=11,11,10,00,11,00,11,1x`; **B** = `y=11,10,00,11,00,11,10,11`; **C** = `y=11,10,00,11,00,11,1x,11`
* `acg_alias_not`: **A** = `y=00,01,11,00,11,00,0x,00`; **B** = `y=00,01,11,00,11,00,01,00`
* `acg_alias_bits`: **A** = `y=00,00,11,11,01,11,x0,01`; **B** = `y=00,10,11,01,11,01,00,11`; **C** = `y=00,10,11,01,11,x1,00,11`
* `acg_alias_hier`: **A** = `y=11,11,10,00,11,00,11,1x`; **B** = `y=11,10,00,11,00,11,10,11`; **C** = `y=11,10,00,11,00,11,1x,11`
* `acg_alias_thru`: **A** = `y=11,11,10,00,11,00,11,1x`; **B** = `y=11,10,00,11,00,11,10,11`; **C** = `y=11,10,00,11,00,11,1x,11`
* `acg_alias_wr`: **A** = `y=11,10,00,11,00,11,1x,11`; **B** = `y=11,10,00,11,00,11,10,11`
* `acg_alias_copy`: **A** = `y=11,10,00,11,00,11,1x,11`; **B** = `y=11,10,00,11,00,11,10,11`

### gu-comb-loop / pr-always-nocontrol

| case | slang | Icarus | Verilator | Yosys | Xcelium | ls-sv extractor | fourstate | run2 |
|---|---|---|---|---|---|---|---|---|
| `loop_osc` | ok | A | ok(%Error: tb_v.sv:4: Settle region did not) | B | B | - | REJECT | runs |
| `loop_osc2` | ok | timeout | A | netlist-sim-timeout | B | - | REJECT | REFUSES:  run2: timeout (fuel exhausted / comb loop) |
| `loop_mux` | ok | A | A | A | A | - | REJECT | runs |
| `loop_fn` | ok | A | A | A | A | - | REJECT | runs |
| `loop_sr` | ok | timeout | A | netlist-sim-timeout | B | - | REJECT | runs |
| `loop_comb_block` | ok | A | A | A | A | - | pass | runs |
| `loop_lat_if` | ok | A | A | B | A | - | REJECT | runs |
| `loop_lat_if_b` | ok | A | A | A | A | - | REJECT | runs |
| `alw_nocontrol` | ERROR: 'always' procedure does not advance time and so will create  | reject | A | A | hangs | `ProceduralBlockSymbol:NoEventControl` | pass | REFUSES:  run2: unsupported: unsupported process 'ProceduralBlockSymbol:NoEventControl' [ProceduralBloc |
| `alw_nocontrol_ff` | ERROR: always_ff procedure must have one and only one event control | reject | A | reject | reject | `ProceduralBlockSymbol:NoEventControl` | REJECT | REFUSES:  run2: unsupported: unsupported process 'ProceduralBlockSymbol:NoEventControl' [ProceduralBloc |

Traces (one value per stimulus cycle; a letter names one distinct trace of the case):

* `loop_osc`: **A** = `y=z`; **B** = `y=x`
* `loop_osc2`: **A** = `a=0`; **B** = `a=0,1,0`
* `loop_mux`: **A** = `y=1,1,0,0`
* `loop_fn`: **A** = `a=1,0,0,1,1;b=1,0,0,1,1`
* `loop_sr`: **A** = `q=1,1,0,0,0,0;qn=0,0,1,1,0,1`; **B** = `q=1,1,0,0,0,1;qn=0,0,1,1,0,0`
* `loop_comb_block`: **A** = `y=01,10,11`
* `loop_lat_if`: **A** = `y=0,0,0,0,0,0`; **B** = `y=x,x,0,0,0,0`
* `loop_lat_if_b`: **A** = `y=0,0,0,0,0`
* `alw_nocontrol`: **A** = `y=00000001,00000010`
* `alw_nocontrol_ff`: **A** = `y=00000001,00000010`
