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

The entry applies only to its named simulator and single schedule. A changed
input or trace fails the harness. Agreement also fails while the entry is
live, requiring review and removal of the resolved declaration. Missing
tools and failed simulations cannot satisfy an entry. Xcelium runs keep
their ordinary comparison. CI runs mutation and reporting tests even on
hosts without a simulator, and emits warnings for measured disagreements.

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
`nested_member_concat`, `typedef_nested_concat`, and
`fixed_array_noncanonical_slice`. Their declarations bind each observed pair
separately. No licensed-simulator confirmation is claimed for this group.

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
status, stdout and stderr for review.

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
