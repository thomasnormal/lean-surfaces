import LeanModels.Sv.Ingest2
import LeanModels.Sv.CombProcSummary

/-!
# `comb_word`: `+`, `-`, `*`, comparisons and shifts in the `sv_comb` fragment (WP-B2)

Twenty-five real envelopes, loaded by `load_design_sv2`:

* `add_same.sv`: `assign y = a + b;` with `a`, `b`, `y` all `N` bits wide (no conversion marker);
* `add_wide.sv`: the same into an `(N+1)`-bit target (slang zero-extends each operand: the `Resize` marker);
* `addw.sv`: a carry-in and a carry-out, `t = a + b + cin` in an `(N+1)`-bit signal and `s`, `cout` selected from it;
* `sub_wide.sv`: `d = a - b` into an `(N+1)`-bit target (zero extension, then a subtraction modulo `2^(N+1)`);
* `addp.sv`: the same operators in the two leaves of an `always_comb` tree, `if (c) y = a + b; else y = a - b;`
  (WP-B2 gate 2: the procedural chain reads the word-level fragment too);
* `cmp_same.sv`: the six comparisons of two `N`-bit operands (WP-B2 gate 2b);
* `cmp_mixed.sv`: comparisons of operands of different widths, against an unsized constant, and into a wider target;
* `trunc_inc.sv`: a sum into a narrower target (a truncation marker), `a + 1` and `a - 1` (an unsized constant);
* `shl_n.sv`, `shr_n.sv`: the barrel shifters `y = a << s` and `y = a >> s` with a RUN-TIME 3-bit amount (WP-B2 gate 3);
* `shl_wide.sv`: `y = a << s` into an `(N+1)`-bit target (the operand is extended BEFORE the shift);
* `onehot.sv`: `y = 1 << s`, the unsized constant `1` as the left operand (computed at `max N 32` bits, truncated);
* `shl_const.sv`: shifts by an unsized constant amount, `a << 1` and `a >> 2`;
* `cat_add.sv`: concatenations as operands of `+`, `?:` and `==` (WP-B2 gate 3b);
* `row_chain.sv`, `row_chain_lp.sv`, `row_chain_lit.sv`: a chain of ROWS of a two-dimensional packed array indexed by a
  genvar, `r[i + 1] = ~r[i]`, over parameter, localparam (rows `2N` wide) and literal dimensions (WP-B2 gate 4a: the
  extractor's legacy `BitSel` over a two-dimensional base is a whole row);
* `ps_rot.sv`: literal-bound part selects (the legacy `PartSel`): a rotation by concatenated part selects, a byte swap
  by part-select TARGETS, a field (gate 4a);
* `ps_gen.sv`: part selects whose bounds are affine in a genvar, read and written inside a generate loop (gate 4a);
* `shl_gen.sv`: a GENVAR as the amount of a shift, `pp[i] = aw << i` (WP-B2 gate 4b: a constant of the instance);
* `repl_pad.sv`: zero padding, `{ {K{1'b0}}, x }` (WP-B2 gate 4c: a replication of a sized literal, a parameter count);
* `repl_mask.sv`: the AND mask of a partial product, `a & {N{b[i]}}` (gate 4c: a replicated bit select);
* `repl_bits.sv`: replications with LITERAL counts, a part select as a whole right-hand side and a sized literal inside a
  concatenation (gate 4c);
* `mul_word.sv`: `p = a * b` into `N` bits (the product modulo `2^N`) and `q = a * b` into `2N` bits (each factor
  zero-extended to the context first: the full product);
* `sq_chain.sv`: a generate loop bounded by a `$clog2` LOCALPARAM, `L = $clog2(N) + 1`, of squarings
  `r[i + 1] = r[i] * r[i]`.

The guards are the non-vacuity checks: the self-determined recognizer (`rdsOf?`) refuses all of them, the
word-level one (`PDesign.summary`, `PDesign.summaryP`, through `rdsOfW?`) accepts them.
-/

namespace Examples.«system-verilog».comb_word.gen

open LeanModels.Sv LeanModels.Sv.CombView

load_design_sv2 add_same from "Examples/system-verilog/comb_word/add_same.sv.json"
load_design_sv2 add_wide from "Examples/system-verilog/comb_word/add_wide.sv.json"
load_design_sv2 addw from "Examples/system-verilog/comb_word/addw.sv.json"
load_design_sv2 sub_wide from "Examples/system-verilog/comb_word/sub_wide.sv.json"
load_design_sv2 addp from "Examples/system-verilog/comb_word/addp.sv.json"
load_design_sv2 cmp_same from "Examples/system-verilog/comb_word/cmp_same.sv.json"
load_design_sv2 cmp_mixed from "Examples/system-verilog/comb_word/cmp_mixed.sv.json"
load_design_sv2 trunc_inc from "Examples/system-verilog/comb_word/trunc_inc.sv.json"
load_design_sv2 shl_n from "Examples/system-verilog/comb_word/shl_n.sv.json"
load_design_sv2 shr_n from "Examples/system-verilog/comb_word/shr_n.sv.json"
load_design_sv2 shl_wide from "Examples/system-verilog/comb_word/shl_wide.sv.json"
load_design_sv2 onehot from "Examples/system-verilog/comb_word/onehot.sv.json"
load_design_sv2 shl_const from "Examples/system-verilog/comb_word/shl_const.sv.json"
load_design_sv2 cat_add from "Examples/system-verilog/comb_word/cat_add.sv.json"
load_design_sv2 row_chain from "Examples/system-verilog/comb_word/row_chain.sv.json"
load_design_sv2 row_chain_lp from "Examples/system-verilog/comb_word/row_chain_lp.sv.json"
load_design_sv2 row_chain_lit from "Examples/system-verilog/comb_word/row_chain_lit.sv.json"
load_design_sv2 ps_rot from "Examples/system-verilog/comb_word/ps_rot.sv.json"
load_design_sv2 ps_gen from "Examples/system-verilog/comb_word/ps_gen.sv.json"
load_design_sv2 shl_gen from "Examples/system-verilog/comb_word/shl_gen.sv.json"
load_design_sv2 repl_pad from "Examples/system-verilog/comb_word/repl_pad.sv.json"
load_design_sv2 repl_mask from "Examples/system-verilog/comb_word/repl_mask.sv.json"
load_design_sv2 repl_bits from "Examples/system-verilog/comb_word/repl_bits.sv.json"
load_design_sv2 mul_word from "Examples/system-verilog/comb_word/mul_word.sv.json"
load_design_sv2 sq_chain from "Examples/system-verilog/comb_word/sq_chain.sv.json"

#guard add_same.pdesign.summary.toOption.isSome
#guard add_wide.pdesign.summary.toOption.isSome
#guard addw.pdesign.summary.toOption.isSome
#guard sub_wide.pdesign.summary.toOption.isSome
#guard addp.pdesign.summaryP.toOption.isSome
#guard cmp_same.pdesign.summary.toOption.isSome
#guard cmp_mixed.pdesign.summary.toOption.isSome
#guard trunc_inc.pdesign.summary.toOption.isSome
#guard shl_n.pdesign.summary.toOption.isSome
#guard shr_n.pdesign.summary.toOption.isSome
#guard shl_wide.pdesign.summary.toOption.isSome
#guard onehot.pdesign.summary.toOption.isSome
#guard shl_const.pdesign.summary.toOption.isSome
#guard cat_add.pdesign.summary.toOption.isSome
#guard row_chain.pdesign.summary.toOption.isSome
#guard row_chain_lp.pdesign.summary.toOption.isSome
#guard row_chain_lit.pdesign.summary.toOption.isSome
#guard ps_rot.pdesign.summary.toOption.isSome
#guard ps_gen.pdesign.summary.toOption.isSome
#guard shl_gen.pdesign.summary.toOption.isSome
#guard repl_pad.pdesign.summary.toOption.isSome
#guard repl_mask.pdesign.summary.toOption.isSome
#guard repl_bits.pdesign.summary.toOption.isSome
#guard mul_word.pdesign.summary.toOption.isSome
#guard sq_chain.pdesign.summary.toOption.isSome

-- the instantiations at small widths
#guard (add_same.sem 4).processes.size == 1
#guard (addw.sem 4).processes.size == 3
#guard (mul_word.sem 4).processes.size == 2
-- `L = $clog2(N) + 1` squarings: 3 at `N = 4`, 4 at `N = 5` (the rows `r[0]`, the `L` squarings, `y`)
#guard (sq_chain.sem 4).processes.size == 5
#guard (sq_chain.sem 5).processes.size == 6

end Examples.«system-verilog».comb_word.gen
