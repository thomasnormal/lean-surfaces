// SPDX-License-Identifier: Apache-2.0
// A drive strength on a continuous assignment to a variable. The tools share no reading of it (measured 2026-11-01,
// stimulus a = 0 1 x z 0 1): Icarus 12 applies it, so `(strong0, highz1)` drives z where a = 1; Xcelium 24.03 ignores
// it on a variable (`*W,CAVSTR`) and reads y = a; Yosys 0.53 cannot read it (syntax error), so there is no scored
// netlist; Verilator 5.042 stops (`Unsupported: highz strength`). The symbolic extractor used to read the strength from
// source bytes that only the M0 path loads and admitted the assignment as a plain one (y = a); it refuses it loudly
// now: `ContinuousAssignSymbol:strength` (P-SAME-PROGRAM).
module cstr_highz (
  input  logic a,
  output logic y
);
  assign (strong0, highz1) y = a;
endmodule
