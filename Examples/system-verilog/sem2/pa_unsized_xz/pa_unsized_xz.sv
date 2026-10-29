// An unsized x/z literal widened inside an INPUT PORT ACTUAL (round 5 Lane
// A, 2026-10-29; INIT2 verifier repro `p8`). The tools split: Icarus 12.0
// evaluates an actual narrower than its port self-determined and pads it
// with ZEROS ("Padding 8 high bits of the port"), Xcelium 24.03 and Yosys
// 0.53 (`40'hxxxxxxxxx0`) extend the x (IEEE 1800-2023 §5.7.1, §23.3.3).
// At a = 0: z1 = 8 zeros, 28 x, 0000 in Icarus, 36 x then 0000 in Yosys;
// z2 = 4 zeros, 32 z against 36 z; z3 = 16 zeros, 28 z, 0001 against 44 z
// then 0001; z4 (`s ? 'hx0 : 'h5`, s = 1) and z5 (`'hx0 | a`) the same
// split. The model followed Icarus at 2e8c8b28 (a zero-extending `Resize`)
// and Xcelium/Yosys after round 4 (the literal padded); now loud
// (`PortConnection:unsized-xz`).
module pa_unsized_xz_c40 (input logic [39:0] i, output logic [39:0] o);
  assign o = i;
endmodule

module pa_unsized_xz_w #(
  parameter int W = 40
) (
  input  logic [W-1:0] i,
  output logic [W-1:0] o
);
  assign o = i;
endmodule

module pa_unsized_xz (
  input  logic        clk,
  input  logic        s,
  input  logic [7:0]  a,
  output logic [39:0] z1,
  output logic [35:0] z2,
  output logic [47:0] z3,
  output logic [39:0] z4,
  output logic [39:0] z5
);
  pa_unsized_xz_c40 u1 (.i('hx0), .o(z1));
  pa_unsized_xz_w #(.W(36)) u2 (.i('bz), .o(z2));
  pa_unsized_xz_w #(.W(48)) u3 (.i('hz1), .o(z3));
  pa_unsized_xz_c40 u4 (.i(s ? 'hx0 : 'h5), .o(z4));
  pa_unsized_xz_c40 u5 (.i('hx0 | a), .o(z5));
endmodule
