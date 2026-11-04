// A CHILD's unsized constants on parameter-width outputs, instantiated at an
// override (`W = 8`, the child elaborated alone at its default `W = 2`): the
// unconverted constants are fitted at the child's instantiated width
// (verifier v_cstale: o8 = 00000011, b8 = 00000001 where every simulator
// reads 11111111, 00100101).
module int_const_child #(parameter int W = 2) (
  input  logic [W-1:0] a,
  output logic [W-1:0] ones,
  output logic [W-1:0] big,
  output logic [W-1:0] inc,
  output logic [W-1:0] wm,
  output logic [W-1:0] nw
);
  assign ones = -1;
  assign big  = 37;
  assign inc  = a + 1;
  assign wm   = W - 1;
  assign nw   = -W;
endmodule

module int_const_hier (
  input  logic [7:0] a,
  output logic [1:0] o2, b2, i2, w2, n2,
  output logic [7:0] o8, b8, i8, w8, n8
);
  int_const_child          u2 (.a(a[1:0]), .ones(o2), .big(b2), .inc(i2), .wm(w2), .nw(n2));
  int_const_child #(.W(8)) u8 (.a(a),      .ones(o8), .big(b8), .inc(i8), .wm(w8), .nw(n8));
endmodule
