// Clean-room hierarchy wall: an uncovered output-net bit remains z.
module ov_leaf #(parameter integer W = 4) (
  input wire [W-1:0] a,
  output wire [W-1:0] y
);
  assign y = a;
endmodule
module hierarchy_wire_hole #(parameter integer W = 8, parameter integer P = 4) (
  input wire [W-1:0] a,
  output wire [W-1:0] y
);
  ov_leaf #(.W(P)) lo(.a(a[P-1:0]), .y(y[P-1:0]));
  ov_leaf #(.W(W - W/2)) hi(.a(a[W-1:W/2]), .y(y[W-1:W/2]));
endmodule
