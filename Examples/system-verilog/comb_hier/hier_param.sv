// The two halves through `W/2` itself: one parameterized identity leaf per half, the halves selected by `W/2` in the parent's
// port connections (no localparam), and the parent's output a `wire` tiled by the instances' output ports.
module leaf #(parameter integer W = 4) (input wire [W-1:0] a, output wire [W-1:0] y);
  assign y = a;
endmodule
module hierarchy_parameterized #(parameter integer W = 8) (input wire [W-1:0] a, output wire [W-1:0] y);
  leaf #(.W(W/2)) lo(.a(a[W/2-1:0]), .y(y[W/2-1:0]));
  leaf #(.W(W/2)) hi(.a(a[W-1:W/2]), .y(y[W-1:W/2]));
endmodule
