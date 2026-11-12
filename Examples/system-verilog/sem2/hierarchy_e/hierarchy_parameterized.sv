module leaf_param #(parameter integer W = 4)(input wire [W-1:0] a, output wire [W-1:0] y);
  assign y = a;
endmodule
module hierarchy_parameterized #(parameter integer W = 8)(input wire [W-1:0] a, output wire [W-1:0] y);
  leaf_param #(.W(W/2)) lo(.a(a[W/2-1:0]), .y(y[W/2-1:0]));
  leaf_param #(.W(W/2)) hi(.a(a[W-1:W/2]), .y(y[W-1:W/2]));
endmodule
