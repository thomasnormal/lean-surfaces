// The halves of `halves.sv` with `wire` ports: the output halves are driven by the instances' ports.
module wire_out_leaf #(parameter integer W = 4) (input wire [W-1:0] a, output wire [W-1:0] y);
  assign y = ~a;
endmodule

module wire_out #(parameter integer W = 8) (input wire [W-1:0] a, output wire [W-1:0] y);
  localparam integer H = W / 2;
  wire_out_leaf #(.W(W / 2)) lo (.a(a[H-1:0]), .y(y[H-1:0]));
  wire_out_leaf #(.W(W / 2)) hi (.a(a[W-1:H]), .y(y[W-1:H]));
endmodule
