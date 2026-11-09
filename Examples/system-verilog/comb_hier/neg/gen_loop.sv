// An instance inside a generate loop: one inverter per bit.
module gen_loop_leaf (input logic a, output logic y);
  assign y = ~a;
endmodule

module gen_loop #(parameter integer W = 4) (input logic [W-1:0] a, output logic [W-1:0] y);
  for (genvar i = 0; i < W; i++) begin : g
    gen_loop_leaf u (.a(a[i]), .y(y[i]));
  end
endmodule
