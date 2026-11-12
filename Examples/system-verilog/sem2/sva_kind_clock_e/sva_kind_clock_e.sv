module restrict_e(input logic clk, input logic a);
  rp: restrict property (@(posedge clk) a);
endmodule
