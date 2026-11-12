module int32_const_add_unary_e_tb;
  logic [31:0] a0,u0,a1,u1;
  int32_const_add_unary_e #(.N(2)) d0(.add_mod_out(a0),.unary_min_out(u0));
  int32_const_add_unary_e #(.N(3)) d1(.add_mod_out(a1),.unary_min_out(u1));
  initial begin #1; $display("ROW default a=%0d u=%0d", $signed(a0), $signed(u0)); $display("ROW override a=%0d u=%0d", $signed(a1), $signed(u1)); $finish; end
endmodule
