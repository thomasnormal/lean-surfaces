module int32_negative_shift_e_tb;
  logic [31:0] left_zero, right_arith;
  int32_negative_shift_e d(.left_zero(left_zero),.right_arith(right_arith));
  initial begin #1; $display("ROW shifts left=%h right=%h",left_zero,right_arith); $finish; end
endmodule
