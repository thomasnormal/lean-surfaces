module int32_negative_shift_e_tb;
  logic [31:0] left_zero, logical_right, arithmetic_right, logical_param, arithmetic_param;
  logic [31:0] left_zero1, logical_right1, arithmetic_right1, logical_param1, arithmetic_param1;
  int32_negative_shift_e #(.N(8)) d0(.left_zero(left_zero),.logical_right(logical_right),.arithmetic_right(arithmetic_right),.logical_param(logical_param),.arithmetic_param(arithmetic_param));
  int32_negative_shift_e #(.N(16)) d1(.left_zero(left_zero1),.logical_right(logical_right1),.arithmetic_right(arithmetic_right1),.logical_param(logical_param1),.arithmetic_param(arithmetic_param1));
  initial begin
    #1;
    $display("ROW N=8 left=%h logical=%h arithmetic=%h logical_param=%h arithmetic_param=%h",left_zero,logical_right,arithmetic_right,logical_param,arithmetic_param);
    $display("ROW N=16 left=%h logical=%h arithmetic=%h logical_param=%h arithmetic_param=%h",left_zero1,logical_right1,arithmetic_right1,logical_param1,arithmetic_param1);
    $finish;
  end
endmodule
