// IEEE 1800-2023 §11.4.10: negative shift counts produce the finite all-zero result.
module int32_negative_shift_e(output logic [31:0] left_zero, output logic [31:0] right_arith);
  localparam int L = 1 << -1;
  localparam int R = -8 >> 1;
  assign left_zero = L;
  assign right_arith = R;
endmodule
