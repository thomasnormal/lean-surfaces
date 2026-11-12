// IEEE 1800-2023 §11.4.10: shifts use the 32-bit int operand pattern.
module int32_negative_shift_e #(parameter int N = 8) (
  output logic [31:0] left_zero,
  output logic [31:0] logical_right,
  output logic [31:0] arithmetic_right,
  output logic [31:0] logical_param,
  output logic [31:0] arithmetic_param
);
  localparam int L = 1 << -1;
  localparam int R = -8 >> 1;
  localparam int A = -8 >>> 1;
  localparam int RP = -N >> 1;
  localparam int AP = -N >>> 1;
  assign left_zero = L;
  assign logical_right = R;
  assign arithmetic_right = A;
  assign logical_param = RP;
  assign arithmetic_param = AP;
endmodule
