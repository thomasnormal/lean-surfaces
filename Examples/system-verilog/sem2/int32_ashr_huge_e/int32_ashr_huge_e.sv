// IEEE 1800-2023 §11.4.10: arithmetic right shifts fill with the sign bit.
module int32_ashr_huge_e #(parameter int N = 8) (
  output logic signed [31:0] negative_amount,
  output logic signed [31:0] width_amount,
  output logic signed [31:0] one_amount,
  output logic signed [31:0] parameter_amount
);
  localparam int NEG = -8 >>> -1;
  localparam int HUGE = -8 >>> 40;
  localparam int ONE = -1 >>> 1;
  localparam int PARAM = -8 >>> (N - 9);
  assign negative_amount = NEG;
  assign width_amount = HUGE;
  assign one_amount = ONE;
  assign parameter_amount = PARAM;
endmodule
