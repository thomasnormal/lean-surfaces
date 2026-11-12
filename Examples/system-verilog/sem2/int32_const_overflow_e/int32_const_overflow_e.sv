// Clean-room wrong-answer witness: int intermediates wrap at 32 bits.
module int32_const_overflow_e #(parameter int N = 10000) (
  output logic [31:0] k_out,
  output logic [31:0] s_out,
  output logic [31:0] a_out,
  output logic [31:0] u_out
);
  localparam int K = (N * 1000000) / 1000000;
  localparam int S = (1 << (N + 24)) >> 30;
  localparam int A = (N + 32'sd2147483647) % 1000;
  localparam int U = -32'sh8000_0000;
  assign k_out = K;
  assign s_out = S;
  assign a_out = A;
  assign u_out = U;
endmodule
