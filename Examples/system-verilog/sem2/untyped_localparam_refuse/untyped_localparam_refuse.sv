// IEEE 1800-2023 §§6.20.2, 11.6.1: untyped constants take the initializer type.
// Icarus and Xcelium disagree on lossless intermediate width, so E refuses.
module untyped_localparam_refuse #(parameter int N = 10000) (output logic [31:0] k, output logic [31:0] a);
  localparam K = (N * 1000000) / 1000000;
  localparam A = (N + 32'sd2147483647) % 1000;
  assign k = K;
  assign a = A;
endmodule
