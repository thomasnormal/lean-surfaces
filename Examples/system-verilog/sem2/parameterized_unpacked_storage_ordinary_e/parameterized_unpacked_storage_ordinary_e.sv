module parameterized_unpacked_storage_ordinary_e #(parameter int N = 2)
  (input logic [7:0] x, output logic [7:0] y);
  logic [7:0] stage [0:N-1];
  assign stage[0] = x;
  assign y = stage[0];
endmodule
