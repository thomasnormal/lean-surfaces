module array_index_e #(parameter int N = 4) (input logic [1:0] i, output logic [7:0] y);
  logic [7:0] values [0:N-1];
  always_comb y = values[i];
endmodule
