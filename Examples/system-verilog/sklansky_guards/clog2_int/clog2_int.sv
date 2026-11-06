// Clean-room guard for a 32-bit signed int localparam using $clog2.
module clog2_int #(parameter int N = 16)
  (input logic [N-1:0] a, output logic [N-1:0] y);
  localparam int L = $clog2(N + 1);
  assign y = a;
endmodule
