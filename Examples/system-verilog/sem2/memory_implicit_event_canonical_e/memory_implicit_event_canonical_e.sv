// Clean-room boundary: implicit event control beside source-shaped memory.
module memory_implicit_event_canonical_e #(parameter integer W=4, parameter integer P=2) (
  input logic [W-1:0] d, input logic [1:0] idx, output logic [W-1:0] q);
  logic [W-1:0] s [P];
  initial begin s[0] = 4'h5; s[1] = 4'h9; end
  always @* q = s[idx] ^ d;
endmodule
