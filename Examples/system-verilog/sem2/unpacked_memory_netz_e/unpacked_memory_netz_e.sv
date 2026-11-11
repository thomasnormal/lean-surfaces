// Clean-room E witness: a parameter-sized memory beside an undriven net.
// The net is observed through zq so its IEEE §6.6 initial value is tested.
module unpacked_memory_netz_e #(parameter int N = 4) (
  input logic clk,
  input logic [7:0] d,
  output logic [7:0] q,
  output logic zq
);
  logic [7:0] mem [0:N-1];
  wire pcpi_mul_wr;

  always_ff @(posedge clk) mem[0] <= d;
  assign q = mem[0];
  assign zq = pcpi_mul_wr;
endmodule
