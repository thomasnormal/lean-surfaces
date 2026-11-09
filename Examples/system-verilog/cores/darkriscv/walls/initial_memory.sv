// Clean-room memory-route guard: one source-shaped initial process.
// IEEE 1800-2023 §9.2.1 runs the process once at time zero.
`timescale 1ns/1ns
module initial_memory #(parameter int W = 8, parameter int DEPTH = 2) (
  input  logic clk,
  output logic [W-1:0] q
);
  logic [W-1:0] mem [0:DEPTH-1];

  initial begin
    mem[0] = 8'h3c;
  end

  assign q = mem[0];
endmodule
