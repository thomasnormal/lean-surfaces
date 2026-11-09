// Clean-room memory-route guard for declared-signal selects.
`timescale 1ns/1ns
module dark_selects (
  input logic clk,
  input logic [31:0] d,
  input logic [4:0] i,
  output logic [7:0] q,
  output logic b
);
  logic [31:0] r;
  always @(posedge clk) r <= d;
  assign q = r[7:0];
  assign b = r[i];
endmodule
