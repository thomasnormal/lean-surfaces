// Clean-room memory-route guard for ordinary case selection.
`timescale 1ns/1ns
module dark_case_memory #(parameter integer N = 1) (
  input logic clk,
  input logic [1:0] sel,
  input logic [7:0] d,
  output logic [7:0] q
);
  logic [7:0] mem [N];
  always @(posedge clk) begin
    case (sel)
      2'd0: mem[0] <= d;
      2'd1: mem[0] <= 8'hA5;
      default: mem[0] <= 8'h5A;
    endcase
  end
  assign q = mem[0];
endmodule
