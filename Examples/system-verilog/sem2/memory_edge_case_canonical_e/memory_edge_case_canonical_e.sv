// Clean-room canonical-E row: plain case in a source-shaped edge body.
module memory_edge_case_canonical_e #(parameter integer W = 4) (
  input logic clk, input logic [1:0] sel, input logic [W-1:0] d,
  output logic [W-1:0] q0, output logic [W-1:0] q1,
  output logic [W-1:0] hit);
  logic [W-1:0] mem [0:1];
  initial begin
    mem[0] = 4'h1;
    mem[1] = 4'h2;
  end
  assign q0 = mem[0];
  assign q1 = mem[1];
  always_ff @(posedge clk) begin
    case (sel)
      2'd0: mem[0] <= d;
      2'd1: mem[1] <= d;
      default: hit <= d;
    endcase
  end
endmodule
