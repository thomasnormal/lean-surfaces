// Clean-room canonical-E row: all source case modes in one edge body.
module memory_edge_casez_casex_canonical_e #(parameter integer W = 4, parameter integer D = 2) (
  input logic clk, input logic [3:0] sel, input logic [W-1:0] d,
  output logic [W-1:0] qz, output logic [W-1:0] qx,
  output logic [W-1:0] plain);
  logic [W-1:0] mem [0:D-1];
  initial begin
    mem[0] = 4'h1;
    mem[1] = 4'h2;
    plain = '0;
  end
  assign qz = mem[0];
  assign qx = mem[1];
  always @(posedge clk) begin
    case (sel)
      4'h0: plain <= d;
      default: plain <= '0;
    endcase

    casez (sel)
      4'b1???: mem[0] <= d;
      4'b01??: mem[0] <= 4'h1;
      4'b00z1: mem[0] <= 4'h2;
      default: mem[0] <= 4'h3;
    endcase

    casex (sel)
      4'b1x??: mem[1] <= d;
      4'b01??: mem[1] <= 4'h4;
      4'b00z1: mem[1] <= 4'h5;
      default: mem[1] <= 4'h6;
    endcase
  end
endmodule
