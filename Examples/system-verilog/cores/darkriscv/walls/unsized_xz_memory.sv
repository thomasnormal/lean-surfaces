// Clean-room memory-route guard: point-dependent unsized x/z conversions.
// IEEE 1800-2023 §5.7.1 extends the literal's own 32-bit payload with its
// most-significant x/z bit to the destination expression width.
`timescale 1ns/1ns
module unsized_xz_memory #(parameter int N = 8) (
  input  logic clk,
  output logic [63:0] qx,
  output logic [63:0] qz,
  output logic [63:0] qhx,
  output logic [63:0] qhz,
  output logic [N-1:0] qm
);
  logic [N-1:0] mem [0:3];

  assign qm = mem[0];

  always @(posedge clk) begin
    qx  <= 'bx;
    qz  <= 'bz;
    qhx <= 'hx0;
    qhz <= 'hz1;
  end
endmodule
