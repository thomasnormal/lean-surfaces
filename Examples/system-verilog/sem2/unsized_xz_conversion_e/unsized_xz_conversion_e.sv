// Clean-room E memory fixture: parser-retained unsized x/z conversions.
// IEEE 1800-2023 §5.7.1 extends each literal's 32-bit payload with its
// most-significant x/z bit at the destination width.
module unsized_xz_conversion_e #(parameter int N = 40) (
  input logic clk,
  output logic [N-1:0] qx,
  output logic [N-1:0] qz,
  output logic [N-1:0] qhx,
  output logic [N-1:0] qhz,
  output logic [N-1:0] mem_q
);
  logic [N-1:0] mem [0:N-1];
  assign mem_q = mem[0];

  always_ff @(posedge clk) begin
    qx  <= 'bx;
    qz  <= 'bz;
    qhx <= 'hx0;
    qhz <= 'hz1;
  end
endmodule
