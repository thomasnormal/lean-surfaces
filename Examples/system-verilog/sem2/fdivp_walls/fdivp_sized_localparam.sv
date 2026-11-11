// Clean-room reproduction of the fdivp sized localparam wall.
module fdivp_sized_localparam #(
  parameter int W = 8,
  parameter int OFF = 0,
  parameter int EW = $clog2(W + 1)
) (
  input logic [W-1:0] a,
  output logic [EW-1:0] y
);
  localparam [EW-1:0] KOV = 2**(W-1) - 1 + OFF;
  assign y = KOV;
endmodule
