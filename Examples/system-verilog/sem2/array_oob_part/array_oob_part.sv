// Part and indexed-part selects that overhang an INNER dimension of a
// NON-last element, and an element label outside an ASCENDING dimension.
// IEEE 1800-2023 7.4.6/11.5.1: each dimension is range-checked on its own -
// out-of-range bits read x and an msb-overhanging write is clipped. Icarus
// 12.0 and Yosys 0.53 linearize into the neighbouring element instead (a
// declared disagreement, docs/sv-oracle-disagreements.md).
module array_oob_part (
  input  logic [7:0] src,
  input  logic [3:0] a,
  output logic [2:0] d_hi,
  output logic [2:0] r_lo,
  output logic [1:0] r_hi,
  output logic       asc_oob,
  output logic [7:0] w_flat
);
  logic [1:0][3:0] m;
  logic [0:1][0:3] q;
  logic [1:0][3:0] w;
  assign m = src;
  assign q = src;
  always_comb begin
    d_hi = m[0][5:3];
    r_lo = q[0][2 +: 3];
    r_hi = q[1][-1 +: 2];
    asc_oob = q[0][4];
  end
  always_comb begin
    w = 8'h00;
    w[0][5:2] = a;
  end
  assign w_flat = w;
endmodule
