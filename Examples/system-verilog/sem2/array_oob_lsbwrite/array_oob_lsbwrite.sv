// Part-select TARGETS overhanging the LSB end of their dimension. IEEE
// 1800-2023 11.5.1: writes to the out-of-range bits do nothing, so the
// in-range bits take the RHS's UPPER bits. On a 1-D vector (v) the model,
// Icarus 12.0 and Yosys 0.53 agree. On an INNER dimension of a non-last
// element (w) Icarus 12.0 and Yosys 0.53 linearize the write into the
// element below (a declared disagreement, docs/sv-oracle-disagreements.md).
// Xcelium 24.03-s004 follows neither: it treats a part-select that is only
// partly in range as wholly invalid and DROPS the whole write, on v and on
// w alike (docs/sv-xcelium-audit.md, clusters P3 and DX1).
module array_oob_lsbwrite #(parameter int L = -1) (
  input  logic [3:0] a,
  output logic [7:0] w_flat,
  output logic [7:0] v
);
  logic [1:0][3:0] w;
  always_comb begin
    w = 8'h00;
    w[1][L +: 2] = a[1:0];
  end
  always_comb begin
    v = 8'h00;
    v[L +: 3] = a[2:0];
  end
  assign w_flat = w;
endmodule
