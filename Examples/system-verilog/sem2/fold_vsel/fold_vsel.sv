// Round 3 folds, item 3: run-time and genvar labels keep the legacy offset
// encoding (`v[s]`, `w[g] = v[g]`), exact while `logic [N-1:0] v` is
// [m:0] with m >= 0. At N = 0 it is the ascending [-1:0]: `v[s]` at s = 1
// reads label 1 (out of range, x in Icarus and Yosys), not offset 1.
module fold_vsel #(parameter int N = 3) (
  input  logic [N-1:0] v,
  input  logic [1:0]   b,
  input  logic         s,
  output logic [1:0]   y,
  output logic         o,
  output logic [1:0]   w
);
  for (genvar g = 0; g < 2; g++) begin : gl
    assign y[g] = v[0];
    assign w[g] = v[g] ^ b[g];
  end
  assign o = v[s];
endmodule
