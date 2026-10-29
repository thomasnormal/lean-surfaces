// A genvar initializer wider than the genvar's 32 bits (round 4 folds):
// `genvar m = U` with `logic [N-1:0] U` is an assignment to a 32-bit
// `integer`. Where U's value does not fit (N = 40, U = 2^40 - 1) slang and
// IEEE 1800-2023 (27.4) truncate it (m starts at -1) while Icarus 12.0 and
// Yosys 0.53 keep it whole (no iteration): the model refuses. Where it fits
// every tool agrees. The 32-bit reading drives the bits below the start.
module fold_rgvw #(parameter int N = 32, parameter logic [N-1:0] U = 3) (
  input  logic [3:0] a,
  output logic [3:0] o);
  localparam integer I1 = U;
  for (genvar m = U; m < 4; m++) begin : M
    assign o[m] = a[m];
  end
  for (genvar k = 0; k < I1 && k < 4; k++) begin : MZ
    assign o[k] = 1'b0;
  end
endmodule
