// Genvar initializers that are context-propagating expressions over narrow
// parameters (round 4 folds, verifier repro rf_gv): IEEE 1800-2023 and
// Yosys 0.53/slang evaluate `U + 1'b1` in the genvar's 32-bit context,
// Icarus 12.0 at its own width — where the two readings differ the model
// refuses; where they agree it runs.
module fold_rgv #(parameter int N = 32, parameter logic [N-1:0] U = 3,
                  parameter logic signed [3:0] S = 1) (
  input  logic [3:0] a,
  output logic [16:0] o3,
  output logic [3:0] o4);
  // The 32-bit readings, as INT-class localparams (every tool agrees on
  // those): the bits below each loop's start are driven 0, so every bit is
  // driven exactly once wherever the two readings of the initializer agree.
  localparam integer I0 = U + 1'b1;
  localparam integer J0 = S + S;
  for (genvar g = U + 1'b1; g < 17; g++) begin : G
    assign o3[g] = 1'b1;
  end
  for (genvar k = 0; k < I0 && k < 17; k++) begin : GZ
    assign o3[k] = 1'b0;
  end
  for (genvar h = S + S; h < 4; h++) begin : H
    assign o4[h] = a[h];
  end
  for (genvar k = 0; k < J0 && k < 4; k++) begin : HZ
    assign o4[k] = 1'b0;
  end
endmodule
