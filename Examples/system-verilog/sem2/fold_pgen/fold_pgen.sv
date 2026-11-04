// Round 3 folds, item 1, where the oracles split: a GENVAR used as a simple
// operand in an unsigned context. Up to 32 bits (N <= 30) every tool agrees.
// Wider, a negative genvar is zero-extended by Yosys 0.53, Verilator 5.042
// and the LRM (the loop's implicit localparam is an `integer`, IEEE
// 1800-2023 27.4, converted to the unsigned context type first, 11.8.2) but
// SIGN-extended by Icarus 12.0: the model refuses (`GenvarRef:unsigned-
// extension`). A non-negative genvar extends the same either way.
module fold_pgen #(parameter int N = 7, parameter int G0 = -1) (
  input  logic [N+1:0] a,
  output logic [N+1:0] o
);
  for (genvar g = G0; g < G0 + 1; g++) begin : gl
    assign o = a ^ g;
  end
endmodule
