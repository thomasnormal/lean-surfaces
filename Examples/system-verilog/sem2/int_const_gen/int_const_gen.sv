// Genvar-width targets (`neg[(g*(g-1))/2 +: g]`, g = 1..3): slang binds the
// constant at the FIRST iteration's width (1 bit); the envelope keeps the
// unconverted constant and the model fits it at each iteration's width
// (verifier w_gvw_flat: 001011 where every simulator reads 111111).
module int_const_gen (
  input  logic [3:0] a,
  output logic [5:0] neg,
  output logic [5:0] gv,
  output logic [5:0] gm
);
  for (genvar g = 1; g <= 3; g++) begin : gl
    assign neg[(g*(g-1))/2 +: g] = -1;
    assign gv[(g*(g-1))/2 +: g] = g + 4;
    assign gm[(g*(g-1))/2 +: g] = -g;
  end
endmodule
