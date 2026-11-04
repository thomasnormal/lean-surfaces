// Fixed-width four-state case equality is exact, including X and Z bits.
module case_equality_fixed (
  input  logic a,
  input  logic b,
  output logic eq,
  output logic ne
);
  always_comb begin
    eq = a === b;
    ne = a !== b;
  end
endmodule
