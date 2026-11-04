// A same-width signed'(a) cast changes interpretation without changing bits.
module signed_cast_fixed (
  input logic [7:0] a,
  output logic signed [7:0] y,
  output logic lt
);
  always_comb begin
    y = signed'(a);
    lt = signed'(a) < 8'sd0;
  end
endmodule
