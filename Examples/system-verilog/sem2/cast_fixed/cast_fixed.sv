// A literal unsigned sized cast keeps the source four-state bits and
// zero-extends them to the fixed target width.
module cast_fixed (
  input  logic [3:0] a,
  output logic [7:0] y
);
  always_comb y = 8'(a);
endmodule
