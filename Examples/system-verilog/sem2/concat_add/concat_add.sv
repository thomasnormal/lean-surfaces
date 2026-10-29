// A one-line N-bit adder with a concatenated continuous-assignment target:
// the RHS is evaluated at the target's width N + 1 (each operand
// zero-extended), and {cout, s} distributes it MSB-first. The hand-built twin
// `LeanModels.Sv.Comb2ConcatExample.caddDesign N` is proved correct for every N.
module concat_add #(parameter int N = 4) (
  input  logic [N-1:0] a, b,
  input  logic         cin,
  output logic [N-1:0] s,
  output logic         cout
);
  assign {cout, s} = a + b + cin;
endmodule
