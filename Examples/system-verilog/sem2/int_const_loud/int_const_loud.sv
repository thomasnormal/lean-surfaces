// A signed constant OUTSIDE the INT-class vocabulary (a constant ternary)
// assigned to a parameter-width target: its fold is a default-point value
// (`[N+1:0]` at N = 7), so it is LOUD: `ConversionExpression:signed-constant`.
module int_const_loud #(parameter int N = 7) (
  input  logic [3:0]   a,
  output logic [N+1:0] o
);
  assign o = (3 > 2) ? -1 : 2;
endmodule
