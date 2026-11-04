// WP-B2 gate 3: a barrel shifter written with the word-level operator. The left operand is context-determined
// (`N` bits, the target's width), the amount is self-determined and unsigned (3 bits): `a << s` is `BitVec` `<<<`,
// an amount of `N` or more gives 0.
module shl_n #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [2:0]   s,
  output logic [N-1:0] y
);
  assign y = a << s;
endmodule
