// WP-B2 gate 3b pin P18: concatenations as operands. `s`: bare concatenations (as wide as the sum) plus a 1-bit operand; `t`: a bare and a narrower one (a `Resize` marker around the concatenation); `u`: markers around both operands of a subtraction; `w`: concatenations in the arms of `?:`; `e`: `==` of two concatenations. An x/z bit of an operand makes the whole sum x; a concatenation keeps its x/z bits in place.
module wl_cat_add #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  input  logic cin,
  output logic [N:0] s,
  output logic [N+1:0] t,
  output logic [N+2:0] u,
  output logic [N:0] w,
  output logic e
);
  assign s = {1'b0, a} + {1'b0, b} + cin;
  assign t = {2'b0, a} + {b, 1'b0};
  assign u = {a, 1'b1} - {1'b0, b, 1'b0};
  assign w = cin ? {a, 1'b0} : {1'b1, a};
  assign e = {a, b} == {b, a};
endmodule
