// WP-B2: an adder with a carry-in and a carry-out written with `+`. The sum is formed in the (N+1)-bit signal t
// (every operand zero-extended to N+1 bits, the carry lands in t[N]); s and cout are selects of it.
module addw #(parameter int N = 8) (
  input  logic [N-1:0] a, b,
  input  logic         cin,
  output logic [N-1:0] s,
  output logic         cout
);
  logic [N:0] t;
  assign t = a + b + cin;
  assign s = t[N-1:0];
  assign cout = t[N];
endmodule
