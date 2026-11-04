// WP-B2 gate 3: the logical right shift by a run-time amount (`>>`, zero fill), `BitVec` `>>>`.
module shr_n #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [2:0]   s,
  output logic [N-1:0] y
);
  assign y = a >> s;
endmodule
