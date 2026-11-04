// WP-B2 gate 3: shifts by an unsized constant amount (`a << 1` was the gate-1 negative `neg_shift`).
module shl_const #(parameter int N = 4) (
  input  logic [N-1:0] a,
  output logic [N-1:0] y,
  output logic [N-1:0] z
);
  assign y = a << 1;
  assign z = a >> 2;
endmodule
