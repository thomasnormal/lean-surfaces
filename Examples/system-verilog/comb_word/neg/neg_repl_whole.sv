// WP-B2 gate 4c: a replication of a WHOLE signal is refused (its width is the declared one; replicate a bit or a part select).
module neg_repl_whole #(parameter int N = 4) (
  input  logic [N-1:0] a,
  output logic [2*N-1:0] y
);
  assign y = {2{a}};
endmodule
