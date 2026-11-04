// WP-B2 gate 4c pin P22: REPLICATION. `pad = { {K{1'b0}}, a }` (zero padding: a replication of a sized literal, the count a parameter, as a part of a concatenation; K = 0 is the empty replication, legal beside another operand), `pp[i] = a & {N{b[i]}}` (the AND mask of a partial product: a replicated bit select), `rp = {4{x[1:0]}}` (a replicated part select with a literal count as a whole right-hand side), `cl = {x[0], {4{2'b10}}, x[3:2]}` (a replicated sized literal between two accesses), `rb = {N{b[0]}}` (a replicated bit as a whole right-hand side, N bits). An x/z bit of the replicated operand is replicated with it; the AND mask of an x bit is x where `a` is 1 and 0 where `a` is 0.
module wl_repl #(parameter int N = 4, parameter int K = 3) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  input  logic [7:0] x,
  output logic [N+K-1:0] pad,
  output logic [N-1:0][N-1:0] pp,
  output logic [7:0] rp,
  output logic [10:0] cl,
  output logic [N-1:0] rb
);
  assign pad = { {K{1'b0}}, a };
  for (genvar i = 0; i < N; i++) begin : g
    assign pp[i] = a & {N{b[i]}};
  end
  assign rp = {4{x[1:0]}};
  assign cl = {x[0], {4{2'b10}}, x[3:2]};
  assign rb = {N{b[0]}};
endmodule
