// WP-B2 gate 4c: a replication of a part select with a LITERAL count, as a whole right-hand side (`{4{x[1:0]}}`), and
// of a sized literal inside a concatenation with an access on either side.
module repl_bits (
  input  logic [7:0] x,
  output logic [7:0] y,
  output logic [10:0] z
);
  assign y = {4{x[1:0]}};
  assign z = {x[0], {4{2'b10}}, x[3:2]};
endmodule
