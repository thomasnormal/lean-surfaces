// WP-B2 gate 4c: a replication in a SELF-determined position (the operand of a reduction) keeps the v1 fragment.
module neg_repl_selfdet (
  input  logic [3:0] a,
  output logic y
);
  assign y = |{4{a[0]}};
endmodule
