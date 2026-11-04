// WP-B2 gate 4c: a replication in a leaf of an `always_comb` tree is refused (the procedural chain does not carry the
// scope of a constant of the instance, nor the non-negativity of a count); the same replication in an `assign` is read.
module neg_repl_leaf (
  input  logic [3:0] a,
  input  logic       s,
  output logic [7:0] y
);
  always_comb begin
    if (s) y = {8{a[0]}};
    else   y = 8'h00;
  end
endmodule
