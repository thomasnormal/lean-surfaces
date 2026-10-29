// ADMITTED by the always_comb alias guard (LeanModels/Sv/CombAlias2.lean): the
// alias is inside the instantiated module and the block WRITES `t` before it
// reads the copy `w` (write then read), so the flattened design is admitted.
// Compare `acg_alias_hier`, the same child with the statements swapped
// (refused).
module acg_alias_hier_ok_leaf (
  input  logic [1:0] a,
  output logic [1:0] y
);
  logic [1:0] t, w;
  assign w = t;
  always_comb begin
    t = a;
    y = w;
  end
endmodule

module acg_alias_hier_ok (
  input  logic [1:0] a,
  output logic [1:0] y
);
  acg_alias_hier_ok_leaf u (.a(a), .y(y));
endmodule
