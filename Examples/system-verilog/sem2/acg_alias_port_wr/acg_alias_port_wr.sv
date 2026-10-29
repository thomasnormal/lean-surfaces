// ADMITTED by the always_comb alias guard (LeanModels/Sv/CombAlias2.lean): a
// child whose input port `i` and output port `o` are connected to the SAME
// parent variable `w` (a port loop), with the block WRITING `o` first and
// only then reading `i`. Every tool agrees (y = a). Compare `acg_alias_port`,
// the same child with the two statements swapped (refused).
module acg_alias_port_wr_leaf (
  input  logic [1:0] i, a,
  output logic [1:0] o, y
);
  always_comb begin
    o = a;
    y = i;
  end
endmodule

module acg_alias_port_wr (
  input  logic [1:0] a,
  output logic [1:0] y
);
  logic [1:0] w;
  acg_alias_port_wr_leaf u (.i(w), .a(a), .o(w), .y(y));
endmodule
