// Clean-room F1 witness for a qualified signal in an SVA property.
module sva_scoped_leaf (
  input logic a,
  output logic flag
);
  assign flag = a;
endmodule

module sva_scoped (
  input logic clk,
  input logic a,
  output logic q
);
  sva_scoped_leaf u (.a(a), .flag(q));
  assert property (@(posedge clk) u.flag == a);
endmodule
