// REFUSED by the clock discipline (`Clock:data-read`, WP-Q0): the child
// register is clocked by the parent's input port through a bare connection
// (allowed), but the child ALSO reads its clock port as data (`ck & d`), which
// after flattening is a read of a continuous copy of the parent's clock.
module clk_cd_reg (
  input  logic ck, d,
  output logic q, y
);
  always_ff @(posedge ck) q <= d;
  assign y = ck & d;
endmodule

module clk_child_data (
  input  logic clk, d,
  output logic q, y
);
  clk_cd_reg u (.ck(clk), .d(d), .q(q), .y(y));
endmodule
