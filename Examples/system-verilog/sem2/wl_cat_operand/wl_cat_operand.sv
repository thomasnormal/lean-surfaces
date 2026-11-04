// WP-B2 pin P4: concatenations as operands of `+` and `-` (sized zero padding, mixed add/sub chain), shapes of tasks/fdiv16/reference/fdiv16.sv lines 111 and 132.
module wl_cat_operand (
  input  logic [4:0] xa,
  input  logic [3:0] lzb,
  input  logic adj,
  input  logic [4:0] ef,
  input  logic [9:0] q,
  input  logic inc,
  output logic [6:0] eoff,
  output logic [14:0] mag
);
  assign eoff = {2'b0, xa} + {3'b0, lzb} + 7'd47 - {6'b0, adj};
  assign mag = {ef, q} + {14'd0, inc};
endmodule
