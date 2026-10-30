// Constant element and range selects through a packed struct member whose type
// is a multi-dimensional packed array: the labels count ELEMENTS (8 bits each),
// so each select is a flat multi-bit window of the struct vector.
module member_elem_struct (
    input  logic [33:0] p_i,
    output logic [7:0]  b2_o,
    output logic [7:0]  b0_o,
    output logic [3:0]  nib_o,
    output logic [15:0] r_o,
    output logic [1:0]  tag_o,
    output logic        top_o
);
  typedef struct packed {
    logic [3:0][7:0] bytes;
    logic [1:0]      tag;
  } pkt_t;
  pkt_t p;

  assign p = p_i;
  assign b2_o = p.bytes[2];
  assign b0_o = p.bytes[0];
  assign nib_o = p.bytes[1][3:0];
  assign r_o = p.bytes[2:1];
  assign tag_o = p.tag;
  assign top_o = p.bytes[3][7];
endmodule
