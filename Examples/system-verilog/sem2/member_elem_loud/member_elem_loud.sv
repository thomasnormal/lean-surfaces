// Member element selects the extractor does not lower: a run-time element label
// and an indexed part select over a multi-dimensional packed member. Both stay
// loud (never a one-bit window, the pre-fix lowering).
module member_elem_loud (
    input  logic [33:0] p_i,
    input  logic [1:0]  i_i,
    output logic [7:0]  dyn_o,
    output logic [15:0] ix_o
);
  typedef struct packed {
    logic [3:0][7:0] bytes;
    logic [1:0]      tag;
  } pkt_t;
  pkt_t p;

  assign p = p_i;
  assign dyn_o = p.bytes[i_i];
  assign ix_o = p.bytes[1+:2];
endmodule
