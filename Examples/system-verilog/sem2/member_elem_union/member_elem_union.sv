// Packed union views of one 32-bit word: byte and halfword element selects
// through multi-dimensional members, read and written (a byte swap), next to
// a one-bit select of the one-dimensional member.
module member_elem_union (
    input  logic [31:0] w_i,
    output logic [31:0] swapped_o,
    output logic [15:0] hi_o,
    output logic [15:0] lo_o,
    output logic [7:0]  b3_o,
    output logic        w5_o
);
  typedef union packed {
    logic [31:0]      w;
    logic [1:0][15:0] h;
    logic [3:0][7:0]  b;
  } word_u;
  word_u in_v, out_v;

  always_comb begin
    in_v.w = w_i;
    out_v.b[0] = in_v.b[3];
    out_v.b[1] = in_v.b[2];
    out_v.b[2] = in_v.b[1];
    out_v.b[3] = in_v.b[0];
  end

  assign swapped_o = out_v.w;
  assign hi_o = in_v.h[1];
  assign lo_o = in_v.h[0];
  assign b3_o = in_v.b[3];
  assign w5_o = in_v.w[5];
endmodule
