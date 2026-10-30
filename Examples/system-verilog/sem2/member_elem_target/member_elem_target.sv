// Continuous drivers on byte and halfword elements of a packed union member:
// each element select is an 8- or 16-bit write window, not a bit.
module member_elem_target (
    input  logic [7:0]  a_i,
    input  logic [7:0]  b_i,
    input  logic [15:0] c_i,
    output logic [15:0] w_o,
    output logic [31:0] v_o
);
  typedef union packed {
    logic [15:0]     w;
    logic [1:0][7:0] b;
  } half_u;
  typedef union packed {
    logic [31:0]      w;
    logic [1:0][15:0] h;
  } word_u;
  half_u q;
  word_u r;

  assign q.b[1] = a_i;
  assign q.b[0] = b_i;
  assign w_o = q.w;
  assign r.h[1] = c_i;
  assign r.h[0] = {b_i, a_i};
  assign v_o = r.w;
endmodule
