// Element selects through an ascending-range member (element 0 is the most
// significant), through a member of a nested packed struct, and an indexed
// part select inside a wide element.
module member_elem_nested (
    input  logic [33:0] a_i,
    input  logic [15:0] o_i,
    output logic [7:0]  a0_o,
    output logic [7:0]  a3_o,
    output logic [15:0] a12_o,
    output logic [3:0]  n1_o,
    output logic [3:0]  z_o,
    output logic [1:0]  ix_o
);
  typedef struct packed {
    logic [0:3][7:0] bytes;
    logic [1:0]      tag;
  } asc_t;
  typedef struct packed {
    logic [1:0][3:0] n;
    logic [3:0]      z;
  } inner_t;
  typedef struct packed {
    inner_t     inn;
    logic [3:0] lo;
  } outer_t;
  asc_t   a;
  outer_t o;

  assign a = a_i;
  assign o = o_i;
  assign a0_o = a.bytes[0];
  assign a3_o = a.bytes[3];
  assign a12_o = a.bytes[1:2];
  assign n1_o = o.inn.n[1];
  assign z_o = o.inn.z;
  assign ix_o = a.bytes[1][2+:2];
endmodule
