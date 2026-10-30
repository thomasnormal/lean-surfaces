// Member element selects over non-zero-based descending and ascending ranges,
// a three-dimensional member, and a union member nested in a struct: each label
// counts ELEMENTS of the array it selects from.
module member_elem_shapes (
    input  logic [63:0] a_i,
    output logic [3:0]  n5_o,
    output logic [7:0]  n65_o,
    output logic [3:0]  r4_o,
    output logic [3:0]  r7_o,
    output logic [3:0]  m10_o,
    output logic [7:0]  m1_o,
    output logic [1:0]  m102_o,
    output logic [7:0]  ub1_o,
    output logic [3:0]  ubn_o
);
  typedef union packed {
    logic [15:0]     w;
    logic [1:0][7:0] b;
  } u_t;
  typedef struct packed {
    logic [7:4][3:0]       n;
    logic [4:7][3:0]       r;
    logic [1:0][1:0][3:0]  m;
    u_t                    u;
  } s_t;
  s_t s;

  assign s = a_i;
  assign n5_o = s.n[5];
  assign n65_o = s.n[6:5];
  assign r4_o = s.r[4];
  assign r7_o = s.r[7];
  assign m10_o = s.m[1][0];
  assign m1_o = s.m[1];
  assign m102_o = s.m[1][0][2:1];
  assign ub1_o = s.u.b[1];
  assign ubn_o = s.u.b[0][7:4];
endmodule
