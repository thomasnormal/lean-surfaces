// Packed aggregate members in fixed-array cells reuse vector windows.
module packed_aggregate_array_member (
    output logic [1:0] struct_out,
    output logic [3:0] union_out
);
  typedef struct packed { logic [1:0] hi; logic [1:0] lo; } S;
  typedef union packed { logic [3:0] a; logic [3:0] b; } U;
  S sa [0:1];
  U ua [0:1];

  assign sa[0].lo = 2'b01;
  assign struct_out = sa[0].lo;
  assign ua[0].a = 4'b1010;
  assign union_out = ua[0].b;
endmodule
