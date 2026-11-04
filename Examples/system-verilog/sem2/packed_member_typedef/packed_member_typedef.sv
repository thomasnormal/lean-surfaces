// A packed-struct typedef is compile-time metadata for the vector window tier.
module packed_member_typedef (
    input  logic [3:0] source,
    output logic [7:0] out
);
  typedef struct packed {
    logic [3:0] hi;
    logic [3:0] lo;
  } pair_t;
  pair_t value;

  assign value.lo = source;
  assign value.hi = 4'ha;
  assign out = value;
endmodule
