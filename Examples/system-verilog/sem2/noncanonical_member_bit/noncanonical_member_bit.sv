// Literal bits of noncanonical packed members use declaration-label offsets.
module noncanonical_member_bit (
    input  logic       source,
    output logic [3:0] out
);
  struct packed {
    logic [10:7] hi;
    logic [3:0]  lo;
  } value;

  assign value.hi[10] = source;
  assign out = value.hi;
endmodule
