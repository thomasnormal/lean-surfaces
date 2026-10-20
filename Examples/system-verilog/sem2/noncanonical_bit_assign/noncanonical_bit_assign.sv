// Constant bits on noncanonical packed ranges normalize to LVec offsets.
module noncanonical_bit_assign (
    input  logic [10:3] source,
    output logic [10:3] value
);
  assign value[3] = source[10];
  assign value[10] = source[3];
endmodule
