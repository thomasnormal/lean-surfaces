// Constant parts on noncanonical packed ranges normalize to LVec offsets.
module noncanonical_part_assign (
    input  logic [10:3] source,
    output logic [10:3] value
);
  assign value[6:3] = source[10:7];
  assign value[10:7] = source[6:3];
endmodule
