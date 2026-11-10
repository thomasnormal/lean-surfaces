// IEEE 1800-2023 §§11.5.1, 11.8.1: the base retains unsigned type.
module unsigned_part_base (
  input logic [7:0] v,
  input logic [3:0] s,
  input logic [31:0] bu,
  output logic [3:0] by_sub, by_base
);
  assign by_sub = v[s - 2 +: 4];
  assign by_base = v[bu +: 4];
endmodule
