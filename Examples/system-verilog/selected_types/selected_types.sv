// Whole packed aggregates use the implicit [7:0] vector view.
module top;
  typedef struct packed { bit [3:0] hi; bit [3:0] lo; } bits_t;
  typedef struct packed { logic [3:0] hi; bit [3:0] lo; } mixed_t;
  typedef union packed { bit [7:0] word; bit [3:0][1:0] pairs; } union_t;
  bit [7:0] vector_value;
  bits_t struct_value;
  mixed_t mixed_value;
  union_t union_value;
  bit signed [7:0] signed_value;
  bit [0:7] ascending;
  int integer_value;
  byte byte_value;
  integer index_value;
  logic [3:0] vector_part, struct_part, mixed_part, union_part;
  logic vector_bit, struct_bit, mixed_bit, union_bit;
  logic [15:0] widened;
  initial begin
    vector_value = 8'hA5;
    struct_value = 8'hA5;
    mixed_value = 8'b10xz0101;
    union_value = 8'hA5;
    signed_value = 8'hA5;
    ascending = 8'hA5;
    integer_value = 32'hA5000000;
    byte_value = 8'hA5;
    index_value = 2;
    vector_part = vector_value[index_value +: 4];
    struct_part = struct_value[index_value +: 4];
    mixed_part = mixed_value[index_value +: 4];
    union_part = union_value[index_value +: 4];
    $display("inside %b %b %b %b", vector_part, struct_part, mixed_part, union_part);
    if ({vector_part, struct_part, mixed_part, union_part} !== 16'b1001_1001_xz01_1001)
      $display("FAIL inside");
    index_value = 6;
    vector_part = vector_value[index_value +: 4];
    struct_part = struct_value[index_value +: 4];
    mixed_part = mixed_value[index_value +: 4];
    union_part = union_value[index_value +: 4];
    $display("partial %b %b %b %b", vector_part, struct_part, mixed_part, union_part);
    if ({vector_part, struct_part, mixed_part, union_part} !== 16'b0010_0010_xx10_0010)
      $display("FAIL partial");
    index_value = -2;
    vector_part = vector_value[index_value +: 4];
    struct_part = struct_value[index_value +: 4];
    mixed_part = mixed_value[index_value +: 4];
    union_part = union_value[index_value +: 4];
    $display("negative %b %b %b %b", vector_part, struct_part, mixed_part, union_part);
    if ({vector_part, struct_part, mixed_part, union_part} !== 16'b0100_0100_01xx_0100)
      $display("FAIL negative");
    index_value = 10;
    vector_bit = vector_value[index_value];
    struct_bit = struct_value[index_value];
    mixed_bit = mixed_value[index_value];
    union_bit = union_value[index_value];
    $display("outside %b %b %b %b", vector_bit, struct_bit, mixed_bit, union_bit);
    if ({vector_bit, struct_bit, mixed_bit, union_bit} !== 4'b00x0)
      $display("FAIL outside");
    index_value = 'x;
    vector_part = vector_value[index_value +: 4];
    struct_part = struct_value[index_value +: 4];
    mixed_part = mixed_value[index_value +: 4];
    union_part = union_value[index_value +: 4];
    $display("unknown %b %b %b %b", vector_part, struct_part, mixed_part, union_part);
    if ({vector_part, struct_part, mixed_part, union_part} !== 16'b0000_0000_xxxx_0000)
      $display("FAIL unknown");
    index_value = 1;
    vector_part = vector_value[index_value -: 4];
    struct_part = struct_value[index_value -: 4];
    mixed_part = mixed_value[index_value -: 4];
    union_part = union_value[index_value -: 4];
    $display("minus %b %b %b %b", vector_part, struct_part, mixed_part, union_part);
    if ({vector_part, struct_part, mixed_part, union_part} !== 16'b0100_0100_01xx_0100)
      $display("FAIL minus");
    vector_part = vector_value[9:6];
    struct_part = struct_value[1:-2];
    mixed_part = mixed_value[9:6];
    union_part = union_value[12:9];
    $display("simple %b %b %b %b", vector_part, struct_part, mixed_part, union_part);
    if ({vector_part, struct_part, mixed_part, union_part} !== 16'b0010_0100_xx10_0000)
      $display("FAIL simple");
    widened = signed_value[7:4];
    $display("integral %h %b %b %b", widened, integer_value[33:30], byte_value[9:6], ascending[0:3]);
    if (widened !== 16'h000a || integer_value[33:30] !== 4'b0010 ||
        byte_value[9:6] !== 4'b0010 || ascending[0:3] !== 4'b1010)
      $display("FAIL integral");
    $display("PASS");
    $finish;
  end
endmodule
