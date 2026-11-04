module dimension_queries;
  logic [7:0] vector;
  int integer_value;
  logic scalar;

  initial begin
    typedef logic [2:4][9:6] packed_t;
    typedef int array_t [4:1][0:2];
    typedef logic single_t [3:3];
    typedef logic [-2:1] negative_t;
    typedef packed_t mixed_t [1:2];
    typedef struct packed {logic [2:0] first; bit second;} packet_t;
    typedef union packed {logic [3:0] word; bit [3:0] other;} union_t;
    typedef enum logic [4:0] {LOW = 5'd3, HIGH = 5'd4} state_t;
    typedef enum bit {OFF = 0, ON = 1} scalar_state_t;
    if ($size(vector) == 8 && $high(vector) == 7 &&
        $left(vector) == 7 && $right(vector) == 0 && $low(vector) == 0 &&
        $increment(vector) == 1 &&
        $size(integer_value) == 32 && $high(integer_value) == 31 &&
        $left(integer_value) == 31 && $right(integer_value) == 0 &&
        $low(integer_value) == 0 && $increment(integer_value) == 1 &&
        $dimensions(integer_value) == 1 &&
        $unpacked_dimensions(integer_value) == 0 &&
        $dimensions(scalar) == 0 && $unpacked_dimensions(scalar) == 0 &&
        $size(vector, 1 + 0) == 8 && $high(vector, 1) == 7 &&
        $left(vector, 1) == 7 && $right(vector, 1) == 0 &&
        $low(vector, 1) == 0 && $increment(vector, 1) == 1 &&
        $dimensions(packed_t) == 2 && $unpacked_dimensions(packed_t) == 0 &&
        $size(packed_t, 1) == 3 && $left(packed_t, 1) == 2 &&
        $right(packed_t, 1) == 4 && $low(packed_t, 1) == 2 &&
        $high(packed_t, 1) == 4 && $increment(packed_t, 1) == -1 &&
        $size(packed_t, 2) == 4 && $increment(packed_t, 2) == 1 &&
        $dimensions(array_t) == 3 && $unpacked_dimensions(array_t) == 2 &&
        $size(array_t, 1) == 4 && $increment(array_t, 1) == 1 &&
        $size(array_t, 2) == 3 && $increment(array_t, 2) == -1 &&
        $size(array_t, 3) == 32 && $left(array_t, 3) == 31 &&
        $dimensions(single_t) == 1 && $unpacked_dimensions(single_t) == 1 &&
        $size(single_t) == 1 && $increment(single_t) == 1 &&
        $left(negative_t) == -2 && $right(negative_t) == 1 &&
        $size(negative_t) == 4 && $increment(negative_t) == -1 &&
        $dimensions(mixed_t) == 3 && $unpacked_dimensions(mixed_t) == 1 &&
        $left(mixed_t, 1) == 1 && $right(mixed_t, 1) == 2 &&
        $left(mixed_t, 2) == 2 && $right(mixed_t, 2) == 4 &&
        $size(mixed_t, 3) == 4 && $increment(mixed_t, 3) == 1 &&
        $dimensions(packet_t) == 1 && $size(packet_t) == 4 &&
        $dimensions(union_t) == 1 && $size(union_t) == 4 &&
        $dimensions(state_t) == 1 && $size(state_t) == 5 &&
        $dimensions(scalar_state_t) == 1)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
// REFERENCE: daa07efa82ae4db3bafe9b94 24.03-s004 2026-10-19T08:19:37Z | tests=dimension-queries | source=Examples/system-verilog/dimension_queries/dimension_queries.sv@sha256:aee85cde868b303ddf6d6ef21cd87a03aa679ea8df95dc937b92ff8ae7ca7912 | top=dimension_queries | args=[] | map=dimension_queries.sv#initial
