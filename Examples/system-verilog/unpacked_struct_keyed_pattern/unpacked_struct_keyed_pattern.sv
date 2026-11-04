/*
:name: unpacked_struct_keyed_pattern
:description: IEEE 1800-2023 Section 10.9.2 -- keyed assignment patterns
  write flattened integral unpacked-struct fields in declaration order.
:tags: 10.9.2
:type: simulation
*/
typedef struct {
  logic [7:0] r;
  bit [7:0] g;
  logic [7:0] b;
} rgb_t;

module top;
  rgb_t color;
  initial begin
    color = '{b:8'h00, r:8'hFF, g:8'h80};
    if (color.r == 8'hFF && color.g == 8'h80 && color.b == 8'h00)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
