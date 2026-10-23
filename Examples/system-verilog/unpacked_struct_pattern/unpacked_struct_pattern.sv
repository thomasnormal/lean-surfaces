/*
:name: unpacked_struct_pattern
:description: IEEE 1800-2023 Section 10.9.2 -- a positional assignment
  pattern writes the fields of an unpacked struct.
:tags: 10.9.2
:type: simulation
*/
typedef struct {
  logic [7:0] r;
  logic [7:0] g;
  logic [7:0] b;
} rgb_t;

module top;
  rgb_t color;
  initial begin
    color = '{8'hFF, 8'h80, 8'h00};
    if (color.r == 8'hFF && color.g == 8'h80 && color.b == 8'h00)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
