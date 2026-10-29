/* Equal-width untagged unions flatten to one aliased cell per array element. */
module top;
  typedef union { bit [7:0] a; bit [7:0] b; } u_t;
  u_t values [1:0];

  initial begin
    values[0].a = 8'hA5;
    if (values[0].b !== 8'hA5) $finish;
    values[1].b = 8'h3C;
    if (values[1].a !== 8'h3C) $finish;
    $display("PASS");
    $finish;
  end
endmodule
