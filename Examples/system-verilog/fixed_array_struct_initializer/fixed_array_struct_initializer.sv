/* Complete positional patterns flatten fixed unpacked struct-array cells. */
module top;
  typedef struct { int a; int b; } record_t;
  record_t values[1:0] = '{'{0, 0}, '{1, 1}};

  initial begin
    if (values[1].a != 0 || values[1].b != 0) $finish;
    if (values[0].a != 1 || values[0].b != 1) $finish;
    $display("PASS");
    $finish;
  end
endmodule
