module top;
  typedef union {
    logic [7:0] a;
    logic [7:0] b;
  } bytes_t;
  bytes_t left;
  bytes_t right;

  initial begin
    left.a = 8'hA5;
    right.b = 8'hA5;
    if (left === right) $display("PASS");
    else $display("FAIL");
    $finish;
  end
endmodule
