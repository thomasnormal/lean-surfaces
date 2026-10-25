module top;
  typedef union {
    logic [7:0] a;
    logic [7:0] b;
  } bytes_t;
  bytes_t left;
  bytes_t right;
  bytes_t out;
  bit choose;

  initial begin
    left.a = 8'hA5;
    right.b = 8'h3C;
    choose = 1'b1;
    out = choose ? left : right;
    if (out === left) $display("PASS");
    else $display("FAIL");
    $finish;
  end
endmodule
