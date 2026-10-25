module top;
  typedef union {
    logic [7:0] a;
    logic [7:0] b;
  } bytes_t;
  bytes_t value;

  initial begin
    value.a = 8'hA5;
    value.b += 1;
    if (value.a === 8'hA6) $display("PASS");
    else $display("FAIL");
    $finish;
  end
endmodule
