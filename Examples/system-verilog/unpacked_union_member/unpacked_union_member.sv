module top;
  typedef union {
    logic [7:0] a;
    logic [7:0] b;
  } bytes_t;
  bytes_t value;

  initial begin
    value.a = 8'hA5;
    if (value.b === 8'hA5) $display("PASS");
    else $display("FAIL: value.b=%h", value.b);
    $finish;
  end
endmodule
