module top;
  typedef union {
    logic [7:0] a;
    logic [7:0] b;
  } bytes_t;
  bytes_t source;
  bytes_t copy;

  initial begin
    source.a = 8'hA5;
    copy = source;
    if (copy.b === 8'hA5) $display("PASS");
    else $display("FAIL: copy.b=%h", copy.b);
    $finish;
  end
endmodule
