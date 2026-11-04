module top;
  logic [15:0] source;
  int captured, live;
  initial begin
    source = 9;
    captured = $clog2(source);
    $display("before %0d", captured);
    captured <= $clog2(source);
    source = 256;
    #1;
    live = $clog2(source);
    $display("after %0d %0d", captured, live);
    $finish;
  end
endmodule
