module top;
  int value;
  initial begin
    value = 8;
    $display("effects %0d %0d", $clog2(value++), value);
    $finish;
  end
endmodule
