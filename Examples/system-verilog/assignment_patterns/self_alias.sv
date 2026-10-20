module top;
  int values [0:1] = '{3, 7};
  initial begin
    values = '{values[1], values[0]};
    $display("self %0d %0d", values[0], values[1]);
    $finish;
  end
endmodule
