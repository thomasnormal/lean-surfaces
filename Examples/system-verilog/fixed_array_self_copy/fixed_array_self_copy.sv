// An exact blocking self-copy has no observable storage effect.
module top;
  int values [0:1] = '{3, 7};
  initial begin
    values = values;
    $display("selfcopy %0d %0d", values[0], values[1]);
    $finish;
  end
  // expected self-check line: selfcopy 3 7
endmodule
