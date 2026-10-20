module top;
  logic[7:0] unknown_value;
  int value;
  initial begin
    unknown_value='x;
    value=($clog2(unknown_value):7:$clog2(unknown_value));
    $display("unselected-math %0d",value);
    $finish;
  end
endmodule
