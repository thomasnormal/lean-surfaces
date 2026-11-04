module top;
  logic [7:0] value;
  initial begin
    value = 'x;
    $display("unknown %0d", $clog2(value));
    $finish;
  end
endmodule
