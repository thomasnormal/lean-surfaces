module top;
  initial begin
    $display("constant %0d %0d", $clog2(8'hxx), $clog2(8'hzz));
    $finish;
  end
endmodule
