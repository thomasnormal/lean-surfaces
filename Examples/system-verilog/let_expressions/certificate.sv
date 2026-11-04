module top;
 logic [3:0] held, actual, result;
 let plus(a)=held+a;
 initial begin : invocation
  logic [3:0] held;
  held=4'd7; top.held=4'd14; actual=4'd3; result=plus(actual);
  $display("certificate %0d",result);
  $finish;
 end
endmodule
