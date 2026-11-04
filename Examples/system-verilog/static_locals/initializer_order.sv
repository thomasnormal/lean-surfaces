module top;
 int snapshot=data.value;
 initial begin : data
  static int value=4;
 end
 initial begin $display("order %0d",snapshot);$finish;end
endmodule
