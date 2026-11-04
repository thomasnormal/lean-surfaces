module child;
  int value = 5;
endmodule
module top;
  child instance_value();
  initial begin $display("instance %0d", instance_value.value); $finish; end
endmodule
