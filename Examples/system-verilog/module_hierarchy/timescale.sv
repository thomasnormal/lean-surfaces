module leaf;
  timeunit 1ns;timeprecision 1ps;
  initial begin #1;$display("late");end
endmodule
module top;
  timeunit 1ps;timeprecision 1ps;
  leaf child();
  initial begin #2;$display("early");#1000;$finish;end
endmodule
