package Dependent;
  int first = 4;
  int second = first + 1;
endpackage
module top;
  initial begin $display("dependent %0d", Dependent::second); $finish; end
endmodule
