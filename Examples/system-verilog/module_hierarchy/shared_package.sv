package shared_values;
  int counter=0;
endpackage
module leaf;
  import shared_values::*;
  initial counter++;
endmodule
module top;
  import shared_values::*;
  leaf a(),b(),c();
  initial begin #1;$display("shared %0d",counter);$finish;end
endmodule
