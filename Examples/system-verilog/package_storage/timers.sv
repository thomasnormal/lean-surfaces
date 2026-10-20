package Shared;
  int value = 5;
endpackage
module top;
  import Shared::value;
  initial begin
    #2;
    value = 8;
    #2;
    value <= 13;
    #2;
    $display("later %0d", Shared::value);
    $finish;
  end
  initial begin
    #1;
    $display("before %0d", value);
    #2;
    $display("after %0d", Shared::value);
  end
endmodule
