package Source;
  int count = 3;
endpackage
package Relay;
  import Source::count;
  export Source::count;
endpackage
package Other;
  int count = 20;
endpackage
module top;
  import Relay::*;
  int boot = Source::count + 7;
  initial begin
    count = count + 1;
    $display("bound %0d %0d %0d boot %0d", Source::count, Relay::count, Other::count, boot);
    begin
      int count;
      count = 11;
      Source::count = 6;
      $display("shadow %0d %0d", count, Relay::count);
    end
    Other::count = Other::count + 2;
    $display("distinct %0d %0d", Source::count, Other::count);
    $finish;
  end
endmodule
