module tick_delays;
  timeunit 1ns;
  timeprecision 1ns;

  initial begin
    $display("start %0d", $time);
    #2;
    $display("first %0d", $time);
    #3;
    $display("second %0d", $time);
  end
endmodule
