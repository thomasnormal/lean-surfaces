module zero_delay_slot;
  timeunit 1ns;
  timeprecision 1ns;

  initial begin
    #2;
    $display("before_zero %0d", $time);
    #0;
    $display("after_zero %0d", $time);
    #1;
    $display("later %0d", $time);
  end
endmodule
