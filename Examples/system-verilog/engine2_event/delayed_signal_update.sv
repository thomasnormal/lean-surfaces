module delayed_signal_update;
  timeunit 1ns;
  timeprecision 1ns;

  logic value = 0;

  initial begin
    #1;
    value = 1;
    $display("updated %0d %0d", value, $time);
  end
endmodule
