module resume_after_update;
  timeunit 1ns;
  timeprecision 1ns;

  logic value = 0;

  initial begin
    @(posedge value);
    $display("resumed %0d", $time);
  end

  initial begin
    #1;
    value = 1;
  end
endmodule
