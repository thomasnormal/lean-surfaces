module wait_resume_completion;
  timeunit 1ns;
  timeprecision 1ns;

  reg flag;

  initial begin
    flag = 0;
    $display("waiting %0d", $time);
    @(posedge flag);
    $display("resumed %0d", $time);
  end

  initial begin
    #2;
    flag = 1;
    #3;
    $display("other completed %0d", $time);
  end
endmodule
