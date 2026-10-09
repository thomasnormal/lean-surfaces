module multi_signal_once;
  timeunit 1ns;
  timeprecision 1ns;

  logic first = 0;
  logic second = 1;
  integer resumes = 0;

  initial begin
    @(posedge first or negedge second);
    resumes = resumes + 1;
    #1;
    $display("resumes %0d at %0d", resumes, $time);
  end

  initial begin
    #1;
    first = 1;
    second = 0;
  end
endmodule
