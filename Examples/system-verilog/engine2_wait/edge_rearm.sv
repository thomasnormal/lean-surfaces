module edge_rearm;
  timeunit 1ns;
  timeprecision 1ns;

  logic pulse = 0;
  integer resumes = 0;

  initial begin
    @(posedge pulse);
    resumes = resumes + 1;
    @(posedge pulse);
    resumes = resumes + 1;
    $display("edge occurrences %0d at %0d", resumes, $time);
  end

  initial begin
    #1;
    pulse = 1;
    #1;
    pulse = 0;
    #1;
    pulse = 1;
  end
endmodule
