/*
:name: timeformat_inert
:description: literal timeformat has no effect without a percent-t consumer
:tags: 20.4.3
:type: simulation
*/
module top;
  initial begin
    $timeformat(-9, 2, " ns", 10);
    $display("PASS");
  end
endmodule
