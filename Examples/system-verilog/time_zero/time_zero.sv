/*
:name: time_zero
:description: §20.4 — `$time` in the time-zero self-check slice is zero
:tags: 20.4
:type: simulation
*/
module top;
  initial begin
    if ($time === 64'd0) $display("PASS");
    else $display("FAIL %0d", $time);
    $finish;
  end
endmodule
