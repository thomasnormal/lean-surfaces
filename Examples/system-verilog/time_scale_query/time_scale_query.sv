/*
:name: time_scale_query
:description: IEEE 1800-2023 Section 20.4 -- literal timescale queries
  fold to their signed decimal exponents.
:tags: 20.4
:type: simulation
*/
`timescale 1ns/1ps
module top;
  int unit_code;
  int precision_code;
  initial begin
    unit_code = $timeunit;
    precision_code = $timeprecision;
    if (unit_code == -9 && precision_code == -12)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
