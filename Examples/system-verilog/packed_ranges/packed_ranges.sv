/*
:name: packed_ranges
:description: §7.4.1 — whole-vector operations retain an ascending packed range
:tags: 7.4.1
:type: simulation
*/
module top;
  logic [0:7] value;
  initial begin
    value = 8'hA5;
    if (value === 8'hA5) $display("PASS");
    else $display("FAIL %h", value);
    $finish;
  end
endmodule
