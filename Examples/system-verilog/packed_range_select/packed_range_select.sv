/*
:name: packed_range_select
:description: §7.4.1 — constant bit selects map ascending packed labels
:tags: 7.4.1
:type: simulation
*/
module top;
  logic [0:7] value;
  initial begin
    value[2] = 1'b1;
    if (value[2] === 1'b1) $display("PASS");
    else $display("FAIL");
    $finish;
  end
endmodule
