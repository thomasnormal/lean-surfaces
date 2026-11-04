/*
:name: packed_range_part_select
:description: §7.4.1 — constant part selects map ascending packed labels
:tags: 7.4.1
:type: simulation
*/
module top;
  logic [0:7] value;
  initial begin
    value[1:4] = 4'b1010;
    if (value[1:4] === 4'b1010) $display("PASS");
    else $display("FAIL");
    $finish;
  end
endmodule
