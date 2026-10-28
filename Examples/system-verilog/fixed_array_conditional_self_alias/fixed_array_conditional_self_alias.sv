/*
:name: fixed_array_conditional_self_alias
:description: §7.4 — conditional fixed-array assignment with a self-alias branch
:tags: 7.4, 11.4
:type: simulation
*/
module top;
  logic [7:0] source [0:1];
  logic [7:0] value [0:1];
  logic choose;
  initial begin
    source[0] = 8'h11;
    source[1] = 8'h22;
    value[0] = 8'hAA;
    value[1] = 8'hBB;
    choose = 0;
    value = choose ? value : source;
    choose = 1;
    value = choose ? value : source;
    if (value[0] == 8'h11 && value[1] == 8'h22) $display("PASS");
    else $display("FAIL");
    $finish;
  end
endmodule
