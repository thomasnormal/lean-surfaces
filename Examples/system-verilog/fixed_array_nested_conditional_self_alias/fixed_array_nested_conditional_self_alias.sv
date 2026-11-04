/*
:name: fixed_array_nested_conditional_self_alias
:description: §7.4 — conditional nested fixed-array assignment with a self-alias branch
:tags: 7.4, 11.4
:type: simulation
*/
module top;
  logic [7:0] source [0:1][0:1];
  logic [7:0] value [4:5][9:8];
  logic choose;

  initial begin
    source[0][0] = 8'h11;
    source[0][1] = 8'h22;
    source[1][0] = 8'h33;
    source[1][1] = 8'h44;
    value[4][9] = 8'haa;
    value[4][8] = 8'hbb;
    value[5][9] = 8'hcc;
    value[5][8] = 8'hdd;
    choose = 0;
    value = choose ? value : source;
    choose = 1;
    value = choose ? value : source;
    if (value[4][9] == 8'h11 && value[4][8] == 8'h22 &&
        value[5][9] == 8'h33 && value[5][8] == 8'h44)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
