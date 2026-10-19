/*
:name: unpacked_init_patterns
:description: §7.4 — structured and replicated fixed-unpacked initializers
:tags: 7.4
:type: simulation
*/
module top;
  logic [7:0] defaulted [0:1] = '{default: 8'h12};
  logic [7:0] repeated [0:1] = '{2{8'h34}};
  initial begin
    if (defaulted[0] === 8'h12 && defaulted[1] === 8'h12 &&
        repeated[0] === 8'h34 && repeated[1] === 8'h34)
      $display("PASS");
    else
      $display("FAIL %h %h %h %h", defaulted[0], defaulted[1],
               repeated[0], repeated[1]);
    $finish;
  end
endmodule
