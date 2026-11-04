/* Whole bounded multidimensional fixed-array copies use ordinal cells. */
module top;
  logic [3:0] source [0:1][0:2];
  logic [3:0] target [5:6][9:7];

  initial begin
    source = '{'{4'h1, 4'h2, 4'h3}, '{4'h4, 4'h5, 4'h6}};
    target = source;
    if (target[5][9] === 4'h1 && target[5][7] === 4'h3 &&
        target[6][9] === 4'h4 && target[6][7] === 4'h6)
      $display("PASS");
    else
      $display("FAIL %h %h %h %h", target[5][9], target[5][7],
               target[6][9], target[6][7]);
    $finish;
  end
endmodule
