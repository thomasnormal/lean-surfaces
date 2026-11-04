/* A constant multidimensional row copies into a flat fixed array. */
module top;
  logic [3:0] source [0:1][0:2];
  logic [3:0] row [7:5];

  initial begin
    source = '{'{4'h1, 4'h2, 4'h3}, '{4'h4, 4'h5, 4'h6}};
    row = source[1];
    if (row[7] === 4'h4 && row[6] === 4'h5 && row[5] === 4'h6)
      $display("PASS");
    else
      $display("FAIL %h %h %h", row[7], row[6], row[5]);
    $finish;
  end
endmodule
