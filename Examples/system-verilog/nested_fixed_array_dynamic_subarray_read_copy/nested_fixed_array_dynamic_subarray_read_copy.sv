/* A dynamic multidimensional subarray read copies a row into a flat array. */
module top;
  logic [3:0] matrix [0:1][0:2];
  logic [3:0] row [5:3];
  logic index;

  initial begin
    matrix = '{'{4'h1, 4'h2, 4'h3}, '{4'h4, 4'h5, 4'h6}};
    index = 1'b1;
    row = matrix[index];
    if (row[5] === 4'h4 && row[4] === 4'h5 && row[3] === 4'h6)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
