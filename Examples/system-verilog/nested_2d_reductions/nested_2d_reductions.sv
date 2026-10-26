/* Finite 2-D reductions consume each row with a pure inner reduction. */
module top;
  logic [7:0] matrix[2][2] = '{'{5, 10}, '{15, 20}};
  logic [7:0] rows_total;
  logic [7:0] explicit_total;
  initial begin
    rows_total = matrix.sum with (item.sum);
    explicit_total = matrix.sum with (item.sum with (item));
    if (rows_total === 8'd50 && explicit_total === 8'd50)
      $display("PASS");
    else
      $display("FAIL %0d %0d", rows_total, explicit_total);
    $finish;
  end
endmodule
