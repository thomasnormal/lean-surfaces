/* A post-incremented fixed-array index is sampled before the write. */
module top;
  int order[2];
  int idx;
  initial begin
    order[idx++] = 1;
    order[idx++] = 2;
    if (order[0] == 1 && order[1] == 2 && idx == 2)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
