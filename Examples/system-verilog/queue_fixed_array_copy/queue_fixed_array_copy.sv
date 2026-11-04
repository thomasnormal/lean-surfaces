/* A scalar literal queue copies to a same-count fixed array left to right. */
module top;
  int fixed_arr [3];
  int q[$] = '{10, 20, 30};

  initial begin
    fixed_arr = q;
    if (fixed_arr[0] == 10 && fixed_arr[1] == 20 && fixed_arr[2] == 30)
      $display("PASS");
    else
      $display("FAIL: %0d %0d %0d", fixed_arr[0], fixed_arr[1], fixed_arr[2]);
  end
endmodule
