/* Discarded fixed-array locator queries have no represented result. */
module top;
  logic [7:0] values [2];
  initial begin
    values.min();
    values.max();
    values.unique();
    values.unique_index();
    values.min with (item + 1);
    values.max with (item * 2);
    values.unique with (item + 1);
    values.unique_index with (item + 1);
    $display("PASS");
    $finish;
  end
endmodule
