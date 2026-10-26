/* Discarded fixed-array locator queries have no represented result. */
module top;
  logic [7:0] values [2];
  initial begin
    values.min();
    values.max();
    values.unique();
    values.unique_index();
    $display("PASS");
    $finish;
  end
endmodule
