/* Empty queue and uninitialized dynamic-array delete calls are inert. */
module top;
  int queue_values[$] = {};
  int dynamic_values[];
  initial begin
    queue_values.delete();
    dynamic_values.delete();
    if (queue_values.size() == 0 && dynamic_values.size() == 0)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
