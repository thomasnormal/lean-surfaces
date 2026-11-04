/*
:name: assoc_count_history
:description: IEEE 1800-2023 §7.9.1 finite literal associative-array num and size
:tags: 7.9.1 associative array
:type: simulation
*/
module top;
  int values[string];
  initial begin
    if (values.num() !== 0 || values.size() !== 0) begin $display("FAIL"); $finish; end
    values["red"] = 1;
    values["blue"] = 2;
    values["red"] = 3;
    if (values.num() == 2 && values.size() == 2)
      $display("PASS");
    else
      $display("FAIL: num=%0d size=%0d", values.num(), values.size());
    $finish;
  end
endmodule
