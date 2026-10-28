/*
:name: assoc_exists_sized_comparison
:description: IEEE 1800-2023 §7.9.3 - exists() presence bits are context-sized in equality expressions.
:tags: 7.9.3 associative array exists equality sizing
:type: simulation
*/
module top;
  initial begin
    int values[int];
    int named[string];
    values[5] = 100;
    named["answer"] = 42;
    if (values.exists(5) == 1 && values.exists(99) == 0 &&
        named.exists("answer") === 1 && named.exists("missing") === 0)
      $display("PASS");
    else
      $display("FAIL: context-sized exists result");
    $finish;
  end
endmodule
