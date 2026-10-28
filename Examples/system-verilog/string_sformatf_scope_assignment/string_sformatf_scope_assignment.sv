/* A metadata-only %m query can feed a pure top-level string assignment. */
module top;
  string scope_name;

  initial begin
    scope_name = $sformatf("%m");
    if (scope_name == "top")
      $display("PASS");
    else
      $display("FAIL: scope=%s", scope_name);
    $finish;
  end
endmodule
