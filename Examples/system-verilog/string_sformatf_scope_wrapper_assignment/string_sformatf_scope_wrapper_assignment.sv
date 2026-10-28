/* Literal text may surround a metadata-only %m query. */
module top;
  string scope_name;

  initial begin
    scope_name = $sformatf("hier: %m");
    if (scope_name == "hier: top")
      $display("PASS");
    else
      $display("FAIL: scope=%s", scope_name);
    $finish;
  end
endmodule
