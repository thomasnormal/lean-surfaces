/* A procedural event declaration is metadata for a pure $typename query. */
module top;
  initial begin
    event named_ev;
    string text;
    text = $typename(named_ev);
    if (text == "event")
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
