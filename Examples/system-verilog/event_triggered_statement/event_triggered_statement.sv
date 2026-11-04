/* Discarded triggered queries are false before any event trigger. */
module top;
  event a;
  event b;
  initial begin
    a.triggered();
    b.triggered();
    $display("PASS");
    $finish;
  end
endmodule
