/* Source-pure string statement methods are erased by the legacy adapter. */
// PASS
module top;
  string s = "Test";
  initial begin
    s.putc(2, "B");
    s.itoa(12);
    s.bintoa(10);
    s.octtoa(8);
    s.hextoa(255);
    $display("PASS");
  end
endmodule
