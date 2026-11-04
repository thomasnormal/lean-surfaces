/*
:name: severity_dynamic
:description: IEEE 1800-2023 Section 20.10 -- severity tasks evaluate
  display-style integral arguments while their diagnostic stream is outside
  the self-check observable output.
:tags: 20.10
:type: simulation
*/
module top;
  int x;
  initial begin
    x = 42;
    $warning("x=%0d str=%s", x, "hello");
    $info("h=%h", x);
    $error("x=%0d", x);
    $display("PASS");
    $finish;
  end
endmodule
