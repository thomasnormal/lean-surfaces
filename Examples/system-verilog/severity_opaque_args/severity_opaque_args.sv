/*
:name: severity_opaque_args
:description: IEEE 1800-2023 Section 20.10 -- quiet severity tasks may
  evaluate source-pure real and time arguments even though their diagnostic
  stream is outside the self-check observable output.
:tags: 20.10
:type: simulation
*/
module top;
  initial begin
    real r = 3.14;
    int x = 42;
    $info("Integer: %0d, Real: %f, String: %s", x, r, "hello");
    $warning("Value %0d is at time %0t", x, $time);
    $error("Realtime %f", $realtime);
    $display("PASS");
    $finish;
  end
endmodule
