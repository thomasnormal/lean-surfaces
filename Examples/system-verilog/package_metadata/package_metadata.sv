/* A metadata-only package contributes no self-check runtime state. */
// Expected transcript includes: a5, PASS.
package P;
  typedef logic [7:0] byte_t;
endpackage

module top;
  import P::byte_t;
  byte_t value = 8'hA5;

  initial begin
    $display("%0h", value);
    $display("PASS");
    $finish;
  end
endmodule
