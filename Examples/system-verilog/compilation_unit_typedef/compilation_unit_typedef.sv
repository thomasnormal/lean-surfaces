/* Compilation-unit typedefs are metadata in the legacy self-check tier. */
// Expected transcript includes: a5, PASS.
typedef logic [7:0] byte_t;

module top;
  byte_t value = 8'hA5;

  initial begin
    $display("%0h", value);
    $display("PASS");
    $finish;
  end
endmodule
