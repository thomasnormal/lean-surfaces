/* A resolved forward typedef is compile-time metadata in the legacy tier. */
typedef int word_t;
typedef word_t;

module top;
  word_t value = 42;

  initial begin
    $display("%0d", value);
    $display("PASS");
    $finish;
  end
endmodule
