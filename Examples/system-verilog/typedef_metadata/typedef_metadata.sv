/* Compile-time typedefs are metadata in the legacy self-check tier. */
// PASS
module top;
  typedef bit [7:0] byte_t;
  typedef struct { bit [3:0] hi; bit [3:0] lo; } pair_t;
  byte_t b;
  pair_t p;

  initial begin
    $display("PASS");
    $finish;
  end
endmodule
