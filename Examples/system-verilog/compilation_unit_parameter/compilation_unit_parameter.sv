/* Compilation-unit parameters are elaboration metadata, not runtime cells. */
// Expected transcript includes: 8, a5, PASS.
parameter int WIDTH = 8;

module top;
  logic [WIDTH-1:0] value = 8'hA5;

  initial begin
    $display("%0d", WIDTH);
    $display("%0h", value);
    $display("PASS");
    $finish;
  end
endmodule
