/* Exact integral parameters are elaboration metadata, not runtime cells. */
// Expected transcript includes: 8, a, a5, PASS.
module top #(parameter int WIDTH = 8, parameter logic [3:0] MASK = 4'ha);
  logic [WIDTH-1:0] value = 8'hA5;

  initial begin
    $display("%0d", WIDTH);
    $display("%0h", MASK);
    $display("%0h", value);
    $display("PASS");
    $finish;
  end
endmodule
