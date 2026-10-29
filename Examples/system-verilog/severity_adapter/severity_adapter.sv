/* Severity diagnostics and fatal termination use the represented adapter state. */
// PASS
module top;
  logic [3:0] x;
  initial begin
    x = 4'd3;
    $info("x=%0d", x);
    $warning("warning");
    $error("error");
    $display("PASS");
    $fatal(1, "done=%0d", x);
    $display("FAIL");
  end
endmodule
