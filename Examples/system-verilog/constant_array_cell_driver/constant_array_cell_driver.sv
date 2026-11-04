/* A literal continuous assignment to each fixed-unpacked variable cell is a
 * time-zero write in the self-check surface. */
module top;
  logic [3:0] cells [0:1];
  assign cells[0] = 4'hA;
  assign cells[1] = 4'h5;
  initial begin
    if (cells[0] === 4'hA && cells[1] === 4'h5)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
