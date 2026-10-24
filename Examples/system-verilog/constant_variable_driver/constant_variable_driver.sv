/* Pure literal continuous drivers on packed variables are time-zero writes. */
module top;
  logic [3:0] whole;
  logic [3:0] window;
  assign whole = 4'hA;
  assign window[2:1] = 2'b01;
  initial begin
    if (whole === 4'hA && window[2:1] === 2'b01 && window[0] === 1'bx)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
