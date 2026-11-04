/* Empty output arguments render as literal spaces between default values. */
// Expected output lines are pinned by the differential row below.
// start msg1 end
//           5           2           3
// PASS
module top;
  initial begin
    $display("start", " msg1", , "end");
    $display(5, , 2, , 3);
    $display("PASS");
    $finish;
  end
endmodule
