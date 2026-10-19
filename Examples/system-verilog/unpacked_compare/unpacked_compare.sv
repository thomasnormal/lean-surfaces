/*
:name: unpacked_compare
:description: §11.4 — equal-length fixed-unpacked arrays compare cellwise
:tags: 11.4
:type: simulation
*/
module top;
  logic [7:0] a [0:3];
  logic [7:0] b [0:3];
  initial begin
    a[0] = 8'h12;
    a[1] = 8'h34;
    a[2] = 8'h56;
    a[3] = 8'h78;
    b[0] = 8'h12;
    b[1] = 8'h34;
    b[2] = 8'h56;
    b[3] = 8'h78;
    if (a == b && a[0:1] != b[2:3])
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
