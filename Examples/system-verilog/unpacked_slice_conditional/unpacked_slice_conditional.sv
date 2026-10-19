/*
:name: unpacked_slice_conditional
:description: §10.4 — conditional fixed-array slices lower cellwise
:tags: 10.4
:type: simulation
*/
module top;
  logic [7:0] a [0:3];
  logic [7:0] b [0:3];
  logic [7:0] value [0:3];
  logic choose;
  initial begin
    a[2] = 8'h12;
    a[3] = 8'h34;
    b[0] = 8'h56;
    b[1] = 8'h78;
    choose = 1'b1;
    value[1:2] = choose ? a[2:3] : b[0:1];
    if (value[1] === 8'h12 && value[2] === 8'h34)
      $display("PASS");
    else
      $display("FAIL %h %h", value[1], value[2]);
    $finish;
  end
endmodule
