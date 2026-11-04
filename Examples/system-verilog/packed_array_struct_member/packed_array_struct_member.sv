/*
:name: packed_array_struct_member
:description: §7.4.1 — constant members of packed-array packed-struct elements share one vector
:tags: 7.4.1 packed-array packed-struct selected-write
:type: simulation
*/
module top;
  typedef struct packed {
    logic [3:0] hi;
    logic [3:0] lo;
  } byte_t;

  byte_t [3:0] arr;

  initial begin
    arr[0].hi = 4'hA;
    arr[0].lo = 4'hB;
    arr[3].hi = 4'hC;
    arr[3].lo = 4'hD;
    if (arr[0] === 8'hAB && arr[3] === 8'hCD)
      $display("PASS");
    else
      $display("FAIL: arr[0]=%0h arr[3]=%0h", arr[0], arr[3]);
    $finish;
  end
endmodule
