/*
:name: packed_union_reshaped_member
:description: §7.3.1 — constant nested selections of a packed-union view alias its raw vector
:tags: 7.3.1 packed-union packed-array selected-write
:type: simulation
*/
module top;
  union packed {
    logic [7:0] raw;
    logic [0:1][3:0] lanes;
  } value;

  initial begin
    value.raw = 8'h00;
    value.lanes[0][2:1] = 2'bz1;
    if (value.raw === 8'b0z10_0000)
      $display("PASS");
    else
      $display("FAIL: raw=%b", value.raw);
    $finish;
  end
endmodule
