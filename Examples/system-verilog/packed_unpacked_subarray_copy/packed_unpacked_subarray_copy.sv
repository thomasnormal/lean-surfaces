/*
:name: packed_unpacked_subarray_copy
:description: IEEE 1800-2023 7.4.4 — packed slices inside selected unpacked elements copy constant windows
:tags: 7.4.4
:type: simulation
*/
module top;
  bit [3:0][7:0] joe [0:9];
  initial begin
    joe[6] = 32'hAABBCCDD;
    joe[7] = 32'h00000000;
    joe[7][3:2] = joe[6][1:0];
    if (joe[7][3] == 8'hCC && joe[7][2] == 8'hDD &&
        joe[7][1] == 8'h00 && joe[7][0] == 8'h00)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
