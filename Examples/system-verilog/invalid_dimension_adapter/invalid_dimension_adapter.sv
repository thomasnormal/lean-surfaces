/*
:name: invalid_dimension_adapter
:description: Malformed packed dimensions are declaration-only compile errors.
:tags: 7.4 6.9.1
:type: simulation
*/
module top;
  bit [3:x] bad_range;
  bit [3] bad_single = 1'b0;
  initial begin
    $display("PASS");
    $finish;
  end
endmodule
