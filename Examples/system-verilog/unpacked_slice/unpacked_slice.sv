/*
:name: unpacked_slice
:description: §10.2 — simple constant unpacked-array slices accept positional patterns
:tags: 10.2
:type: simulation
*/
module top;
  logic [7:0] value [0:3];
  initial begin
    value[1:2] = '{8'h12, 8'h34};
    if (value[0] === 8'hxx && value[1] === 8'h12 &&
        value[2] === 8'h34 && value[3] === 8'hxx)
      $display("PASS");
    else
      $display("FAIL %h %h %h %h", value[0], value[1], value[2], value[3]);
    $finish;
  end
endmodule
