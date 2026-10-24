/*
:name: streaming_left_slice_target
:description: IEEE 1800-2023 11.4.14.3 -- a named byte slice reverses source chunks into equal-width targets
:tags: 11.4.14 streaming left unpack target slice
:type: simulation
*/
module top;
  bit [31:0] src;
  bit [7:0] a, b, c, d;

  initial begin
    src = 32'h4142_4344;
    {<<byte {a, b, c, d}} = src;
    if (a === 8'h44 && b === 8'h43 && c === 8'h42 && d === 8'h41)
      $display("PASS");
    else
      $display("FAIL %h %h %h %h", a, b, c, d);
    $finish;
  end
endmodule
