/*
:name: streaming_slice_target
:description: IEEE 1800-2023 11.4.14.3 -- an explicit byte slice unpacks a vector into equal-width targets
:tags: 11.4.14 streaming right unpack target slice
:type: simulation
*/
module top;
  bit [31:0] src;
  bit [7:0] a, b, c, d;

  initial begin
    src = 32'hDEAD_BEEF;
    {>>byte {a, b, c, d}} = src;
    if (a === 8'hDE && b === 8'hAD && c === 8'hBE && d === 8'hEF)
      $display("PASS");
    else
      $display("FAIL %h %h %h %h", a, b, c, d);
    $finish;
  end
endmodule
