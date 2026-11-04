/*
:name: sformatf_zero_width
:description: §21.2.1.2 — literal integral zero-width format conversions use the packed renderer
:tags: 21.2.1.2,21.3.3
:type: simulation
*/
module top;
  // expected self-check output: 1010|a|42|012
  initial begin
    $display("%s|%s|%s|%s",
      $sformatf("%0b", 8'b00001010),
      $sformatf("%0h", 8'h0A),
      $sformatf("%0d", 8'd42),
      $sformatf("%0o", 8'h0A));
    $finish;
  end
endmodule
