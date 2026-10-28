/*
:name: string_sformatf_multiple_integral_assignment
:description: §21.3.3 — multiple literal integral $sformatf conversions assign to strings
:tags: 21.3.3
:type: simulation
*/
module top;
  string chars, mixed;
  initial begin
    chars = $sformatf("%c%c", 8'h41, 8'h5A);
    mixed = $sformatf("v=%0d h=%0H", 7, 8'hAB);
    if (chars == "AZ" && mixed == "v=7 h=ab") $display("PASS");
    else $display("FAIL");
    $finish;
  end
endmodule
