/*
:name: string_sformatf_zero_width_assignment
:description: §21.2.1.2 — zero-width binary and octal formatting assigns to strings
:tags: 21.2.1.2 21.3.3
:type: simulation
*/
module top;
  string binary, binary_zero, octal, octal_zero;
  initial begin
    binary = $sformatf("%0b", 8'b00001010);
    binary_zero = $sformatf("%0B", 8'b00000000);
    octal = $sformatf("%0o", 8'h0A);
    octal_zero = $sformatf("%0O", 8'h00);
    if (binary == "1010" && binary_zero == "0" &&
        octal == "12" && octal_zero == "0") $display("PASS");
    else $display("FAIL");
    $finish;
  end
endmodule
