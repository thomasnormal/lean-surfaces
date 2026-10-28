/*
:name: string_sformatf_integral_wrapper_assignment
:description: §21.3.3 — literal text around one integral $sformatf conversion assigns to strings
:tags: 21.2.1.1 21.3.3
:type: simulation
*/
module top;
  string decimal, hexa, binary, octal, character;
  initial begin
    decimal = $sformatf("v=%0d", 8'd42);
    hexa = $sformatf("<%h>", 8'hAB);
    binary = $sformatf("b=%B", 4'b1010);
    octal = $sformatf("o=%0O", 6'o17);
    character = $sformatf("c=%C", 8'h41);
    if (decimal == "v=42" && hexa == "<ab>" && binary == "b=1010" &&
        octal == "o=17" && character == "c=A") $display("PASS");
    else $display("FAIL");
    $finish;
  end
endmodule
