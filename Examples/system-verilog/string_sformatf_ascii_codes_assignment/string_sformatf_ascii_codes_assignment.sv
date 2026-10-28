/*
:name: string_sformatf_ascii_codes_assignment
:description: §21.2.1.7 — integral $sformatf %s operands are packed ASCII codes
:tags: 21.2.1.7 21.3.3
:type: simulation
*/
module top;
  string pair, character;
  initial begin
    pair = $sformatf("%s", 16'h4869);
    character = $sformatf("%S", 8'd65);
    if (pair == "Hi" && character == "A") $display("PASS");
    else $display("FAIL");
    $finish;
  end
endmodule
