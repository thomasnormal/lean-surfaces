/*
:name: string_index_literal_character
:description: §6.16 — a constant-index string byte can be assigned from a one-byte literal
:tags: 6.16
:type: simulation
*/
module top;
  string a;
  initial begin
    a = "hello";
    a[0] = "h";
    if (a != "hello") begin $display("FAIL"); $finish; end
    a[0] = "H";
    if (a != "Hello") begin $display("FAIL"); $finish; end
    $display("PASS");
    $finish;
  end
endmodule
