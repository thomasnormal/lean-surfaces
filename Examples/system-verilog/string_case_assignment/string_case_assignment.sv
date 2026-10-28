/*
:name: string_toupper_method
:description: §11.10.2 — string.toupper() converts all characters to uppercase
:tags: 11.10.2
:type: simulation
*/
module top;
  string s;
  initial begin
    s = "hello123";
    s = s.toupper();
    if (s != "HELLO123") begin $display("FAIL: got '%s'", s); $finish; end
    $display("PASS");
    $finish;
  end
endmodule
