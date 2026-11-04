/*
:name: string_integer_conversion
:description: IEEE 1800-2023 §6.16 — literal integer-to-string conversion methods
:tags: 6.16 6.16.1 string itoa bintoa octtoa hextoa
:type: simulation
*/
module top;
  string s;
  initial begin
    s = "";
    s.itoa(255);
    if (s != "255") begin $display("FAIL: itoa(255) got '%s'", s); $finish; end
    s.hextoa(255);
    if (s != "ff") begin $display("FAIL: hextoa(255) got '%s'", s); $finish; end
    s.bintoa(10);
    if (s != "1010") begin $display("FAIL: bintoa(10) got '%s'", s); $finish; end
    s.octtoa(8);
    if (s != "10") begin $display("FAIL: octtoa(8) got '%s'", s); $finish; end
    $display("PASS");
    $finish;
  end
endmodule
