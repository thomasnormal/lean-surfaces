/*
:name: severity_default_format
:description: IEEE 1800-2023 Section 20.10 — severity tasks use default
  decimal/character conversions when no format string is present.
:tags: 20.10 21.2.1.1
:type: simulation
*/
module top;
  string text;
  initial begin
    text = "hello";
    $info(7);
    $warning(text);
    $error(9, text);
    $display("PASS");
    $finish;
  end
endmodule
