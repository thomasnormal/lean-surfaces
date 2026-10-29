/*
:name: default_display_format
:description: §21.2.1.1 — no-format display and write arguments use their default decimal representation
:tags: 21.2.1 21.2.1.1
:type: simulation
// expected output lines: 175, 175, hello
*/
module top;
  bit [7:0] value = 8'haf;
  string text;

  initial begin
    text = "hello";
    $display(value);
    $write(value);
    $display;
    $display(text);
  end
endmodule
