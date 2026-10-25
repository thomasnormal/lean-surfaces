/* §21.3.3: task-selected radix writes preserve packed X/Z digits. */
module top;
  logic [7:0] payload;
  logic [63:0] binary_text, octal_text, hex_text;

  initial begin
    binary_text = 'x;
    octal_text = 'z;
    hex_text = 'x;
    payload = 8'b10xz_zzzz;
    $swriteb(binary_text, payload);
    $swriteo(octal_text, payload);
    $swriteh(hex_text, payload);
    if ((binary_text !== 64'h3130787a7a7a7a7a) ||
        (octal_text !== 64'h000000000032787a) ||
        (hex_text !== 64'h000000000000787a))
      $display("FAIL");
    else
      $display("PASS");
    $finish;
  end
endmodule
