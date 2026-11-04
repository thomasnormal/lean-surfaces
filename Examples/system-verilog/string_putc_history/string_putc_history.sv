/*
:name: string_putc_history
:description: IEEE 1800-2023 §6.16.2 source-pure string.putc updates
:tags: 6.16 6.16.2 string putc
:type: simulation
*/
module top;
  string s;
  initial begin
    s = "abc";
    s.putc(1, "X");
    if (s != "aXc") begin $display("FAIL"); $finish; end
    if (s.getc(1) != 8'h58) begin $display("FAIL"); $finish; end
    s.putc(1, 32'h0000_0144);
    if (s != "aDc") begin $display("FAIL"); $finish; end
    s.putc(1, 0);
    s.putc(3, "Q");
    s.putc(-1, "Q");
    if (s != "aDc") begin $display("FAIL"); $finish; end
    $display("PASS");
    $finish;
  end
endmodule
