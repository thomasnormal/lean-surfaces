/*
:name: string_direct_copy
:description: §6.16 — source-pure blocking string copies preserve value semantics
:tags: 6.16
:type: simulation
*/
module top;
  string source, copy;
  initial begin
    source = "hello";
    copy = source;
    source = "world";
    if (copy != "hello") begin $display("FAIL: copy changed"); $finish; end
    if (source != "world") begin $display("FAIL: source changed"); $finish; end
    $display("PASS");
    $finish;
  end
endmodule
