/*
:name: string_substr_extraction
:description: §11.10.2 — string.substr(i,j) extracts characters from i to j inclusive
:tags: 11.10.2
:type: simulation
*/
module top;
  string s, sub;
  initial begin
    s = "HelloWorld";
    sub = s.substr(0, 4);
    if (sub != "Hello") begin $display("FAIL: [0:4]='%s'", sub); $finish; end
    sub = s.substr(5, 9);
    if (sub != "World") begin $display("FAIL: [5:9]='%s'", sub); $finish; end
    $display("PASS");
    $finish;
  end
endmodule
