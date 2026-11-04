/*
:name: invalid_string_replication_multiplier
:description: IEEE 1800-2023 §6.16 — a string replication multiplier must be a known non-negative integral value; an x multiplier is illegal.
:tags: 6.16 string replication
:type: compile_error
:diagnostic_match: replication multiplier shall be a non-negative, non-x, non-z expression
*/
module top;
  initial begin
    string text;
    logic [3:0] count = 4'bxxxx;
    text = {count{"hi"}};
    $display("PASS");
    $finish;
  end
endmodule
