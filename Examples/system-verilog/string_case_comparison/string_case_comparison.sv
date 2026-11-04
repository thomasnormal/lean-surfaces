/*
:name: string_case_comparison
:description: IEEE 1800-2023 §§6.16.4-6.16.5 - compare literal string case transformations.
:tags: 6.16.4 6.16.5 string
:type: simulation
*/
module top;
  string s;
  initial begin
    s = "A1_b-?Z";
    if (s.toupper() == "A1_B-?Z" && s.tolower() == "a1_b-?z")
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
