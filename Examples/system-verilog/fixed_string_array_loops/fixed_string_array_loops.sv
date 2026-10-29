/*
:name: fixed_string_array_loops
:description: source-pure fixed string-array elements in foreach, while and do-while
:tags: 12.7.3 12.7.4 12.7.5
:type: simulation
*/
module top;
  string test [4] = '{"111", "222", "333", "444"};
  int hits;
  initial begin
    int i = 0;
    int j = 0;
    foreach (test[i]) begin
      if (test[i] == "222") hits++;
    end
    while (test[j] != "222") j++;
    do j++; while (j < 3);
    if (hits == 1 && j == 3) $display("PASS");
    else $display("FAIL");
    $finish;
  end
endmodule
