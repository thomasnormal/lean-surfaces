/* Source-pure finite associative-array compound assignment history. */
module top;
  int by_name[string];
  int by_number[int];
  string name_key = "beta";

  initial begin
    by_name["alpha"] = 3;
    by_name[name_key] = 10;
    by_name[name_key] += 5;
    by_name["alpha"] <<= 2;

    by_number[1] = 3;
    by_number[2] = 10;
    by_number[2] += 5;
    by_number[1] <<= 2;

    if (by_name.num() == 2 && by_name.size() == 2 &&
        by_name["alpha"] == 12 && by_name[name_key] == 15)
      $display("PASS1");
    if (by_number.num() == 2 && by_number.size() == 2 &&
        by_number[1] == 12 && by_number[2] == 15)
      $display("PASS2");
    $finish;
  end
endmodule
