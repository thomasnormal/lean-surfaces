/* Fixed unpacked struct arrays sort and reverse-sort by one scalar field. */
module top;
  typedef struct { byte red; byte green; byte blue; } color_t;
  color_t values[3];

  initial begin
    values[0] = '{red: 5, green: 9, blue: 2};
    values[1] = '{red: 1, green: 7, blue: 4};
    values[2] = '{red: 3, green: 4, blue: 8};
    values.sort with (item.red);
    if (values[0].red == 1 && values[1].red == 3 && values[2].red == 5 &&
        values[0].green == 7 && values[1].green == 4 && values[2].green == 9)
      $display("SORT PASS");
    else
      $display("SORT FAIL");
    values.rsort with (item.red);
    if (values[0].red == 5 && values[1].red == 3 && values[2].red == 1 &&
        values[0].blue == 2 && values[1].blue == 8 && values[2].blue == 4)
      $display("RSORT PASS");
    else
      $display("RSORT FAIL");
    $finish;
  end
endmodule
