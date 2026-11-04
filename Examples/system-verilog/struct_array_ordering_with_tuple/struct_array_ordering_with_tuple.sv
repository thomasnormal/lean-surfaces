/* Fixed unpacked struct arrays sort by a packed two-field key. */
module top;
  typedef struct { byte red; byte green; byte blue; } color_t;
  color_t values[4];

  initial begin
    values[0] = '{red: 1, green: 5, blue: 2};
    values[1] = '{red: 2, green: 3, blue: 1};
    values[2] = '{red: 3, green: 4, blue: 2};
    values[3] = '{red: 4, green: 1, blue: 1};
    values.sort(x) with ({x.blue, x.green});
    if (values[0].red == 4 && values[1].red == 2 &&
        values[2].red == 3 && values[3].red == 1)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
