/* Discarded deletes from an untouched associative array are inert. */
module top;
  int by_name[string];
  int by_number[int];
  initial begin
    by_name.delete("missing");
    by_name.delete();
    by_number.delete(7);
    if (by_name.num() == 0 && by_name.size() == 0 && by_number.num() == 0)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
