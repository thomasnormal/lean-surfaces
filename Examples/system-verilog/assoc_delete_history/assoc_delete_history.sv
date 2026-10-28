/*
:name: assoc_delete_history
:description: IEEE 1800-2023 §7.9.2 finite literal associative-array deletes
:tags: 7.9.2 associative array delete
:type: simulation
*/
module top;
  int values[string];
  logic [3:0] nibbles[int];
  initial begin
    values["red"] = 1;
    values["blue"] = 2;
    values.delete("red");
    if (values.num() == 1 && !values.exists("red") &&
        values.exists("blue") && values["red"] == 0)
      $display("PASS");
    else
      $display("FAIL");
    values.delete();
    if (values.size() == 0 && values["blue"] == 0)
      $display("PASS2");
    else
      $display("FAIL2");

    nibbles[3] = 4'hf;
    nibbles.delete(3);
    if (nibbles.num() == 0 && nibbles[3] === 4'hx)
      $display("PASS3");
    else
      $display("FAIL3");
    $finish;
  end
endmodule
