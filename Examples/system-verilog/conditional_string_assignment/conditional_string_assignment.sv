/* Source-pure conditional string assignments have no modeled string slot. */
module top;
  string chosen;
  string left = "left";
  bit select_left;

  initial begin
    select_left = 1'b1;
    chosen = select_left ? left : "right";
    if (chosen != "left") begin
      $display("FAIL true branch");
      $finish;
    end

    select_left = 1'b0;
    chosen = select_left ? left : "right";
    if (chosen != "right") begin
      $display("FAIL false branch");
      $finish;
    end

    $display("PASS");
    $finish;
  end
endmodule
