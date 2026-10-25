/* Empty queue pop methods return the element type default. */
module top;
  int front[$];
  int back[$];
  initial begin
    int front_value, back_value;
    front_value = front.pop_front();
    back_value = back.pop_back();
    if (front_value === 0 && back_value === 0 &&
        front.size() === 0 && back.size() === 0)
      $display("PASS");
    else
      $display("FAIL: empty queue pop result");
    $finish;
  end
endmodule
