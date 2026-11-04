/* Discarded pure string transformations have no represented state effect. */
module top;
  string text = "Abc-xy";
  initial begin
    text.toupper();
    text.tolower();
    text.substr(1, 3);
    text.substr(-1, 99);
    $display("PASS");
    $finish;
  end
endmodule
