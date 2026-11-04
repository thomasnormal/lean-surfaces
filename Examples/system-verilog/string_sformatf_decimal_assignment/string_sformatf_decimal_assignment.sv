/*
:name: string_sformatf_decimal_assignment
:description: §21.2.1.1 — literal integral decimal formatting assigns to strings
:tags: 21.2.1.1 21.3.3
:type: simulation
*/
module top;
  string lower, upper, zero;
  initial begin
    lower = $sformatf("%d", 8'd42);
    upper = $sformatf("%D", 8'd7);
    zero = $sformatf("%0d", 8'd0);
    if (lower == "42" && upper == "7" && zero == "0") $display("PASS");
    else $display("FAIL");
    $finish;
  end
endmodule
