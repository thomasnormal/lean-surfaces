/*
:name: sformatf_uppercase
:description: §21.2.1.1 — uppercase integral format letters match lowercase
:tags: 21.2.1.1,21.3.3
:type: simulation
*/
module top;
  logic [7:0] v = 8'hAB;
  initial begin
    if ($sformatf("%H", v) == $sformatf("%h", v) &&
        $sformatf("%D", v) == $sformatf("%d", v) &&
        $sformatf("%O", v) == $sformatf("%o", v) &&
        $sformatf("%B", v) == $sformatf("%b", v))
      $display("PASS");
    else begin $display("FAIL: uppercase format spec mismatch"); $finish; end
    $finish;
  end
endmodule
