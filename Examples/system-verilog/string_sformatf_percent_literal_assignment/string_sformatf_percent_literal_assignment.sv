/*
:name: string_sformatf_percent_literal_assignment
:description: §21.3.3 — escaped percent and one integral $sformatf conversion assign to a string
:tags: 21.2.1.1 21.3.3
:type: simulation
*/
module top;
  string text;
  initial begin
    text = $sformatf("load=100%% value=%0d", 7);
    if (text == "load=100% value=7") $display("PASS");
    else $display("FAIL");
    $finish;
  end
endmodule
