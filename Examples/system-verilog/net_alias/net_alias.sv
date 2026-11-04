/*
:name: net_alias
:description: §10.6 — a direct whole-net alias shares the aliased net cell
:tags: 10.6
:type: simulation
*/
module top;
  wire source;
  wire view;
  alias source = view;
  assign source = 1'b1;

  initial begin
    // PASS
    if (view === 1'b1) $display("PASS");
    else $display("FAIL");
    $finish;
  end
endmodule
