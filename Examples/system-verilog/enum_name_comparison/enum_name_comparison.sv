/*
:name: enum_name_comparison
:description: IEEE 1800-2023 §6.19.5 - compare enum.name() results, including first/last and invalid values.
:tags: 6.19.5 enum name comparison
:type: simulation
*/
module top;
  typedef enum { ALPHA, BETA, GAMMA } g_t;
  g_t e;
  initial begin
    g_t f;
    g_t l;
    int ok;
    ok = 1;
    e = BETA;
    f = e.first();
    l = e.last();
    if (f.name() != "ALPHA") ok = 0;
    if (l.name() != "GAMMA") ok = 0;
    if (e.name() != "BETA") ok = 0;
    e = g_t'(99);
    if (e.name() != "") ok = 0;
    if (ok) $display("PASS");
    else    $display("FAIL");
    $finish;
  end
endmodule
