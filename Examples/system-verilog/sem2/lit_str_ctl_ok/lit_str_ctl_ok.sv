// WP-R-D control for lit_str_ctl: the spellings that every tool reads alike stay admitted and equal in all simulators: the octal controls (\007 \013 \014 = bell, vertical tab, form feed), \n and \t, an escaped backslash before a letter ("\\a" is the two characters backslash and a), and an escaped quote.
module lit_str_ctl_ok (
  input  logic [7:0]  a,
  output logic [23:0] yoct,
  output logic [7:0]  yn,
  output logic [7:0]  yt,
  output logic [15:0] ybsa,
  output logic [7:0]  yq,
  output logic        eq
);
  assign yoct = "\007\013\014";
  assign yn   = "\n";
  assign yt   = "\t";
  assign ybsa = "\\a";
  assign yq   = "\"";
  assign eq   = (a == "\013");
endmodule
