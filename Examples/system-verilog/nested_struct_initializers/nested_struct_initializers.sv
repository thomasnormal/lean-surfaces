/* Complete nested unpacked-struct assignment patterns flatten to leaf cells. */
module top;
  typedef struct {
    int A;
    struct { int B, C; } BC1, BC2;
  } T;
  T def_value = '{default:10};

  typedef struct { int x; int y; } point_t;
  typedef struct { point_t start; point_t finish; bit enabled; } span_t;

  initial begin
    span_t span = span_t'{start: '{x: 3, default: 4},
                          finish: '{default: 9}, default: 1};
    if (def_value.A == 10 && def_value.BC1.B == 10 &&
        def_value.BC1.C == 10 && def_value.BC2.B == 10 &&
        def_value.BC2.C == 10 && span.start.x == 3 &&
        span.start.y == 4 && span.finish.x == 9 &&
        span.finish.y == 9 && span.enabled)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
