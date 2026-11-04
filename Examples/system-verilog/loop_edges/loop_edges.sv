// Trip-schema endpoint headers (WS3 gate G-L0): one always_comb per header shape, every bound a
// parameter so the extractor retains each loop as a `For` node. The bodies only make the loops
// observable; the Lean side (`loop_edges/schema.lean`) reads the HEADERS off the envelope.
module loop_edges #(parameter int N = 4, parameter int C = 3) (
  input  logic [511:0] a,
  output logic [511:0] y_lt, y_le, y_desc, y_step, y_neg, y_shadow, y_pshadow
);
  // `<`: 0 trips at N = 0, 1 at N = 1, and 126, 127, 200 trips
  always_comb begin
    y_lt = '0;
    for (int i = 0; i < N; i++) y_lt[i] = a[i];
  end
  // `<=`
  always_comb begin
    y_le = '0;
    for (int i = 0; i <= N; i++) y_le[i] = a[i];
  end
  // descending `>=` with `--`
  always_comb begin
    y_desc = '0;
    for (int i = N - 1; i >= 0; i--) y_desc[i] = a[i];
  end
  // compound step `+= C`
  always_comb begin
    y_step = '0;
    for (int i = 0; i < N; i += C) y_step[i] = a[i];
  end
  // negative start
  always_comb begin
    y_neg = '0;
    for (int i = -C; i < N; i++) y_neg[i + C] = a[i + C];
  end
  // iterator shadowing: the inner `i` shadows the outer `i`
  always_comb begin
    y_shadow = '0;
    for (int i = 0; i < C; i++)
      for (int i = 0; i < N; i++)
        y_shadow[i] = a[i];
  end
  // an iterator shadowing a parameter: inside the loop `N` is the iterator
  always_comb begin
    y_pshadow = '0;
    for (int N = 0; N < C; N++) y_pshadow[N] = a[N];
  end
endmodule
