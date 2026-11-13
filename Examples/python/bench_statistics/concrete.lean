import LeanModels.Python

/-! A small concrete theorem for the vendored CPython 3.9.25
`statistics.median` function. The odd-cardinality branch avoids the separate
binary64 division proof while still executing the byte-verbatim body through
the deep-embedded interpreter. -/

open LeanModels LeanModels.Python

load_program bench_statistics from "Examples/python/bench_statistics/bench_statistics.json"

theorem bench_statistics_median_odd :
    (match callFunction bench_statistics "median"
      #[.list #[.int 1, .int 3, .int 5]] 4096 with
     | .ok (.int 3) => true
     | _ => false) = true := by
  native_decide
