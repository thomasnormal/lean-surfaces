# Un-driven implicit-pull nets

The legacy self-check tier lowers un-driven `tri0` and `tri1` declarations to
flat cells initialized with their implicit pull zero or one. A driven pull net
remains loud because the envelope does not model pull-strength resolution.
