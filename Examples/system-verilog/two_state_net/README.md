# Two-state data on ordinary wires

The legacy self-check tier admits scalar and descending packed-vector
`wire bit` declarations. Un-driven wires retain the net's high-impedance
startup value; a four-state continuous source is squashed to zero at the
two-state data boundary. Other net kinds and unsupported shapes remain loud.

The fixture checks floating scalar/vector cells and an `x` driver.
