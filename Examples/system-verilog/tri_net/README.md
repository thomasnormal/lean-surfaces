# Un-driven `tri` nets

The legacy self-check tier lowers an un-driven `tri` net to a
declaration-initialized high-impedance cell. A `tri` with a continuous driver
remains loud unless it is already covered by the existing literal-driver path,
because general net-strength resolution is outside the flat state.
