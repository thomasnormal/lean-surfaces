# Un-driven supply nets

The legacy self-check tier lowers an un-driven `supply0` or `supply1` net to a
declaration-initialized flat cell. A supply net with any continuous driver
remains loud because the flat state has no IEEE strength lattice; vector
supplies use the same repeated constant bit.
