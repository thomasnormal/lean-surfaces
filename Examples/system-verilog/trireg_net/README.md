# Plain un-driven `trireg` nets

The legacy self-check tier lowers a plain, un-driven `trireg` scalar or packed
vector to a flat net initialized to high impedance. Charge-strength forms,
delays, declaration drivers, and continuous drivers remain loud because the
envelope does not retain charge or driver state.

The fixture checks both scalar and vector initial values.
