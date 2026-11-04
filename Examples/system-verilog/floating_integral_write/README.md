# Pure integral-to-real writes

Blocking writes from pure integral expressions into named `real` storage are
admitted in the legacy self-check tier. Floating storage is intentionally
opaque, and later floating reads remain loud; the fixture checks the admitted
writes without inventing a real-valued state slot.
