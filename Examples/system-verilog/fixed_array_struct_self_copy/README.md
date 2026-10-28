# Fixed-array struct self-copy

An exact blocking self-copy of a one-dimensional fixed unpacked array of
integral unpacked structs is an observable no-op. The extractor erases the
store after checking the complete cell shape; nonblocking self-copies remain
loud because their publication is scheduler-visible.
