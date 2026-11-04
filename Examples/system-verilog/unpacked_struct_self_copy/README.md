# Unpacked struct self-copy

An exact blocking self-copy of a flattened integral unpacked struct is an
observable no-op. The extractor erases the store after checking the source and
destination are the same struct; nonblocking self-copies remain loud because
publication is scheduler-visible.
