// Verbatim excerpt from the Go standard library, for reference beside the
// Lean model in `guards.lean`. NOT compiled as part of this repository.
//
//   source : src/crypto/internal/fips140/bigmod/nat.go  (Go 1.25.6)
//   license: BSD-3-Clause, "Copyright 2009 The Go Authors." — see
//            docs/go-charter.md §1.4, which rules that the in-tree copies
//            are taken under the repository's single BSD-3 instrument
//            rather than the website's CC-BY-4.0.
//
// It is reproduced under the cite-and-paraphrase law as the rung-3
// exemplar: a real function, chosen by census (docs/backlog/go.md §G6),
// not a fixture written to be easy.

package bigmod

// bitLen is a version of bits.Len that only leaks the bit length of n, but not
// its value. bits.Len and bits.LeadingZeros use a lookup table for the
// low-order bits on some architectures.
func bitLen(n uint) int {
	len := 0
	// We assume, here and elsewhere, that comparison to zero is constant time
	// with respect to different non-zero values.
	for n != 0 {
		len++
		n >>= 1
	}
	return len
}
