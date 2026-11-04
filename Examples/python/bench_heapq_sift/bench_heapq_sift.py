"""CPython heapq._siftdown/_siftup, vendored verbatim for the Lean
verification benchmark (Band C marker: in-place list mutation).

Provenance:
  package : CPython standard library, module `heapq`
  version : Python 3.9.25 (system interpreter of this repo's toolchain)
  file    : /usr/lib64/python3.9/heapq.py, sha256
            0351667ed3afd3310ebd353526824d6f6f34d641ef0a785552c6893b7f95fdf3
  license : PSF License Agreement for Python 3.9.25 (PSF-2.0);
            Copyright (c) 2001-2026 Python Software Foundation.

Vendoring rules (python benchmark, Examples/python/bench_heapq_sift):
  * _siftdown and _siftup are BYTE-VERBATIM copies of heapq.py 3.9.25
    lines 205-217 and 258-276 (sha256 of the two segments:
    5a3bd7628494fcb72968a0018cce3e3d94e6066fa611feb012520151cd11d876
    136c35d6c8dfb2c475d08e84b8b5b0723024402a69b319875702c445eaab27b7). Do NOT edit their bodies. _siftup calls _siftdown (same file,
    vendored below it exactly as in the original).
  * These are the underscore-private pure-Python helpers; the C
    accelerator (`from _heapq import *`) replaces the public functions
    but NOT these two names, so `heapq._siftup` at runtime IS this code.
  * Both functions mutate their `heap` argument in place through
    subscript stores -- the mutation is observable by the caller through
    aliasing. That is the point of this Band C marker: value-semantics
    v0 cannot express it without a state-threading transform.

Authenticity (2026-07-29, Python 3.9.25):
_siftup([5,1,2,7,4,3], 0) leaves the list as [1, 4, 2, 7, 5, 3];
_siftdown([1,3,2,7,4,0], 0, 5) leaves it as [0, 3, 1, 7, 4, 2]
computed against this file AND against the installed `heapq` module's
_siftup/_siftdown -- both agree.
"""

def _siftdown(heap, startpos, pos):
    newitem = heap[pos]
    # Follow the path to the root, moving parents down until finding a place
    # newitem fits.
    while pos > startpos:
        parentpos = (pos - 1) >> 1
        parent = heap[parentpos]
        if newitem < parent:
            heap[pos] = parent
            pos = parentpos
            continue
        break
    heap[pos] = newitem

def _siftup(heap, pos):
    endpos = len(heap)
    startpos = pos
    newitem = heap[pos]
    # Bubble up the smaller child until hitting a leaf.
    childpos = 2*pos + 1    # leftmost child position
    while childpos < endpos:
        # Set childpos to index of smaller child.
        rightpos = childpos + 1
        if rightpos < endpos and not heap[childpos] < heap[rightpos]:
            childpos = rightpos
        # Move the smaller child up.
        heap[pos] = heap[childpos]
        pos = childpos
        childpos = 2*pos + 1
    # The leaf at pos is empty now.  Put newitem there, and bubble it up
    # to its final resting place (by sifting its parents down).
    heap[pos] = newitem
    _siftdown(heap, startpos, pos)
