# Nonvirtual base views on existing objects

2026-10-21. N4950 [class.derived], [class.access.base] and [expr.static.cast]
distinguish an existing complete object from each nonvirtual base-subobject
occurrence. A repeated base in a nonvirtual diamond has a different identity on
each path. A virtual base requires shared-subobject rules and is outside this
slice.

`ClassBaseView` is an explicit state projection. The caller supplies the closed
class hierarchy, one object ID for every expanded occurrence, a source path and
a target path. The source path must be a strict prefix of the target path, so a
view can move from a complete object to a base or from a base occurrence to one
of its bases. Every object is checked against the concrete root's declaration,
constness, storage duration, live initialized phase and empty scalar payload.
The target result is the existing object ID at the selected path and the exact
same `IntegralObjectStore`.

Each admitted base edge retains both Clang's effective access and the source's
written access spelling. The view policy currently admits only paths whose
traversed effective edges are `public`; a protected or private edge returns
`inaccessibleBase` before any projection is produced. This gives the state API
the public conversion boundary without pretending to model protected/private
context, friends, or source-level cast lookup. The written label remains
provenance data for later access-context work.

This operation does not parse or execute a C++ cast expression. It does not
infer ABI offsets, allocate a pointer, perform source-context access lookup,
resolve a virtual base, search for a unique target by class name, or perform
virtual dispatch. Its public-only edge check is the explicit policy boundary.
The explicit path is the identity witness; repeated occurrences therefore stay
distinct and ambiguous name-only conversions are never silently guessed.

The kernel controls cover complete-root and nested-base views, const roots,
diamond identity, prefix failures, same-subobject and missing-path refusals,
duplicate IDs, malformed value stores and a non-public-edge refusal. The generic
theorem proves that a successful view preserves caller memory. Native
class-subobject controls already
compile and observe the same concrete-root/base identities at O0/O2 with UBSan;
they remain the differential oracle for pointer identity while this state API
keeps source conversion outside its trust boundary.
