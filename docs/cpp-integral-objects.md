# C++ integral object values

This rung-1 layer connects `ObjectStore`'s lifetime/provenance records to
`IntegralValue` storage. `IntegralObjectStore` holds an explicit `TargetProfile`,
the existing object metadata, and one optional value slot per object. Reads and
writes always consult the current lifetime record; an old reference does not
retain an obsolete value or become a reference to a later allocation.

## Semantic contract

N4950 [basic.life] starts an object's lifetime after its initialization, if any,
is complete. `initializeValue` therefore publishes an initialized live object
only after its supplied, already-converted integral value is validated.
`defaultInitialize` represents vacuous scalar default-initialization: lifetime
has begun, but no defined value is supplied. Such an object can be assigned
without first reading it. Reading an indeterminate value remains a loud refusal;
this layer does not invent an integer or claim all indeterminate reads have the
same C++ undefined-behavior rule.

`borrow` creates a typed non-owning access to a live object. Accesses can add
const qualification. `assign` checks both the object's and the access's const
qualification, validates the already-converted value, and updates the one object
slot. Two accesses to that object observe the same write; a distinct object does
not. Base integer type identity is checked independently of value width, so
equal-width `long` and `long long` are not interchangeable access types.

`initializeConverted` and `assignConverted` additionally model the scalar
conversion at an initialization or assignment boundary. They require source
type/value agreement, select the destination format from the target profile, and
publish the converted destination value. This is not overload resolution or an
implicit-conversion engine: only the already-admitted builtin-integral source
and destination pair is available.

`materializeTemporary` applies that same checked conversion while allocating a
temporary object. The caller can then extend its lifetime and retain a typed
borrow through scope cleanup.

Ending lifetime discards the readable value but retains metadata as a tombstone.
`extendTemporary` changes a live temporary's cleanup boundary without changing
its identity or value, so the value remains readable until scope cleanup.
Dynamic storage can then be released. `reuseEnded` is the explicit placement
reuse boundary: it keeps an ended identity, clears its old value, replaces its
integral type, and returns storage-only state for a new initialization.
Allocation still appends a fresh identity; no operation silently reuses a
tombstone.

## Boundary

Builtin integral objects and const qualification are admitted. Volatile access,
records, enums, pointers, reference objects, arrays, byte layout/alignment,
implicit storage reuse, casts, initialization-expression evaluation, constructors,
destructors, scope cleanup and exception unwinding remain outside this layer.
References here are checked semantic accesses, not a C++ pointer representation
or a frontend reference-binding judgment. All failures are model-domain errors,
not invented C++ exceptions.

`Translation.execute` remains refused. This is the shared value-store component
needed by future stateful expression and statement execution, not whole-program
execution or a theorem about a prototype.

## Validation

```sh
lake build LeanModels.Cpp.IntegralObjectTests
python3 extractors/cpp/test_integral_objects.py
```

Kernel guards cover exact and converted initialization, assignment after vacuous initialization,
alias-visible writes, distinct objects, const objects/accesses, stale accesses,
dynamic release, invalid values/profiles and incoherent externally supplied
slots. The rung-1 witness in `ObjectModelRung1Tests.lean` additionally traces a
converted write through a borrowed reference, reads it back, and checks that
const and ended-lifetime writes remain refused. The rung-1 default-initialization
witness also checks the uninitialized-read refusal before assigning a converted
value. The optional compiled oracle
compares defined automatic and dynamic integral-object traces at `-O0` and `-O2`
under undefined-behavior sanitization;
indeterminate and expired reads are never executed by the oracle. It validates
this component, not AST or corpus admission. Missing tools are named skips.
