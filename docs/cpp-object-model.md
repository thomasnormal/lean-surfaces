# C++ object and lifetime model

`LeanModels/Cpp/ObjectModel.lean` is the first stateful C++ semantic layer
above translation and typed frontend evidence. It models object identity and
the lifetime transitions needed before a callable body can be executed; it
does not execute AST statements or invent storage layouts.

## State and transitions

An `ObjectStore` is an append-only list of `CppObject` records. The returned
`ObjectId` is the list position, so an object remains a stable provenance
witness after its lifetime ends. Each object retains its `StorageDuration`,
structured `CppTypeEvidence`, and one of these phases:

- `storageOnly`: storage exists but the object's lifetime has not begun;
- `aliveUninitialized`: the lifetime has begun, but no defined value is
  available (for example, after vacuous scalar default-initialization);
- `aliveInitialized`: typed reads are permitted;
- `ended`: the lifetime has ended but storage is retained as a tombstone; or
- `released`: dynamic storage has been released.

`allocate` creates storage, while `declareAutomatic` is the rung-1 declaration
boundary that reserves automatic storage and starts the lifetime, leaving the
object `aliveUninitialized` until a separate initialization operation.
`beginLifetime` records lifetime start for other admitted transitions,
`initializeObject` marks value availability, `endLifetime` ends it, and
`releaseStorage` releases only dynamic storage after the lifetime has ended.
`readType` is the single access gate: it succeeds only for an initialized live
object and refuses missing, not-yet-live, live-but-uninitialized, ended, or
released objects with distinct errors.

Invalid transitions are explicit `ObjectError` values rather than silent
phase rewrites. The model therefore distinguishes an object whose lifetime
never started from one whose lifetime ended, and distinguishes live dynamic
storage from a releasable tombstone.

## Boundary and nonclaims

This slice is deliberately representation-only. It has no bytes, addresses,
pointer arithmetic, subobject graph, constructors/destructors, exception
unwinding, scope executor, or value store. `CppTypeEvidence` is retained as a
witness; it is not converted into a layout or an executable value. Static,
thread, and automatic storage are tracked and can be ended, but only dynamic
storage has an explicit release operation in this slice.

`LeanModels/Cpp/Translation.execute` still refuses every artifact. The next
semantic slice must connect this store to a typed expression/statement model
and add initialization/destruction obligations before any compiled-execution
claim is made.

`IntegralObjects.lean` supplies the integral-value component above this metadata
API. Its initialized lifetime start is atomic; its separate vacuous-initialization
operation supplies no value. The metadata transition primitives alone do not
claim that an arbitrary C++ initialization has completed.

`IntegralObjectStore.declareAutomaticInitialized` is the first typed initialized
declaration boundary: it reserves automatic storage, starts the lifetime,
converts the source value to the declared integral type, and publishes the
initialized value. Reads after `endLifetime` still return the distinct lifetime
error, so the convenience boundary does not erase tombstone state.

The rung-1 dynamic boundary uses the same typed value store with `.dynamic`
storage: allocation reserves a fresh identity, initialization publishes the
value, `endLifetime` creates a tombstone, and `releaseStorage` marks the dynamic
storage released. Borrowed accesses remain tied to that identity and refuse
after release rather than observing a later allocation.

## Validation

`LeanModels/Cpp/ObjectModelTests.lean` uses kernel guards for the complete
happy path, uninitialized and ended reads, repeated starts, live dynamic
release, released reads, missing IDs, and non-dynamic release. These are state
transition checks only; no differential runtime result is claimed.
