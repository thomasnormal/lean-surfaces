# Object-backed integral frames and lexical scopes

2026-10-19. `LeanModels/Cpp/IntegralObjectFrame.lean` connects the integral
object store to a stateful function frame. It is the executable foundation for
automatic parameter and local declarations, including the validated Clang
`DeclStmt` fragment; it does not replace the existing value-only callable
evaluator.

`IntegralObjectFrame` owns one `IntegralObjectStore` and a stack of
`FrameScope`s. A binding records the declaration occurrence handle, its fresh
`ObjectId`, structured type, and whether it is a parameter or local. Lookup
walks from the innermost scope outward, so declaration handles remain identity
witnesses even when source spellings repeat. Every active scope shares one
declaration-handle namespace: a handle cannot be bound again while its earlier
binding remains active, including from a nested scope. After that scope exits,
the handle may be reused by a new dynamic scope, which receives a new object.

Entering a scope pushes an empty binding list. Parameter declaration allocates
automatic storage and initializes it before publishing the binding. Local
declaration publishes its storage binding before evaluating the initializer;
self-reference therefore resolves to the new not-yet-live object and returns
the store's lifetime refusal. A successful expression initializer then uses
`initializeConverted`, preserving the source type and destination conversion.
Default initialization uses `defaultInitialize`: a mutable scalar is alive but
uninitialized and can be assigned without a read. Zero initialization is kept
separate from default initialization. Const access and unsupported structured
types continue to be rejected by `IntegralObjectStore`.

`FrameOutcome` always returns the mutated frame alongside its result. A failed
initializer retains its storage-only binding and all earlier declarations; it
does not roll back a prefix or invent a value. Reads and assignments resolve
through the current frame, so aliasing is the store's object identity rather
than a name-based copy.

`Statement` supplies the stateful control shell for this slice: blocks, ifs,
while loops, for loops, assignment, declaration forms, `break`, `continue`,
and `return`. A for initializer scope encloses its condition, step and body;
each block execution pushes a fresh scope. Loop transfers are consumed by the
nearest loop, while a return unwinds every active scope before publishing its
value. A top-level break or continue is a loud boundary error.

Exiting a scope ends bindings in reverse declaration order and removes only
that scope's bindings. Object IDs remain tombstones in the append-only store.
`returnValue` evaluates the return expression before unwinding all scopes,
then returns the value with the closed frame. Fuel exhaustion, undefined
integral operations, missing declarations and lifetime errors retain the
current frame instead of claiming a successful cleanup.

The expression fragment is deliberately small: literals, declaration-handle
reads, integral unary operations and integral binary operations. The frontend
adapter joins Clang declaration, type, storage and initializer evidence before
the frame executes it; unsupported declaration forms remain loud. The tests
cover parameter and sequential-local initialization, copy/direct/list/default
initialization, nested lookup and shadowing, repeated loop-body allocation,
self-initialization, default initialization followed by assignment, retained
prefix state on division failure, reverse cleanup, return-before-cleanup, const
writes, and loud missing/duplicate bindings.
