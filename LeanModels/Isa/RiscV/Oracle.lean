/-!
# Explicit parameters for the generated Sail support boundary

The pinned Sail Lean output measured by `LeanModels/Isa/RiscV/README.md`
cannot be admitted as emitted: its support file contributes 75 `axiom`
declarations.  This file records the parameter shape those declarations must
have before the generated semantics can enter this tree.  It is an interface,
not a replacement Sail semantics and has no default implementation.

The eight platform/reservation/randomness hooks and the floating-point hooks
below are direct translations of the signatures in Sail 0.13.1's generated
`RiscvExtras.lean`.  A future generated package should take
`SailOracle M PA` as an explicit argument (or an instance supplied by its
platform), and a proof must quantify over that argument wherever the Sail
semantics leaves the result open.
-/

namespace LeanModels.Isa.RiscV

/-! ## Platform, reservation, and nondeterminism hooks -/

/-- The effect type used by the generated Sail support functions.  The
interface deliberately does not choose a concrete Sail monad. -/
structure SailPlatformOracle (M : Type → Type) (PA : Type) where
  platTermWrite : {α : Type} → α → M Unit
  platTermRead : Unit → M String
  loadReservation : PA → Nat → M Unit
  matchReservation : PA → Bool
  cancelReservation : Unit → M Unit
  validReservation : Unit → Bool
  get16RandomBits : Unit → M (BitVec 16)
  sysEnableExperimentalExtensions : Unit → Bool

/-! ## Floating-point and conversion hooks -/

/-- The generated support file's floating-point operations, made data rather
than axioms.  The first result component is Sail's five-bit exception-flags
value; the rounding argument is Sail's three-bit rounding mode. -/
structure SailFloatOracle where
  f16Add : BitVec 3 → BitVec 16 → BitVec 16 → (BitVec 5 × BitVec 16)
  f16Sub : BitVec 3 → BitVec 16 → BitVec 16 → (BitVec 5 × BitVec 16)
  f16Mul : BitVec 3 → BitVec 16 → BitVec 16 → (BitVec 5 × BitVec 16)
  f16Div : BitVec 3 → BitVec 16 → BitVec 16 → (BitVec 5 × BitVec 16)
  f32Add : BitVec 3 → BitVec 32 → BitVec 32 → (BitVec 5 × BitVec 32)
  f32Sub : BitVec 3 → BitVec 32 → BitVec 32 → (BitVec 5 × BitVec 32)
  f32Mul : BitVec 3 → BitVec 32 → BitVec 32 → (BitVec 5 × BitVec 32)
  f32Div : BitVec 3 → BitVec 32 → BitVec 32 → (BitVec 5 × BitVec 32)
  f64Add : BitVec 3 → BitVec 64 → BitVec 64 → (BitVec 5 × BitVec 64)
  f64Sub : BitVec 3 → BitVec 64 → BitVec 64 → (BitVec 5 × BitVec 64)
  f64Mul : BitVec 3 → BitVec 64 → BitVec 64 → (BitVec 5 × BitVec 64)
  f64Div : BitVec 3 → BitVec 64 → BitVec 64 → (BitVec 5 × BitVec 64)
  f16MulAdd : BitVec 3 → BitVec 16 → BitVec 16 → BitVec 16 → (BitVec 5 × BitVec 16)
  f32MulAdd : BitVec 3 → BitVec 32 → BitVec 32 → BitVec 32 → (BitVec 5 × BitVec 32)
  f64MulAdd : BitVec 3 → BitVec 64 → BitVec 64 → BitVec 64 → (BitVec 5 × BitVec 64)
  f16Sqrt : BitVec 3 → BitVec 16 → (BitVec 5 × BitVec 16)
  f32Sqrt : BitVec 3 → BitVec 32 → (BitVec 5 × BitVec 32)
  f64Sqrt : BitVec 3 → BitVec 64 → (BitVec 5 × BitVec 64)
  f16ToI32 : BitVec 3 → BitVec 16 → (BitVec 5 × BitVec 32)
  f16ToUi32 : BitVec 3 → BitVec 16 → (BitVec 5 × BitVec 32)
  i32ToF16 : BitVec 3 → BitVec 32 → (BitVec 5 × BitVec 16)
  ui32ToF16 : BitVec 3 → BitVec 32 → (BitVec 5 × BitVec 16)
  f16ToI64 : BitVec 3 → BitVec 16 → (BitVec 5 × BitVec 64)
  f16ToUi64 : BitVec 3 → BitVec 16 → (BitVec 5 × BitVec 64)
  i64ToF16 : BitVec 3 → BitVec 64 → (BitVec 5 × BitVec 16)
  ui64ToF16 : BitVec 3 → BitVec 64 → (BitVec 5 × BitVec 16)
  f32ToI32 : BitVec 3 → BitVec 32 → (BitVec 5 × BitVec 32)
  f32ToUi32 : BitVec 3 → BitVec 32 → (BitVec 5 × BitVec 32)
  i32ToF32 : BitVec 3 → BitVec 32 → (BitVec 5 × BitVec 32)
  ui32ToF32 : BitVec 3 → BitVec 32 → (BitVec 5 × BitVec 32)
  f32ToI64 : BitVec 3 → BitVec 32 → (BitVec 5 × BitVec 64)
  f32ToUi64 : BitVec 3 → BitVec 32 → (BitVec 5 × BitVec 64)
  i64ToF32 : BitVec 3 → BitVec 64 → (BitVec 5 × BitVec 32)
  ui64ToF32 : BitVec 3 → BitVec 64 → (BitVec 5 × BitVec 32)
  f64ToI32 : BitVec 3 → BitVec 64 → (BitVec 5 × BitVec 32)
  f64ToUi32 : BitVec 3 → BitVec 64 → (BitVec 5 × BitVec 32)
  i32ToF64 : BitVec 3 → BitVec 32 → (BitVec 5 × BitVec 64)
  ui32ToF64 : BitVec 3 → BitVec 32 → (BitVec 5 × BitVec 64)
  f64ToI64 : BitVec 3 → BitVec 64 → (BitVec 5 × BitVec 64)
  f64ToUi64 : BitVec 3 → BitVec 64 → (BitVec 5 × BitVec 64)
  i64ToF64 : BitVec 3 → BitVec 64 → (BitVec 5 × BitVec 64)
  ui64ToF64 : BitVec 3 → BitVec 64 → (BitVec 5 × BitVec 64)
  f16ToF32 : BitVec 3 → BitVec 16 → (BitVec 5 × BitVec 32)
  f16ToF64 : BitVec 3 → BitVec 16 → (BitVec 5 × BitVec 64)
  f32ToF64 : BitVec 3 → BitVec 32 → (BitVec 5 × BitVec 64)
  f32ToF16 : BitVec 3 → BitVec 32 → (BitVec 5 × BitVec 16)
  f64ToF16 : BitVec 3 → BitVec 64 → (BitVec 5 × BitVec 16)
  f64ToF32 : BitVec 3 → BitVec 64 → (BitVec 5 × BitVec 32)
  f32ToBF16 : BitVec 3 → BitVec 32 → (BitVec 5 × BitVec 16)
  f16Lt : BitVec 16 → BitVec 16 → (BitVec 5 × Bool)
  f16LtQuiet : BitVec 16 → BitVec 16 → (BitVec 5 × Bool)
  f16Le : BitVec 16 → BitVec 16 → (BitVec 5 × Bool)
  f16LeQuiet : BitVec 16 → BitVec 16 → (BitVec 5 × Bool)
  f16Eq : BitVec 16 → BitVec 16 → (BitVec 5 × Bool)
  f32Lt : BitVec 32 → BitVec 32 → (BitVec 5 × Bool)
  f32LtQuiet : BitVec 32 → BitVec 32 → (BitVec 5 × Bool)
  f32Le : BitVec 32 → BitVec 32 → (BitVec 5 × Bool)
  f32LeQuiet : BitVec 32 → BitVec 32 → (BitVec 5 × Bool)
  f32Eq : BitVec 32 → BitVec 32 → (BitVec 5 × Bool)
  f64Lt : BitVec 64 → BitVec 64 → (BitVec 5 × Bool)
  f64LtQuiet : BitVec 64 → BitVec 64 → (BitVec 5 × Bool)
  f64Le : BitVec 64 → BitVec 64 → (BitVec 5 × Bool)
  f64LeQuiet : BitVec 64 → BitVec 64 → (BitVec 5 × Bool)
  f64Eq : BitVec 64 → BitVec 64 → (BitVec 5 × Bool)
  f16roundToInt : BitVec 3 → BitVec 16 → Bool → (BitVec 5 × BitVec 16)
  f32roundToInt : BitVec 3 → BitVec 32 → Bool → (BitVec 5 × BitVec 32)
  f64roundToInt : BitVec 3 → BitVec 64 → Bool → (BitVec 5 × BitVec 64)

/-! ## Combined explicit parameter -/

/-- All 75 generated support hooks as explicit data.  There is intentionally
no `default` value: the generated Sail semantics must state which platform,
reservation implementation, randomness source, and arithmetic oracle it is
using. -/
structure SailOracle (M : Type → Type) (PA : Type)
    extends SailPlatformOracle M PA, SailFloatOracle

end LeanModels.Isa.RiscV
