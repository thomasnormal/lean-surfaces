import LeanModels.Sv.Param
import LeanModels.Sv.CombGuard2

/-!
# SV parametric lowering to the semantic tier (`PDesign.instantiate2`)

The `Design2` twin of `Param.lean`'s `instantiate`: substitutes concrete
parameter values into a symbolic sv-0.2 envelope and lowers the FULL
semantic-tier vocabulary — selects (constant and dynamic index, read and
write), part-selects, replication, reductions, casts/signed comparisons,
bitwise resize, `case`/`case inside`, and async active-low reset processes
— into `Sem2.lean`'s `Design2`, which runs under `run2`.

Shared with `Param.lean` (single source of truth, no second copy):
`evalInt` (the constant tier, now with `bitSel`/`partSel` constant rules),
`genvarSeq`/`stepDelta` (generate iteration), `bindLocals`/`bindEnums`,
`IEnv`, and `PDesign.crossCheck` (the load-time differential gate).

## Element widths (the T-array design, honest version)

No CV32E40P provable file uses unpacked arrays for state: `fifo.mem_q` and
`register_file.mem` are **multi-dim packed** vectors, so "array" state is
ONE `LVec` and `m[i]` reads/writes the `elemW`-bit chunk at offset
`i*elemW`. `elemW` is a per-declaration fact — the product of the widths of
every packed dimension after the first (`1` for 1-D vectors and enums) —
computed here at instantiation and stored in the select nodes, never in the
state. A part-select over a multi-dim outer dimension selects whole chunks
(`offset = lsb*elemW`, `width = (msb-lsb+1)*elemW`; with `elemW = 1` this
is the ordinary 1-D rule).

## Value-tier decisions beyond `Param.lean`'s ledger

* A select whose base is a *parameter* (fifo's `FIFO_DEPTH[ADDR_DEPTH:0]`)
  is a constant — folded by `evalInt`'s new select rules and materialized
  at context width.
* A select index that constant-evaluates (genvar arithmetic like
  `2**level-1+l`) lowers to a constant `slice`; anything else stays a
  dynamic `index` node with the pinned x/OOB semantics.
* Part-select bounds must constant-evaluate (the LRM requires constant
  bounds); a failure is loud.
* `Resize` lowers to the **instantiated context width** (the envelope's
  `width` field is defaults-elaborated metadata, and contributes its
  OPERAND's width to a max-of-operands width — `selfWidth2`); the
  extractor never folds unsigned width conversions (sized literals
  included) in symbolic mode. The tree only carries the conversions the
  DEFAULT point needed, so the context rules are re-applied at every point
  (§11.6.1/§11.8.2): `- ~ +` extend their operand to the context, `+ - *`
  run at the widest x-carrying operand (`rigidMax2`) and truncate, `/ % **
  << >>` truncate to the context (`ctxTrunc2`), and a `$signed` operand
  that would need a widening the default did not is loud.
* `$signed`/`$unsigned` casts are width-preserving bit identities and
  vanish; signedness survives in the operator (`s<` … lower to `scmp`).
* A plain `case` compares at the widest self-determined width among its
  subject and every item (`caseWidth2`, §12.5): enum labels and `Int`
  patterns materialize there, and a narrower subject is zero-extended. A
  `case … inside` item wider than its subject is loud (its comparisons
  are pairwise).
-/

namespace LeanModels.Sv

/-! ## Element widths -/

/-- Element width of a declared type: product of the packed-dim widths
AFTER the first dimension (`1` for scalars, 1-D vectors, and enums). -/
def PType.elemWidth (env : IEnv) : PType → Except String Nat
  | .packed [] _ => .ok 1
  | .packed (_ :: rest) _ =>
      rest.foldlM (fun acc d => do pure (acc * (← d.width env))) 1
  | .typeRef .. => .ok 1
  | .unrecoverable _ => .error "unrecoverable packed dimensions"

/-- `(name, elemW)` for every declaration, in order (widths threaded like
`buildDecls` — `$bits`/`$high` in later bounds may look back). -/
def buildElems (env : IEnv) : List PDecl → Res (List (String × Nat))
  | [] => .ok []
  | pd :: rest => do
      match pd.type.width env, pd.type.elemWidth env with
      | .ok w, .ok ew => do
          let es ← buildElems { env with widths := (pd.name, w) :: env.widths } rest
          .ok ((pd.name, ew) :: es)
      | .error e, _ | _, .error e => Res.unsupported s!"decl '{pd.name}': {e}"

/-- Element width of a select *base* expression: a declared signal's
`elemW`; one level of select strips one dimension (the LEGACY nested
`BitSel`/`PartSel` encoding is exact only up to 2-D, so a chunk's elements
are bits — the extractor emits it only for 2-D roots and a dynamic index,
and every constant-index select chain on a multi-dimensional array as ONE
`ArraySel` path, lowered by `arrayElemRead`/`arrayPartRead` below); a
part-select keeps the element shape. A concatenation is a flat packed vector with bit elements.
`none` = outside the tier (loud at the caller). -/
def elemOf (elems : List (String × Nat)) : PExpr → Option Nat
  | .ident n => elems.lookup n
  | .concat _ => some 1
  | .bitSel .. => some 1
  | .partSel b _ _ => elemOf elems b
  | .cast _ a => elemOf elems a
  | _ => none

mutual
/-- Whether an expression reads a declared signal — its value is a RUN-TIME
quantity, never an elaboration-time constant. This is what separates a
dynamic indexed part-select base (`v[sel +: 4]`, lowered by `dynPartRead`)
from a constant base that merely fails `evalInt` (such as the
width-dependent `~K`), which stays loud on the static path. -/
def PExpr.readsSignal : PExpr → Bool
  | .ident _ | .arrayElem .. | .arrayPart .. => true
  | .unary _ a | .resize _ a | .signedResize _ a | .squash2 _ a | .sysCall _ a
  | .reduce _ a | .cast _ a => a.readsSignal
  | .binary _ l r | .bitSel l r | .repl l r => l.readsSignal || r.readsSignal
  | .partSel b m l | .ternary b m l => b.readsSignal || m.readsSignal || l.readsSignal
  | .concat ps => PExpr.readsSignalList ps
  | .lit _ | .paramRef .. | .genvarRef _ | .enumRef .. | .int _ | .fill _
  | .unsupported .. => false

/-- `PExpr.readsSignal` over a list (concatenation parts). -/
def PExpr.readsSignalList : List PExpr → Bool
  | [] => false
  | p :: ps => p.readsSignal || PExpr.readsSignalList ps
end

/-! ## Packed-array select paths (`arrayElem` / `arrayPart`)

The envelope's `ArraySel` node carries a whole select chain over a declared
packed array — `x[i₁]…[iₖ]`, optionally followed by a part select on the
next dimension — with every index/bound the RAW declared label. Lowering
reads the declaration's dimensions from `IEnv.dims` — evaluated ONCE, in
the DECLARATION's scope (`dimTable`, run by `instantiate2` before generate
expansion), never at the select site: a genvar may legally reuse the name
of a parameter the declared range mentions (`for (genvar K …)` over
`logic [3:0][K:0] m`), and the range must still see the module's `K`.
Ascending, descending and non-zero-based ranges normalize exactly at every
parameter point (IEEE 1800-2023 §7.4.2: the RIGHT bound of `[l:r]` is
offset 0 in either direction), and lowering checks EVERY dimension's range
on its own (§7.4.6/§11.5.1: `pp[0][5]` on `[1:0][3:0]` selects bit 5 of the
element `pp[0]` — out of range — never bit 5 of the flat vector). The result
is ONE flat window of the declared vector:

* in range — a read is `.slice (.ident n) lo w`, a write `Lhs2.slice n lo w`
  (the shape the comb settle theorem consumes);
* an out-of-range constant element select reads all-x and writes nothing
  (the no-op target is the zero-width window `Lhs2.slice n 0 0`) — the
  pinned `Sem2` rules for dynamic out-of-range selects;
* a part select partially out of its dimension reads x in exactly the
  out-of-range bits (a concat of the in-range window with x fill) and
  writes exactly the in-range bits: an msb-side overhang is the clipped
  window; an overhang BELOW the dimension's lsb (`x[-2 +: 4]`, `x[1 -: 4]`
  at some parameter point) is a concatenation target whose low leaf is a
  zero-effect SINK past the vector's msb, consuming the RHS bits that land
  out of range (`arrayPartTarget`).

An indexed part-select whose BASE reads a signal (`v[sel +: 4]`, §11.5.1:
only the width must be constant) is a READ-only tier over a 1-D vector
with a descending range: `dynPartPlan` and `dynBaseRead` lower it to a
shift of the x-padded vector, exact in every out-of-range bit and on an x/z
base. The base's self-determined width picks the reading: unsigned below 32
bits (`dynPartRead`), a two's-complement `int` at exactly 32 (`dynPartRead32`
— Icarus 12.0 and Yosys 0.53 both read a 32-bit index that way; measured
2026-10-28), loud above (they disagree). A dynamic base on a target, on an
ascending range, or after an element select is loud (`ArraySel:dynamic`).
A constant label far outside its dimension (`partOffsetsWild`: a 32-bit
unsigned wrap such as `UI - 1` at 0) is loud too — the two tools read it
differently.

Measured (2026-10-27): Icarus 12.0 and Yosys 0.53 both LINEARIZE a select
that leaves an INNER dimension of a non-last element — element selects
(`pp[0][4]` reads/writes `pp[1][0]`), element labels outside an ASCENDING
dimension (`q[0][4]` on `[0:1][0:3]`), and part/indexed-part selects that
overhang either end of their dimension (`m[0][5:3]` reads two bits of
`m[1]`; `q[1][-1 +: 2]` one bit of `q[0]`; the msb-overhang write
`w[0][5:2] = a` lands its top bits in `w[1]`, the lsb-overhang write
`w[1][-1 +: 2]` its low bit in `w[0][3]`). The model keeps the LRM
per-dimension rule (x reads, clipped/no-op writes; slang's constant
evaluator agrees) — a recorded simulator/synthesis disagreement
(`docs/sv-oracle-disagreements.md` "Linearized packed-array indices";
declared rows `array_oob_inner`, `array_oob_part` and `array_oob_lsbwrite`
in `harness/sv/cases2.json`). Overhang past either END of the vector (the
last element's msb, the first element's lsb) agrees in every tool (rows
`array_oob`, `partsel*`). -/

/-- Element offset of declared label `k` in a dimension declared `[l:r]`:
the right bound is offset 0 (the LSB side) whether the range ascends or
descends. -/
def labelOffset (l r k : Int) : Int := if r ≤ l then k - r else r - k

/-- Element count of a dimension declared `[l:r]`. -/
def dimCount (l r : Int) : Nat := (l - r).natAbs + 1

/-- Bits per element of a list of (unselected) dimensions. -/
def dimsStride : List (Int × Int) → Nat
  | [] => 1
  | (l, r) :: rest => dimCount l r * dimsStride rest

/-- Evaluate symbolic packed dimensions to `(msb, lsb)` labels. -/
def evalDims (env : IEnv) : List PDim → Except String (List (Int × Int))
  | [] => .ok []
  | d :: ds => do
      let m ← evalInt env d.msb
      let l ← evalInt env d.lsb
      let rest ← evalDims env ds
      .ok ((m, l) :: rest)

/-- `dimTable`'s scope after the declaration `pd`: its width threaded into
`widths` exactly as `buildDecls` does (nothing else changes). -/
def dimTableStep (env : IEnv) (pd : PDecl) : IEnv :=
  match pd.type.width env with
  | .ok w => { env with widths := (pd.name, w) :: env.widths }
  | .error _ => env

/-- The packed-array geometry table, built ONCE in the declaration scope
`env` (parameters, localparams, enums, typed-parameter widths — what
`buildDecls` sees): every declaration with an explicit packed dimension
list, its dimensions evaluated to `(msb, lsb)` labels, declared widths
threaded exactly like `buildDecls` (`$bits`/`$high` in a later bound look
back, never forward). A declaration whose dimensions do not evaluate is
ABSENT (its select paths are loud; `buildDecls` refuses it anyway). -/
def dimTable (env : IEnv) : List PDecl → List (String × List (Int × Int))
  | [] => []
  | pd :: rest =>
      match pd.type with
      | .packed ds _ =>
          match evalDims env ds with
          | .ok es => (pd.name, es) :: dimTable (dimTableStep env pd) rest
          | .error _ => dimTable (dimTableStep env pd) rest
      | _ => dimTable (dimTableStep env pd) rest

/-- The evaluated packed dimensions of the declared signal `n` (a lookup in
the declaration-scope table — the select site's genvars never reach it). -/
def arrayDims (env : IEnv) (n : String) : Except String (List (Int × Int)) :=
  match env.dims.lookup n with
  | some es => .ok es
  | none => .error s!"'{n}' has no declared packed dimension list"

/-- Walk element-select labels down the dimensions: the bit offset of the
selected element (meaningful when in range), whether EVERY index is in
range of its own dimension, and the unselected dimensions. -/
def walkIndices (env : IEnv) : List (Int × Int) → List PExpr →
    Except String (Int × Bool × List (Int × Int))
  | ds, [] => .ok (0, true, ds)
  | [], _ :: _ => .error "more selects than packed dimensions"
  | (l, r) :: ds, i :: is => do
      let k ← evalInt env i
      let (base, ok, rest) ← walkIndices env ds is
      let off := labelOffset l r k
      .ok (off * (dimsStride ds : Int) + base,
        ok && decide (0 ≤ off) && decide (off < (dimCount l r : Int)), rest)

/-- Geometry of an element-select path: `(lo, width, inRange)`. -/
def arrayElemWindow (env : IEnv) (n : String) (is : List PExpr) :
    Except String (Int × Nat × Bool) := do
  let ds ← arrayDims env n
  let (base, ok, rest) ← walkIndices env ds is
  .ok (base, dimsStride rest, ok)

/-- The two end LABELS of a part select: `[a:b]` gives `(a, b)`; `[a +: b]`
and `[a -: b]` need a positive constant width `b` (§11.5.1). -/
def partLabels (env : IEnv) (mode : PartMode) (a b : PExpr) : Except String (Int × Int) := do
  let x ← evalInt env a
  let y ← evalInt env b
  match mode with
  | .range => .ok (x, y)
  | .up => if 0 < y then .ok (x + y - 1, x) else .error "indexed part-select width must be positive"
  | .down => if 0 < y then .ok (x, x - y + 1) else .error "indexed part-select width must be positive"

/-- Geometry of a part-select path: `(prefix lo, prefix inRange, element
stride, element count of the part's dimension, lo, hi)` — `lo ≤ hi` the
element offsets the part spans within its dimension. A `[a:b]` part whose
msb label lies on the lsb side of the declared range is loud (§11.5.1
requires the declared direction; the frontend rejects it). -/
def arrayPartGeom (env : IEnv) (n : String) (is : List PExpr) (mode : PartMode)
    (a b : PExpr) : Except String (Int × Bool × Nat × Nat × Int × Int) := do
  let ds ← arrayDims env n
  let (base, ok, rest) ← walkIndices env ds is
  match rest with
  | [] => .error "part select below the last packed dimension"
  | (l, r) :: inner =>
      let (k₁, k₂) ← partLabels env mode a b
      let o₁ := labelOffset l r k₁
      let o₂ := labelOffset l r k₂
      if mode == .range && o₁ < o₂ then
        .error "part-select direction contradicts the declared range"
      else
        .ok (base, ok, dimsStride inner, dimCount l r, min o₁ o₂, max o₁ o₂)

/-- The DYNAMIC indexed part-select plan. IEEE 1800-2023 §11.5.1 lets the
base of `x[e +: w]` / `x[e -: w]` be a run-time expression (only the width
`w` must be a positive constant). `none` = the base is not dynamic (it
constant-evaluates, or reads no signal): the static `arrayPartGeom` path
decides, unchanged. `some (.ok (w, q, c))` = the read plan: part width `w`,
x pad `q` below the vector (`r` for `+:`, `r + w - 1` for `-:` over a range
`[l:r]` — chosen so the shift amount in `dynPartRead` IS the base value),
vector width `c`. `some (.error _)` = dynamic but outside the tier (loud):
the tier is a 1-D vector with a DESCENDING declared range, no element path
in front, and a non-negative pad. How the base VALUE is read (unsigned,
or 32-bit two's complement) is `dynBaseRead`'s choice, by the base's width;
a base whose type is signed is refused by the extractor
(`RangeSelectExpression:dynamic-signed-base`). -/
def dynPartPlan (env : IEnv) (n : String) (is : List PExpr) (mode : PartMode)
    (a b : PExpr) : Option (Except String (Nat × Nat × Nat)) :=
  match evalInt env a with
  | .ok _ => none
  | .error _ =>
      if !a.readsSignal then none
      else some (do
        if !is.isEmpty then throw "dynamic part-select base after an element select"
        if mode == .range then throw "dynamic [msb:lsb] bounds (§11.5.1 requires constants)"
        let w ← evalInt env b
        if w ≤ 0 then throw "indexed part-select width must be positive"
        match ← arrayDims env n with
        | [(l, r)] =>
            if l < r then throw "dynamic part-select over an ascending range"
            let q := r + (if mode == .down then w - 1 else 0)
            if q < 0 then throw "dynamic part-select over a range reaching below label 0"
            pure (w.toNat, q.toNat, dimCount l r)
        | _ => throw "dynamic part-select over a multi-dimensional packed array")

/-- Width of a packed-array select path (its select's own width, in or
out of range). -/
def arraySelWidth (env : IEnv) : PExpr → Option Nat
  | .arrayElem n is =>
      match arrayElemWindow env n is with
      | .ok (_, w, _) => some w
      | .error _ => none
  | .arrayPart n is mode a b =>
      match arrayPartGeom env n is mode a b with
      | .ok (_, _, s, _, lo, hi) => some ((hi - lo + 1).toNat * s)
      | .error _ =>
          match dynPartPlan env n is mode a b with
          | some (.ok (w, _, _)) => some w
          | _ => none
  | _ => none

/-- An out-of-range part select whose element offsets reach `±2^30`:
LOUD. Such a label only arises from a 32-bit unsigned wrap (`UI - 1` with
`int unsigned UI = 0`, `U - 1` with `logic [3:0] U = 0` — `evalInt` is
width-exact), and the tools then DISAGREE: Icarus 12.0 reads the label as a
huge unsigned index (every bit x), Yosys 0.53 as a negative one (partly in
range) — measured 2026-10-28, verifier probe `pc.sv`. (The x-filled window
would also be gigantic.) In-range selects are never affected. -/
def partOffsetsWild (lo hi : Int) : Bool :=
  decide (lo ≤ -(2 : Int) ^ 30) || decide ((2 : Int) ^ 30 ≤ hi)

/-- Read lowering of an element-select path. -/
def arrayElemRead (env : IEnv) (n : String) (is : List PExpr) : Expr2 :=
  match arrayElemWindow env n is with
  | .ok (lo, w, true) => .slice (.ident n) lo.toNat w
  | .ok (_, w, false) => .lit (LVec.xVec w)
  | .error e => .unsupported "ArraySel" e

/-- Read lowering of a part-select path: the in-range window, with x fill
for exactly the out-of-range bits. -/
def arrayPartRead (env : IEnv) (n : String) (is : List PExpr) (mode : PartMode)
    (a b : PExpr) : Expr2 :=
  match arrayPartGeom env n is mode a b with
  | .error e => .unsupported "ArraySel" e
  | .ok (pb, ok, s, c, lo, hi) =>
      let w := (hi - lo + 1).toNat * s
      if ok && decide (0 ≤ lo) && decide (hi < (c : Int)) then
        .slice (.ident n) (pb + lo * s).toNat w
      else if partOffsetsWild lo hi then
        .unsupported "ArraySel:index-range" s!"part select [{lo}, {hi}] (element offsets) far outside its dimension"
      else
        let lo' := max lo 0
        let hi' := min hi ((c : Int) - 1)
        if ok && decide (lo' ≤ hi') then
          let above := (hi - hi').toNat * s
          let below := (lo' - lo).toNat * s
          .concat ((if above = 0 then #[] else #[.lit (LVec.xVec above)])
            ++ #[.slice (.ident n) (pb + lo' * s).toNat ((hi' - lo' + 1).toNat * s)]
            ++ (if below = 0 then #[] else #[.lit (LVec.xVec below)]))
        else .lit (LVec.xVec w)

/-- Read lowering of a DYNAMIC indexed part-select (`dynPartPlan`'s
`(w, q, c)`, base lowered to `e`, read unsigned at its self-determined
width): the vector padded with `w` x bits above and `q` x bits below,
shifted right by `e`, low `w` bits — so every selected bit outside the
declared range reads x and every bit inside reads the vector (§11.5.1) —
under the guard `e ≤ c + q` (past it every selected bit is above the msb:
all x, where the logical shift would fill zeros). An x/z bit in `e` makes
the shift and the guard x, so the whole result is x (§11.5.1; Icarus
agrees, row `partsel`). -/
def dynPartRead (n : String) (w q c : Nat) (e : Expr2) : Expr2 :=
  .ternary (.binary .le e (.lit (LVec.ofNat (Nat.log2 (c + q) + 1) (c + q))))
    (.slice (.binary (.shr false)
        (.concat (#[.lit (LVec.xVec w), .ident n]
          ++ (if q = 0 then #[] else #[.lit (LVec.xVec q)]))) e) 0 w)
    (.lit (LVec.xVec w))

/-- Read lowering of a DYNAMIC indexed part-select whose base `e` is
EXACTLY 32 bits wide (`v[s - 2 +: 4]` — an unsized `2` makes the base
32-bit unsigned — or `a[sel*W +: W]`). Icarus 12.0 and Yosys 0.53 both read
such a base as a two's-complement `int` (measured 2026-10-28: `v[s-2 +: 4]`
at `s = 0` is `v[1:-2]`, its low two bits in range, the rest x; LRM §11.5.1
leaves negative bases to the index rules), so the model does too. The
shift amount is the base sign-extended to 34 bits plus `w - 1`, over the
vector padded with `w` x bits above and `q + w - 1` below: a base down to
`-(w-1)` still reaches the vector's low bits, and the single UNSIGNED
34-bit guard `t ≤ c + q + w - 1` rejects both ends at once (a base below
`-(w-1)` is negative, so `t` has its top bit set). Every out-of-range bit
reads x; an x/z base reads all x (it poisons `t`, the guard and the shift). -/
def dynPartRead32 (n : String) (w q c : Nat) (e : Expr2) : Expr2 :=
  let t : Expr2 := .binary .add (.resizeSigned 34 e) (.lit (LVec.ofNat 34 (w - 1)))
  .ternary (.binary .le t (.lit (LVec.ofNat 34 (c + q + w - 1))))
    (.slice (.binary (.shr false)
        (.concat (#[.lit (LVec.xVec w), .ident n]
          ++ (if q + w - 1 = 0 then #[] else #[.lit (LVec.xVec (q + w - 1))]))) t) 0 w)
    (.lit (LVec.xVec w))

/-- The reading of a run-time part-select base by its self-determined width
`bw` (the base lowered to `e` at that width): unsigned below 32 bits
(`dynPartRead` — every tool agrees), two's complement at exactly 32
(`dynPartRead32`), loud above (Icarus truncates a wider index to its low 32
bits, Yosys does not — measured: a 40-bit base `2^32 + 1` reads `v[4:1]` in
Icarus and all x in Yosys). -/
def dynBaseRead (n : String) (w q c bw : Nat) (e : Expr2) : Expr2 :=
  if bw < 32 then dynPartRead n w q c e
  else if bw = 32 then dynPartRead32 n w q c e
  else .unsupported "ArraySel:dynamic"
    s!"run-time part-select base of {bw} bits (wider than 32: Icarus truncates it, Yosys does not)"

/-- Target lowering of an element-select path: `(window, RHS context
width)`; out of range is the zero-width (no-op) window. -/
def arrayElemTarget (env : IEnv) (n : String) (is : List PExpr) :
    Except String (Lhs2 × Nat) :=
  match arrayElemWindow env n is with
  | .ok (lo, w, true) => .ok (.slice n lo.toNat w, w)
  | .ok (_, w, false) => .ok (.slice n 0 0, w)
  | .error e => .error e

/-- Total bit width of a declared packed vector (its geometry-table entry;
`0` when absent — unused then, the select is loud). -/
def arrayFlatWidth (env : IEnv) (n : String) : Nat :=
  match arrayDims env n with
  | .ok ds => dimsStride ds
  | .error _ => 0

/-- Target lowering of a part-select path. In range: the flat window.
Fully out of range: a no-op (the zero-width window). An overhang on the
msb side: the in-range window (the RHS's high bits are truncated away). An
overhang on the LSB side (`x[-2 +: 4]`, `x[1 -: 4]`, at some parameter
point): writes to the out-of-range bits do nothing (§11.5.1), so the
in-range elements take the RHS bits ABOVE the overhanging ones — a
concatenation target whose low leaf is a SINK, the zero-effect window just
past the vector's msb (`LVec.insertAt` drops every bit landing there),
consuming exactly the overhanging RHS bits. A concatenation target needs
one sampled RHS: continuous assigns and blocking statements; an NBA to it
stays loud (`resolveLhs2`). A dynamic (signal) base is loud — the write
tier has no run-time-offset window. -/
def arrayPartTarget (env : IEnv) (n : String) (is : List PExpr) (mode : PartMode)
    (a b : PExpr) : Except String (Lhs2 × Nat) :=
  match arrayPartGeom env n is mode a b with
  | .error e =>
      match dynPartPlan env n is mode a b with
      | some _ => .error s!"dynamic indexed part-select target (run-time base): {e}"
      | none => .error e
  | .ok (pb, ok, s, c, lo, hi) =>
      let w := (hi - lo + 1).toNat * s
      if ok && decide (0 ≤ lo) && decide (hi < (c : Int)) then
        .ok (.slice n (pb + lo * s).toNat w, w)
      else if partOffsetsWild lo hi then
        .error s!"part select [{lo}, {hi}] (element offsets) far outside its dimension"
      else if !ok || decide (hi < 0) || decide ((c : Int) ≤ lo) then
        .ok (.slice n 0 0, w)
      else if decide (0 ≤ lo) then
        .ok (.slice n (pb + lo * s).toNat (((c : Int) - lo).toNat * s), w)
      else
        .ok (.concat [.slice n pb.toNat ((min hi ((c : Int) - 1) + 1).toNat * s),
                      .slice n (arrayFlatWidth env n) ((-lo).toNat * s)], w)

/-! ## Self-determined widths (full semantic-tier version) -/

private def maxW2 : Option Nat → Option Nat → Option Nat
  | some a, some b => some (max a b)
  | some a, none => some a
  | none, some b => some b
  | none, none => none

@[simp] theorem maxW2_some (left right : Nat) :
    maxW2 (some left) (some right) = some (max left right) := rfl

/-- Width of a parameter with no DECLARED type: an untyped localparam whose
expression is not INT-class carries its expression's type in `nvals`
(`localparam L = 4'sd3` is 4 bits); every other one is a 32-bit `int`. -/
def paramNWidth (env : IEnv) (n : String) : Nat :=
  match env.nvals.lookup n with
  | some (_, w, _) => w
  | none => 32

mutual
/-- `selfWidth` twin that also knows the semantic-tier nodes (element
widths from `elems`). -/
def selfWidth2 (env : IEnv) (elems : List (String × Nat)) : PExpr → Option Nat
  | .lit v => some v.width
  | .ident n => env.widths.lookup n
  | .paramRef n _ => some ((env.pwidths.lookup n).getD (paramNWidth env n))
  | .genvarRef _ | .int _ | .sysCall .. => some 32
  | .enumRef ty _ _ => env.enums.lookup ty
  | .fill _ => none
  | .unary op a =>
      match op with
      | .m0 .lnot => some 1
      | .m0 _ | .plus => selfWidth2 env elems a
      | .inc | .dec => none
  | .binary op l r =>
      match op with
      | .m0 .eq | .m0 .ne | .m0 .wildEq | .m0 .wildNe
      | .m0 .lt | .m0 .le | .m0 .gt | .m0 .ge
      | .slt | .sle | .sgt | .sge | .ceq | .cne | .land | .lor => some 1
      | .shl | .shr | .ashl | .ashr | .pow => selfWidth2 env elems l
      | .m0 (.pow ..) | .m0 (.shl ..) | .m0 (.shr ..)
      | .m0 (.ashl ..) | .m0 (.ashr ..) => divOperandWidth2 env elems l
      | .m0 .div | .m0 .sdiv | .m0 .rem | .m0 .srem | .div | .mod =>
          maxW2 (divOperandWidth2 env elems l) (divOperandWidth2 env elems r)
      | _ =>
          match selfWidth2 env elems l, selfWidth2 env elems r with
          | some a, some b => some (max a b)
          | some a, none => some a
          | none, some b => some b
          | none, none => none
  | .ternary _ t e =>
      match selfWidth2 env elems t, selfWidth2 env elems e with
      | some a, some b => some (max a b)
      | some a, none => some a
      | none, some b => some b
      | none, none => none
  | .concat parts => selfWidthSum2 env elems parts
  | .resize w a | .signedResize w a =>
      -- An implicit conversion's envelope width is defaults-elaborated
      -- metadata (`instExpr2` lowers it to the CONTEXT width): what it
      -- contributes to a max-of-operands width at THESE parameters is its
      -- operand's own width (`divOperandWidth2`'s reading). The metadata is
      -- the fallback only for an operand of unknown width.
      match selfWidth2 env elems a with
      | some x => some x
      | none => some w
  | .squash2 w _ => some w
  | .bitSel base idx =>
      match elemOf elems base with
      | some ew => some ew
      | none =>
          -- A parameter/genvar-CONSTANT bit select (`i[0]`, `P[2]`): one bit
          -- (§11.5.1), the width `instExpr2` materializes the constant at —
          -- self-determined positions (concat/replication parts) need it.
          match evalInt env (.bitSel base idx) with
          | .ok _ => some 1
          | .error _ => none
  | .partSel base msb lsb =>
      match elemOf elems base, evalInt env msb, evalInt env lsb with
      | some ew, .ok m, .ok l =>
          if l ≤ m && 0 ≤ l then some (((m - l).toNat + 1) * ew) else none
      | none, .ok m, .ok l =>
          -- A constant part select of a parameter/genvar: `m - l + 1` bits.
          match evalInt env (.partSel base msb lsb) with
          | .ok _ => if l ≤ m && 0 ≤ l then some ((m - l).toNat + 1) else none
          | .error _ => none
      | _, _, _ => none
  | .repl count arg =>
      match evalInt env count, selfWidth2 env elems arg with
      | .ok n, some w => if 0 ≤ n then some (n.toNat * w) else none
      | _, _ => none
  | .reduce .. => some 1
  | .cast _ a => selfWidth2 env elems a
  | .arrayElem n is => arraySelWidth env (.arrayElem n is)
  | .arrayPart n is mode a b => arraySelWidth env (.arrayPart n is mode a b)
  | .unsupported .. => none

def selfWidthSum2 (env : IEnv) (elems : List (String × Nat)) : List PExpr → Option Nat
  | [] => some 0
  | p :: rest =>
      match selfWidth2 env elems p, selfWidthSum2 env elems rest with
      | some a, some b => some (a + b)
      | _, _ => none

def divOperandWidth2 (env : IEnv) (elems : List (String × Nat)) : PExpr → Option Nat
  | .resize _ operand | .signedResize _ operand => divOperandWidth2 env elems operand
  | .lit value => some value.width
  | .ident name => env.widths.lookup name
  | .paramRef name _ => some ((env.pwidths.lookup name).getD (paramNWidth env name))
  | .genvarRef _ | .int _ | .sysCall .. => some 32
  | .enumRef name _ _ => env.enums.lookup name
  | .fill _ => none
  | .unary (.m0 .lnot) _ => some 1
  | .unary (.m0 _) operand | .unary .plus operand => divOperandWidth2 env elems operand
  | .unary _ _ => none
  | .binary operator left right =>
      match operator with
      | .m0 .eq | .m0 .ne | .m0 .wildEq | .m0 .wildNe
      | .m0 .lt | .m0 .le | .m0 .gt | .m0 .ge
      | .slt | .sle | .sgt | .sge | .ceq | .cne | .land | .lor => some 1
      | .shl | .shr | .ashl | .ashr | .pow => divOperandWidth2 env elems left
      | .m0 (.pow ..) | .m0 (.shl ..) | .m0 (.shr ..)
      | .m0 (.ashl ..) | .m0 (.ashr ..) => divOperandWidth2 env elems left
      | _ => maxW2 (divOperandWidth2 env elems left) (divOperandWidth2 env elems right)
  | .ternary _ left right => maxW2 (divOperandWidth2 env elems left) (divOperandWidth2 env elems right)
  | .concat parts => divOperandWidthSum2 env elems parts
  | .squash2 width _ => some width
  | .bitSel base _ => elemOf elems base
  | .partSel base upper lower =>
      match elemOf elems base, evalInt env upper, evalInt env lower with
      | some element, .ok high, .ok low =>
          if 0 ≤ low && low ≤ high then some (((high - low).toNat + 1) * element) else none
      | _, _, _ => none
  | .repl count operand =>
      match evalInt env count, divOperandWidth2 env elems operand with
      | .ok amount, some width => if 0 ≤ amount then some (amount.toNat * width) else none
      | _, _ => none
  | .reduce .. => some 1
  | .cast _ operand => divOperandWidth2 env elems operand
  | .arrayElem n is => arraySelWidth env (.arrayElem n is)
  | .arrayPart n is mode a b => arraySelWidth env (.arrayPart n is mode a b)
  | .unsupported .. => none

def divOperandWidthSum2 (env : IEnv) (elems : List (String × Nat)) : List PExpr → Option Nat
  | [] => some 0
  | operand :: rest =>
      match divOperandWidth2 env elems operand, divOperandWidthSum2 env elems rest with
      | some left, some right => some (left + right)
      | _, _ => none
end

/-- **The widest operand that can carry x/z bits** in a context-determined
expression, at THESE parameters: through `+ - * & | ^`, unary `- ~ +`, the
`?:` arms, casts and implicit conversions (`Resize`/`SignedResize` — their
envelope width is defaults-elaborated metadata, never a width here), down
to the rigid leaves, which give their self-determined width (`selfWidth2`;
any other node is a leaf). Constants — unsized integers, parameters,
genvars, enum labels, fills, system calls — give `none`: they carry no x
bits, so the width they add to the operation (§11.6.1: an unsized integer
is 32 bits) changes no bit of the context-width result of these operators,
whose low bits depend only on the operands' low bits. -/
def rigidMax2 (env : IEnv) (elems : List (String × Nat)) : PExpr → Option Nat
  | .int _ | .paramRef .. | .genvarRef _ | .fill _ | .enumRef .. | .sysCall .. => none
  | .unary (.m0 .neg) a | .unary (.m0 .bnot) a | .unary (.m0 .pos) a | .unary .plus a =>
      rigidMax2 env elems a
  | .binary (.m0 .add) l r | .binary (.m0 .sub) l r | .binary (.m0 .and) l r
  | .binary (.m0 .or) l r | .binary (.m0 .xor) l r | .binary (.m0 .mul) l r
  | .binary .mul l r => maxW2 (rigidMax2 env elems l) (rigidMax2 env elems r)
  | .ternary _ t e => maxW2 (rigidMax2 env elems t) (rigidMax2 env elems e)
  | .resize _ a | .signedResize _ a | .cast _ a => rigidMax2 env elems a
  | e => selfWidth2 env elems e

/-- The operation width a context-determined binary operator needs beyond
its context (`instExpr2`'s `+ -` and `*` arms): the wider of the operands'
`rigidMax2`. -/
def ctxOpWidth2 (env : IEnv) (elems : List (String × Nat)) (l r : PExpr) : Option Nat :=
  maxW2 (rigidMax2 env elems l) (rigidMax2 env elems r)

/-- `e` (computed at width `ow`) brought to the context `ctx` — the
truncation of §11.8.2 when the operation was wider (`instExpr2`'s
invariant: under a context width the lowered expression is that wide). -/
@[simp] def ctxTrunc2 (ctx : Option Nat) (ow : Option Nat) (e : Expr2) : Expr2 :=
  match ctx, ow with
  | some w, some o => if o ≤ w then e else .resize w e
  | _, _ => e

@[simp] theorem ctxTrunc2_self (w : Nat) (e : Expr2) : ctxTrunc2 (some w) (some w) e = e := by
  simp

def fitDivOperand2 (signed : Bool) (context sourceWidth : Option Nat) (operand : Expr2) : Expr2 :=
  match context, sourceWidth with
  | some target, some source =>
      if target == source then operand
      else if signed then .resizeSigned target operand
      else .resize target operand
  | _, _ => operand

/-! ## The value tier: `instExpr2` -/

private def intLit2 (ctx : Option Nat) (v : Int) : Expr2 :=
  .lit (LVec.ofInt (ctx.getD 32) v)

/-- Expressions whose instantiated width is INTRINSIC (context-independent):
declared signals, sized literals, selects, concats, replications,
reductions — plus casts of such. Everything else is context-directed
(`Int`/`Fill`/parameter literals materialize at the context width;
arithmetic/ternary propagate it). A rigid operand in a wider/narrower
operator context needs an explicit `resize` (LRM §11.8.2 zero-extension /
truncation) — the `fitExpr2` wrapper below. -/
def rigidExpr : PExpr → Bool
  | .lit _ | .ident _ | .bitSel .. | .partSel .. | .concat _
  | .repl .. | .reduce .. | .arrayElem .. | .arrayPart .. => true
  | .cast _ a => rigidExpr a
  | _ => false

/-- Whether a `Squash2` operand's value depends on the context width: a
context-propagating operator (`PExpr.ctxPropagates`), seen through the
implicit conversions the envelope wraps around it (`Resize`,
`SignedResize`). A rigid operand (a signal, a select, a concatenation) is
the same at every context. -/
def PExpr.ctxSensitive : PExpr → Bool
  | .resize _ a | .signedResize _ a => a.ctxSensitive
  | e => e.ctxPropagates

/-- The message of a value-position read of a stale constant
(`IEnv.stale`, `PParam.overrideRetypes`). -/
def staleMsg2 (n : String) : String :=
  s!"'{n}' has no declared type and a default of another type: overridden by an integer it is an int (IEEE 1800-2023 §6.20.2), but the envelope's value-tier tree was typed at its default's type"

/-- A parameter, genvar or `$high`/`$size` reference: the operand of the
envelope's `Resize` marker of a signed simple operand in an unsigned
context (`_sym_unsigned_simple_operand`, round 3 folds). -/
def PExpr.constLeaf : PExpr → Bool
  | .paramRef .. | .genvarRef _ | .sysCall .. => true
  | _ => false

/-- **Where the oracles split** (round 3 folds): a NEGATIVE genvar widened
into an unsigned context beyond its 32 bits. Yosys 0.53, Verilator 5.042
and the LRM (§27.4: the loop's implicit localparam is an `integer`, a simple
operand converted to the unsigned context type before it is extended,
§11.8.2) zero-extend it — and so does the model for a parameter, where
Icarus 12.0 agrees — but Icarus 12.0 SIGN-extends a genvar (`a ^ g` with
`g = -1` and a 42-bit `a`: Icarus `~a`, Yosys `{a[41:32], ~a[31:0]}`). The
model refuses rather than pick one (`docs/sv-oracle-disagreements.md`,
"Refused where the oracles split"). `some g` names the first such genvar
under a `Resize` marker of `e` at the operation width `w`. -/
def PExpr.negGenvarWidened (env : IEnv) (w : Nat) : PExpr → Option String
  | .resize _ (.genvarRef g) =>
      match env.vals.lookup g with
      | some v => if v < 0 && 32 < w then some g else none
      | none => none
  | .unary _ a | .cast _ a => a.negGenvarWidened env w
  | .binary _ l r => (l.negGenvarWidened env w).orElse fun _ => r.negGenvarWidened env w
  | .ternary _ t e => (t.negGenvarWidened env w).orElse fun _ => e.negGenvarWidened env w
  | _ => none

/-- **A constant subexpression in a value position**, folded to `v` by
`evalInt` (round 3 folds). An INT-class tree keeps its unbounded value,
materialized at the context width by sign extension — the INT class is
signed, so a context it reaches unconverted is signed. Any other tree (one
holding a `Resize` marker of a signed simple operand in an unsigned
context, or typed parameters) is re-evaluated AT THE OPERATION WIDTH
`max(context, its own width)` with its own signedness (§11.8.2: the
operands are extended to the context first): `a + P * 2` with `int P = -3`
and a 42-bit `a` multiplies `zext(P)` by 2 at 42 bits (`2^33 - 6`), where
the self-width value `2^32 - 6` would drop the carry. Loud when that
evaluation fails. (The operation width is `max` of the two at THESE
parameters, so the evaluation happens there in every case — round 3 folds;
`evalInt` reads a root at its own width, round 4.) -/
def constAtCtx2 (env : IEnv) (ctx : Option Nat) (e : PExpr) (v : Int) : Expr2 :=
  if e.isInt env then intLit2 ctx v
  else
    match ctx, ctype env e with
    | some w, .ok (sw, s) =>
        match (if sw < w then e.negGenvarWidened env w else none) with
        | some g => .unsupported "GenvarRef:unsigned-extension" (negGenvarMsg g w)
        | none =>
            match evalAt env (max w sw, s) e with
            | .ok v' => intLit2 ctx v'
            | .error m => .unsupported "Constant:context" m
    | _, _ => intLit2 ctx v

/-- A `$signed(…)`/`signed'(…)` cast at the root (`fitExpr2`'s loud
widening guard). -/
@[simp] def PExpr.signedCast : PExpr → Bool
  | .cast s _ => s
  | _ => false

mutual
/-- Lower a value-position expression to `Expr2` at context width `ctx`.
Total: failures are loud `Expr2.unsupported` nodes, reached-sensitive. -/
def instExpr2 (env : IEnv) (elems : List (String × Nat)) (ctx : Option Nat) :
    PExpr → Expr2
  | .lit v => .lit v
  | .ident n => .ident n
  | .int v => intLit2 ctx v
  | .fill b =>
      match ctx with
      | some w => .lit (LVec.replicate w b)
      | none => .unsupported "Fill:width" "no context width for unbased-unsized literal"
  | .paramRef n none =>
      match env.vals.lookup n with
      | some v => intLit2 ctx v
      | none =>
          match env.nvals.lookup n with
          | some (v, _, _) =>
              -- A stale constant (`IEnv.stale`): its type here is not the one
              -- the envelope's tree around this read was elaborated at.
              if env.stale.contains n then .unsupported "ParamRef:override-type" (staleMsg2 n)
              else intLit2 ctx v
          | none => .unsupported "ParamRef:unbound" n
  | .paramRef n (some p) => .unsupported "ParamRef:package" s!"{p}::{n}"
  | .genvarRef n =>
      match env.vals.lookup n with
      | some v => intLit2 ctx v
      | none => .unsupported "GenvarRef:unbound" n
  | .enumRef ty mem _ =>
      match env.members.lookup (ty, mem) with
      | some v => .lit v
      | none => .unsupported "EnumRef:unknown" s!"{ty}::{mem}"
  | .unary op a =>
      match op with
      | .m0 .lnot => .unary .lnot (instExpr2 env elems none a)
      -- `- ~ +` are context-determined (§11.6.1): the operand is extended
      -- to the context (`fitExpr2` — a rigid operand narrower than the
      -- context at THESE parameters gets its `resize`; slang's tree only
      -- carries one where the DEFAULT point needed it), and an operand wider
      -- than the context is operated on at its own width and the result
      -- truncated (x bits above the context still collapse `-`).
      | .m0 uop =>
          match ctx with
          | some w =>
              let ow := (rigidMax2 env elems a).getD w
              if ow ≤ w then .unary uop (fitExpr2 env elems (some w) a)
              else .resize w (.unary uop (fitExpr2 env elems (some ow) a))
          | none => .unary uop (instExpr2 env elems (selfWidth2 env elems a) a)
      | .plus =>
          match ctx with
          | some w =>
              let ow := (rigidMax2 env elems a).getD w
              if ow ≤ w then .unary .pos (fitExpr2 env elems (some w) a)
              else .resize w (.unary .pos (fitExpr2 env elems (some ow) a))
          | none => .unary .pos (instExpr2 env elems (selfWidth2 env elems a) a)
      | .inc | .dec => .unsupported "UnaryExpression:incdec" ""
  | .binary op l r =>
      match op with
      -- The operation runs at the max of the context and its operands and
      -- the result is truncated back to the context (`ctxTrunc2`), so a
      -- lowered expression under a context width is exactly that wide.
      | .m0 (.pow signedBase signedExponent) =>
          let baseContext := maxW2 ctx (divOperandWidth2 env elems l)
          ctxTrunc2 ctx baseContext <| .binary (.pow signedBase signedExponent)
            (instDivOperand2 env elems signedBase baseContext l)
            (instDivOperand2 env elems signedExponent (divOperandWidth2 env elems r) r)
      | .m0 operator@(.shl signedLeft) | .m0 operator@(.shr signedLeft)
      | .m0 operator@(.ashl signedLeft) | .m0 operator@(.ashr signedLeft) =>
          let leftContext := maxW2 ctx (divOperandWidth2 env elems l)
          ctxTrunc2 ctx leftContext <| .binary operator (instDivOperand2 env elems signedLeft leftContext l)
            (instDivOperand2 env elems false (divOperandWidth2 env elems r) r)
      | .m0 .div | .m0 .sdiv | .m0 .rem | .m0 .srem =>
          let octx := maxW2 ctx
            (maxW2 (divOperandWidth2 env elems l) (divOperandWidth2 env elems r))
          ctxTrunc2 ctx octx <| .binary (match op with
            | .m0 .sdiv => .sdiv
            | .m0 .srem => .srem
            | .m0 .rem => .rem
            | _ => .div)
            (instDivOperand2 env elems (op == .m0 .sdiv || op == .m0 .srem) octx l)
            (instDivOperand2 env elems (op == .m0 .sdiv || op == .m0 .srem) octx r)
      -- Bitwise operators: each result bit depends on the same bit of each
      -- operand only, so narrowing a wider operand to the context first is
      -- exact (x bits included).
      | .m0 .and | .m0 .or | .m0 .xor =>
          let octx := match ctx with
            | some w => some w
            | none => maxW2 (selfWidth2 env elems l) (selfWidth2 env elems r)
          .binary (match op with | .m0 bop => bop | _ => .add)
            (fitExpr2 env elems octx l) (fitExpr2 env elems octx r)
      -- `+ -`: an operand WIDER than the context is NOT narrowed first — an
      -- x/z bit above the context collapses the whole sum (§11.4.3), so the
      -- operation runs at `ctxOpWidth2` and the result is truncated.
      | .m0 .add | .m0 .sub =>
          match ctx with
          | some w =>
              let ow := (ctxOpWidth2 env elems l r).getD w
              if ow ≤ w then
                .binary (match op with | .m0 bop => bop | _ => .add)
                  (fitExpr2 env elems (some w) l) (fitExpr2 env elems (some w) r)
              else
                .resize w (.binary (match op with | .m0 bop => bop | _ => .add)
                  (fitExpr2 env elems (some ow) l) (fitExpr2 env elems (some ow) r))
          | none =>
              let octx := maxW2 (selfWidth2 env elems l) (selfWidth2 env elems r)
              .binary (match op with | .m0 bop => bop | _ => .add)
                (fitExpr2 env elems octx l) (fitExpr2 env elems octx r)
      | .m0 .eq | .m0 .ne | .m0 .wildEq | .m0 .wildNe
      | .m0 .lt | .m0 .le | .m0 .gt | .m0 .ge =>
          let octx := maxW2 (selfWidth2 env elems l) (selfWidth2 env elems r)
          .binary (match op with | .m0 bop => bop | _ => .eq)
            (fitExpr2 env elems octx l) (fitExpr2 env elems octx r)
      | .slt | .sle | .sgt | .sge =>
          let octx := maxW2 (selfWidth2 env elems l) (selfWidth2 env elems r)
          .scmp (match op with
              | .slt => .lt | .sle => .le | .sgt => .gt | _ => .ge)
            (fitExpr2 env elems octx l) (fitExpr2 env elems octx r)
      | .land | .lor =>
          -- Operands are self-determined (§11.4.7), result 1 bit.
          .logical (op == .land)
            (instExpr2 env elems (selfWidth2 env elems l) l)
            (instExpr2 env elems (selfWidth2 env elems r) r)
      | _ =>
          match evalInt env (.binary op l r) with
          | .ok v =>
              if !env.stale.isEmpty && (PExpr.binary op l r).mentionsAny env.stale then
                .unsupported "ParamRef:override-type" "constant folded from a stale parameter"
              else constAtCtx2 env ctx (.binary op l r) v
          | .error e =>
              match op with
              | .m0 .mul | .mul =>
                  match ctx with
                  | some w =>
                      let ow := (ctxOpWidth2 env elems l r).getD w
                      if ow ≤ w then
                        .binary .mul (fitExpr2 env elems (some w) l) (fitExpr2 env elems (some w) r)
                      else
                        .resize w (.binary .mul (fitExpr2 env elems (some ow) l)
                          (fitExpr2 env elems (some ow) r))
                  | none =>
                      let octx := maxW2 (selfWidth2 env elems l) (selfWidth2 env elems r)
                      .binary .mul (fitExpr2 env elems octx l) (fitExpr2 env elems octx r)
              | _ => .unsupported s!"BinaryExpression:{op.sym}" e
  | .ternary c t e =>
      let actx := match ctx with
        | some w => some w
        | none => maxW2 (selfWidth2 env elems t) (selfWidth2 env elems e)
      .ternary (instExpr2 env elems none c)
        (fitExpr2 env elems actx t) (fitExpr2 env elems actx e)
  | .concat parts => .concat (instParts2 env elems parts).toArray
  | .resize w a =>
      -- Target width = the CONTEXT at the current parameters (the
      -- envelope's `w` is defaults-elaborated metadata, used only when
      -- no context width is known). Round 3 folds: a context-propagating
      -- operand (`PExpr.ctxPropagates`) under a context WIDER than its own
      -- width is lowered at the context — the default point's truncation
      -- is no conversion there (repro `sx`); a parameter/genvar marker
      -- (`_sym_unsigned_simple_operand`) no wider than the context is
      -- plain materialization (the same bits; wider, it is zero-extended
      -- from its own width, §11.8.2).
      match ctx, selfWidth2 env elems a with
      | some cw, some sw =>
          if sw < cw then
            if a.ctxPropagates then instExpr2 env elems (some cw) a
            else
              match (PExpr.resize w a).negGenvarWidened env cw with
              | some g => .unsupported "GenvarRef:unsigned-extension" (negGenvarMsg g cw)
              | none => .resize cw (instExpr2 env elems (some sw) a)
          else if a.constLeaf then instExpr2 env elems (some cw) a
          else .resize cw (instExpr2 env elems (some sw) a)
      | _, _ => .resize (ctx.getD w) (instExpr2 env elems (selfWidth2 env elems a) a)
  | .squash2 _ operand =>
      -- The 4-state to 2-state conversion at an assignment boundary
      -- (`Expr2.squash2`, the 2-state declaration tier). Its operand is
      -- lowered at its own self-determined width, EXCEPT where a WIDER
      -- context would change a context-directed operand's operation width
      -- (§11.8.2): `Squash2(w, Resize(w, a + b))` at a point where the
      -- target is wider than the operands carries the sum's carry, and the
      -- own-width lowering would drop it (the default-point fold of round 6,
      -- repro `vs_sqn`, now in the value tier). That corner is loud.
      match ctx, selfWidth2 env elems operand with
      | some cw, some sw =>
          if sw < cw && operand.ctxSensitive then
            .unsupported "Squash2:context"
              s!"a 2-state conversion of a context-directed operand ({sw} bits) under a wider context ({cw} bits): the operation width follows the context (IEEE 1800-2023 §11.8.2) and the own-width lowering would drop the carry"
          else .squash2 (instExpr2 env elems (some sw) operand)
      | _, _ => .squash2 (instExpr2 env elems (selfWidth2 env elems operand) operand)
  | .signedResize width operand =>
      .resizeSigned (ctx.getD width) (instExpr2 env elems (selfWidth2 env elems operand) operand)
  | .sysCall fn a =>
      match evalInt env (.sysCall fn a) with
      | .ok v => intLit2 ctx v
      | .error e => .unsupported "SysCall" e
  | .bitSel base idx =>
      match evalInt env (.bitSel base idx) with
      | .ok v =>  -- parameter-based select: a constant
          if !env.stale.isEmpty && base.mentionsAny env.stale then
            .unsupported "ParamRef:override-type" "select of a stale parameter"
          else intLit2 ctx v
      | .error _ =>
          match elemOf elems base with
          | none => .unsupported "BitSel:base" "select base outside the declared-signal tier"
          | some ew =>
              let base' := instExpr2 env elems (selfWidth2 env elems base) base
              match evalInt env idx with
              | .ok i =>
                  if 0 ≤ i then .slice base' (i.toNat * ew) ew
                  else .unsupported "BitSel:index" "negative constant index"
              | .error _ =>
                  .index base' (instExpr2 env elems (selfWidth2 env elems idx) idx) ew
  | .partSel base msb lsb =>
      match evalInt env (.partSel base msb lsb) with
      | .ok v =>  -- parameter-based part select: a constant
          if !env.stale.isEmpty && base.mentionsAny env.stale then
            .unsupported "ParamRef:override-type" "select of a stale parameter"
          else intLit2 ctx v
      | .error _ =>
          match elemOf elems base, evalInt env msb, evalInt env lsb with
          | some ew, .ok m, .ok l =>
              if 0 ≤ l && l ≤ m && (msb.isInt env || decide (m < 2 ^ 31)) then
                .slice (instExpr2 env elems (selfWidth2 env elems base) base)
                  (l.toNat * ew) (((m - l).toNat + 1) * ew)
              else .unsupported "PartSel:bounds" s!"[{m}:{l}]"
          | none, _, _ => .unsupported "PartSel:base" "select base outside the declared-signal tier"
          | _, .error e, _ | _, _, .error e => .unsupported "PartSel:bounds" e
  | .repl count arg =>
      match evalInt env count with
      | .ok n =>
          if 0 ≤ n then
            .repl n.toNat (instExpr2 env elems (selfWidth2 env elems arg) arg)
          else .unsupported "Repl:count" "negative replication count"
      | .error e => .unsupported "Repl:count" e
  | .reduce op arg =>
      .reduce op (instExpr2 env elems (selfWidth2 env elems arg) arg)
  | .cast _ a => instExpr2 env elems ctx a
  | .arrayElem n is => arrayElemRead env n is
  | .arrayPart n is mode a b =>
      -- A run-time base (`v[sel +: 4]`) is lowered at its own
      -- self-determined width (§11.5.1); every other base is static. The
      -- width picks the reading (`dynBaseRead`): below 32 bits unsigned, at
      -- 32 bits two's complement (what Icarus and Yosys both do), above 32
      -- loud (they disagree).
      match dynPartPlan env n is mode a b with
      | some (.ok (w, q, c)) =>
          match selfWidth2 env elems a with
          | some bw => dynBaseRead n w q c bw (instExpr2 env elems (some bw) a)
          | none => .unsupported "ArraySel:dynamic" "run-time part-select base of unknown width"
      | some (.error e) => .unsupported "ArraySel:dynamic" e
      | none => arrayPartRead env n is mode a b
  | .unsupported k t => .unsupported k t

/-- Concat parts are self-determined (unsized literals in concats are
illegal SV — loud via the `Fill` arm). -/
def instParts2 (env : IEnv) (elems : List (String × Nat)) : List PExpr → List Expr2
  | [] => []
  | p :: rest =>
      instExpr2 env elems (selfWidth2 env elems p) p :: instParts2 env elems rest

/-- Instantiate an operand at context width `ctx`, wrapping RIGID
expressions whose intrinsic width differs in an explicit `resize`
(zero-extension / truncation, LRM §11.8.2) — e.g. a 4-bit counter compared
against an unsized `0` extends to the comparison width. Context-directed
expressions take `ctx` unchanged. -/
def instDivOperand2 (env : IEnv) (elems : List (String × Nat))
    (signed : Bool) (ctx : Option Nat) : PExpr → Expr2
  | .unary (.m0 .lnot) operand =>
      fitDivOperand2 signed ctx (some 1)
        (.unary .lnot (instDivOperand2 env elems false (divOperandWidth2 env elems operand) operand))
  | .unary (.m0 operator) operand =>
      .unary operator
        (instDivOperand2 env elems signed (maxW2 ctx (divOperandWidth2 env elems operand)) operand)
  | .unary .plus operand =>
      .unary .pos
        (instDivOperand2 env elems signed (maxW2 ctx (divOperandWidth2 env elems operand)) operand)
  | .binary (.m0 (.pow _ signedExponent)) left right =>
      .binary (.pow signed signedExponent)
        (instDivOperand2 env elems signed (maxW2 ctx (divOperandWidth2 env elems left)) left)
        (instDivOperand2 env elems signedExponent (divOperandWidth2 env elems right) right)
  | .binary (.m0 operator@(.shl _)) left right
  | .binary (.m0 operator@(.shr _)) left right
  | .binary (.m0 operator@(.ashl _)) left right
  | .binary (.m0 operator@(.ashr _)) left right =>
      let shifted := match operator with | .ashr _ => .ashr signed | _ => operator
      .binary shifted
        (instDivOperand2 env elems signed (maxW2 ctx (divOperandWidth2 env elems left)) left)
        (instDivOperand2 env elems false (divOperandWidth2 env elems right) right)
  | .binary (.m0 operator) left right =>
      let own := maxW2 (divOperandWidth2 env elems left) (divOperandWidth2 env elems right)
      let comparison := match operator with
        | .eq | .ne | .wildEq | .wildNe | .lt | .le | .gt | .ge
        | .slt | .sle | .sgt | .sge => true
        | _ => false
      let common := if comparison then own else maxW2 ctx own
      let value := Expr2.binary operator
        (instDivOperand2 env elems signed common left) (instDivOperand2 env elems signed common right)
      if comparison then fitDivOperand2 signed ctx (some 1) value else value
  | .binary .mul left right =>
      let common := maxW2 ctx (maxW2 (divOperandWidth2 env elems left) (divOperandWidth2 env elems right))
      .binary .mul (instDivOperand2 env elems signed common left)
        (instDivOperand2 env elems signed common right)
  | .binary operator@.slt left right | .binary operator@.sle left right
  | .binary operator@.sgt left right | .binary operator@.sge left right =>
      let common := maxW2 (divOperandWidth2 env elems left) (divOperandWidth2 env elems right)
      fitDivOperand2 signed ctx (some 1)
        (.scmp (match operator with | .slt => .lt | .sle => .le | .sgt => .gt | _ => .ge)
          (instDivOperand2 env elems true common left) (instDivOperand2 env elems true common right))
  | .binary operator@.land left right | .binary operator@.lor left right =>
      fitDivOperand2 signed ctx (some 1)
        (.logical (operator == .land)
          (instDivOperand2 env elems false (divOperandWidth2 env elems left) left)
          (instDivOperand2 env elems false (divOperandWidth2 env elems right) right))
  | .resize width (.genvarRef g) =>
      -- A negative genvar zero-extended past 32 bits: the oracles split
      -- (`PExpr.negGenvarWidened`, round 3 folds).
      match (PExpr.resize width (.genvarRef g)).negGenvarWidened env
          ((ctx.orElse fun _ => some width).getD 0) with
      | some g' => .unsupported "GenvarRef:unsigned-extension"
          (negGenvarMsg g' ((ctx.orElse fun _ => some width).getD 0))
      | none => instDivOperand2 env elems false (ctx.orElse (fun _ => some width)) (.genvarRef g)
  | .resize width operand => instDivOperand2 env elems false (ctx.orElse (fun _ => some width)) operand
  | .signedResize width operand => instDivOperand2 env elems true (ctx.orElse (fun _ => some width)) operand
  | .ternary condition left right =>
      let common := maxW2 ctx (maxW2 (divOperandWidth2 env elems left) (divOperandWidth2 env elems right))
      .ternary (instDivOperand2 env elems false (divOperandWidth2 env elems condition) condition)
        (instDivOperand2 env elems signed common left) (instDivOperand2 env elems signed common right)
  | .concat parts =>
      fitDivOperand2 signed ctx (divOperandWidthSum2 env elems parts)
        (.concat (instDivParts2 env elems parts).toArray)
  | .reduce operator operand =>
      fitDivOperand2 signed ctx (some 1)
        (.reduce operator (instDivOperand2 env elems false (divOperandWidth2 env elems operand) operand))
  | .repl count operand =>
      match evalInt env count with
      | .ok amount =>
          if 0 ≤ amount then
            fitDivOperand2 signed ctx (divOperandWidth2 env elems (.repl count operand))
              (.repl amount.toNat (instDivOperand2 env elems false (divOperandWidth2 env elems operand) operand))
          else .unsupported "Repl:count" "negative replication count"
      | .error message => .unsupported "Repl:count" message
  | .cast _ operand =>
      let source := divOperandWidth2 env elems operand
      fitDivOperand2 signed ctx source (instDivOperand2 env elems false source operand)
  | operand =>
      let source := divOperandWidth2 env elems operand
      fitDivOperand2 signed ctx source (instExpr2 env elems (source.orElse (fun _ => ctx)) operand)

def instDivParts2 (env : IEnv) (elems : List (String × Nat)) : List PExpr → List Expr2
  | [] => []
  | operand :: rest =>
      instDivOperand2 env elems false (divOperandWidth2 env elems operand) operand :: instDivParts2 env elems rest

def fitExpr2 (env : IEnv) (elems : List (String × Nat)) (ctx : Option Nat)
    (e : PExpr) : Expr2 :=
  match ctx with
  | none => instExpr2 env elems none e
  | some tw =>
      if rigidExpr e then
        match selfWidth2 env elems e with
        | some sw =>
            if sw == tw then instExpr2 env elems (some sw) e
            -- A `$signed(…)` operand widened HERE (slang's tree has no
            -- conversion for it: the default point did not need one) would
            -- be sign-extended exactly when the whole expression is signed —
            -- not decidable from this node, so loud rather than zero-extended.
            else if sw < tw && e.signedCast then
              .unsupported "Resize:signed" s!"signed operand widened {sw} → {tw} at these parameters"
            else .resize tw (instExpr2 env elems (some sw) e)
        | none => instExpr2 env elems ctx e
      else instExpr2 env elems ctx e
end

/-! ## Targets, statements, processes -/

/-- Lower an assignment target: `(Lhs2, context width for the RHS)`.
Loud (`.error`) on non-constant part-select bounds, undeclared names, or
negative indices — the caller degrades to `Stmt2.unsupported`. -/
def instLhsLeaf2 (env : IEnv) (elems : List (String × Nat)) :
    PLhs → Except String (Lhs2 × Nat)
  | .ident n =>
      match env.widths.lookup n with
      | some w => .ok (.ident n, w)
      | none => .error s!"assignment target '{n}' undeclared"
  | .bitSel n idx =>
      match elems.lookup n with
      | none => .error s!"assignment target '{n}' undeclared"
      | some ew =>
          match evalInt env idx with
          | .ok i =>
              if 0 ≤ i then .ok (.slice n (i.toNat * ew) ew, ew)
              else .error "negative constant index"
          | .error _ =>
              .ok (.index n (instExpr2 env elems (selfWidth2 env elems idx) idx) ew, ew)
  | .partSel n msb lsb =>
      match elems.lookup n, evalInt env msb, evalInt env lsb with
      | some ew, .ok m, .ok l =>
          if 0 ≤ l && l ≤ m && (msb.isInt env || decide (m < 2 ^ 31)) then
            .ok (.slice n (l.toNat * ew) (((m - l).toNat + 1) * ew),
                 ((m - l).toNat + 1) * ew)
          else .error s!"bad part-select bounds [{m}:{l}]"
      | none, _, _ => .error s!"assignment target '{n}' undeclared"
      | _, .error e, _ | _, _, .error e => .error s!"part-select bound: {e}"
  | .concat _ => .error "nested continuous concatenation target"
  | .arrayElem n is => arrayElemTarget env n is
  | .arrayPart n is mode a b => arrayPartTarget env n is mode a b

/-- A concatenation-target leaf whose lowered window writes exactly its
declared width `w` (a whole signal, an in-range slice, an element select). -/
def concatLeafExact (env : IEnv) : Lhs2 → Nat → Bool
  | .ident n, w => env.widths.lookup n == some w
  | .slice _ _ sw, w => sw == w
  | .index _ _ ew, w => ew == w
  | .concat _, _ => false

def instLhs2 (env : IEnv) (elems : List (String × Nat)) :
    PLhs → Except String (Lhs2 × Nat)
  | .concat parts => do
      if parts.isEmpty then .error "empty continuous concatenation target"
      let lowered ← parts.mapM (instLhsLeaf2 env elems)
      -- Each leaf must write EXACTLY its declared width: the RHS is split by
      -- the resolved windows, so a clipped, no-op or sink-carrying leaf (a
      -- part select overhanging its vector at this parameter point) would
      -- shift every lower leaf's bits.
      if !lowered.all (fun (l, w) => concatLeafExact env l w) then
        .error "concatenation target leaf overhangs its vector at these parameters"
      let width := lowered.foldl (fun n (_, w) => n + w) 0
      return (.concat (lowered.map Prod.fst), width)
  | target => instLhsLeaf2 env elems target

/-- The width a plain `case` compares at (IEEE 1800-2023 §12.5): the widest
self-determined width among its subject and EVERY item expression, at the
current parameters — an unsized `-1` or `4` item is 32 bits wide, so a
narrower subject is zero-extended to it rather than the item truncated to
the subject (2026-10-28: `case (b) -1:` on a 2-bit `b` used to match
`b = 2'b11`, where no simulator does; the envelope's subject `Resize` carries
only the DEFAULT point's width). -/
def caseWidth2 (env : IEnv) (elems : List (String × Nat)) (subj : PExpr)
    (items : List (List PExpr × PStmt)) : Option Nat :=
  items.foldl
    (fun acc item => item.1.foldl (fun w p => maxW2 w (selfWidth2 env elems p)) acc)
    (selfWidth2 env elems subj)

mutual
/-- Lower a statement to `Stmt2`. -/
def instStmt2 (env : IEnv) (elems : List (String × Nat)) : PStmt → Stmt2
  | .blockingAssign t v =>
      .blockingAssign (.ident t) (fitExpr2 env elems (env.widths.lookup t) v)
  | .nbaAssign t v =>
      .nbaAssign (.ident t) (fitExpr2 env elems (env.widths.lookup t) v)
  | .blockingAssignL lhs v =>
      match instLhs2 env elems lhs with
      | .ok (l2, w) => .blockingAssign l2 (fitExpr2 env elems (some w) v)
      | .error e => .unsupported "AssignL" e
  | .nbaAssignL lhs v =>
      match instLhs2 env elems lhs with
      | .ok (l2, w) => .nbaAssign l2 (fitExpr2 env elems (some w) v)
      | .error e => .unsupported "AssignL" e
  | .ifStmt c th el =>
      .ifStmt (instExpr2 env elems none c) (instStmt2 env elems th)
        (match el with
         | some s => some (instStmt2 env elems s)
         | none => none)
  | .block body => .block (instStmts2 env elems body).toArray
  | .caseStmt subj items dflt inside check =>
      let sctx := caseWidth2 env elems subj items
      -- `case … inside` compares the subject with each item PAIRWISE
      -- (`==?`, §12.5.4/§11.4.13): one common width is exact only when no
      -- item is wider than the subject (loud otherwise; no Icarus oracle).
      if inside && sctx != selfWidth2 env elems subj then
        .unsupported "Case:inside-width"
          "a `case inside` item is wider than its subject at these parameters"
      else
        .caseStmt (fitExpr2 env elems sctx subj)
          (instItems2 env elems sctx items).toArray
          (match dflt with
           | some s => some (instStmt2 env elems s)
           | none => none)
          inside check
  | .unsupported k t => .unsupported k t

/-- Case items: patterns at the case's comparison width (`caseWidth2`),
bodies recursively. -/
def instItems2 (env : IEnv) (elems : List (String × Nat)) (sctx : Option Nat) :
    List (List PExpr × PStmt) → List CaseItem2
  | [] => []
  | (pats, body) :: rest =>
      .mk (instPats2 env elems sctx pats).toArray (instStmt2 env elems body)
        :: instItems2 env elems sctx rest

def instPats2 (env : IEnv) (elems : List (String × Nat)) (sctx : Option Nat) :
    List PExpr → List Expr2
  | [] => []
  | p :: rest => fitExpr2 env elems sctx p :: instPats2 env elems sctx rest

def instStmts2 (env : IEnv) (elems : List (String × Nat)) : List PStmt → List Stmt2
  | [] => []
  | s :: rest => instStmt2 env elems s :: instStmts2 env elems rest
end

/-- Lower a process to `Process2`. -/
def instProcess2 (env : IEnv) (elems : List (String × Nat)) : PProcess → Process2
  | .alwaysFF c b => .alwaysFF c (instStmt2 env elems b)
  | .alwaysPlain c b => .alwaysPlain c (instStmt2 env elems b)
  -- WP4 (2026-10-28): a body that reads a bit before writing it and writes
  -- it later on the same path is refused, loudly (`CombGuard2.lean`).
  | .alwaysComb b => combGuardProc (fun n => env.widths.lookup n) (instStmt2 env elems b)
  | .alwaysFFR c rn b => .alwaysFFR c rn (instStmt2 env elems b)
  | .assign t v =>
      match env.widths.lookup t with
      | some w => .assign (.ident t) (fitExpr2 env elems (some w) v)
      | none => .unsupported "Assign" s!"assign target '{t}' undeclared"
  | .assignL lhs v =>
      match instLhs2 env elems lhs with
      | .ok (l2, w) => .assign l2 (fitExpr2 env elems (some w) v)
      | .error e => .unsupported "AssignL" e
  | .unsupported k t => .unsupported k t

/-! ## Generate expansion (Process2 mirror of `Param.lean`'s) -/

mutual
def GenItem.expand2 (env : IEnv) (elems : List (String × Nat)) (iterFuel : Nat) :
    GenItem → Res (List Process2)
  | .process p => .ok [instProcess2 env elems p]
  | .unsupported k t => .ok [.unsupported k t]
  | .inst i => .ok [.unsupported "Instance"
      s!"module instance '{i.name}' of '{i.module}': flat instantiation (hierarchical designs instantiate through `PDesign.instantiateH`, Hier2.lean)"]
  | .genIf cond thenB elseB =>
      match evalInt env cond with
      | .error e => .unsupported s!"generate if: {e}"
      | .ok v =>
          if v != 0 then expandList2 env elems iterFuel thenB
          else expandList2 env elems iterFuel elseB
  | .genFor _label g initE bound step _rc body =>
      match evalInt env initE, stepDelta g step with
      | .ok i0, .ok δ => do
          let vs ← genvarSeq env g bound δ iterFuel i0
          expandIters2 env elems iterFuel g vs body
      | .error e, _ => .unsupported s!"generate for: {e}"
      | _, .error e => .unsupported s!"generate for: {e}"
  termination_by it => (sizeOf it, 0)
  decreasing_by all_goals (simp_wf; omega)

def expandList2 (env : IEnv) (elems : List (String × Nat)) (iterFuel : Nat) :
    List GenItem → Res (List Process2)
  | [] => .ok []
  | it :: rest => do
      let ps ← it.expand2 env elems iterFuel
      let qs ← expandList2 env elems iterFuel rest
      .ok (ps ++ qs)
  termination_by l => (sizeOf l, 0)
  decreasing_by all_goals (simp_wf; omega)

def expandIters2 (env : IEnv) (elems : List (String × Nat)) (iterFuel : Nat)
    (g : String) : List Int → List GenItem → Res (List Process2)
  | [], _ => .ok []
  | v :: vs, body => do
      let ps ← expandList2 (env.bindVal g v) elems iterFuel body
      let qs ← expandIters2 env elems iterFuel g vs body
      .ok (ps ++ qs)
  termination_by vs body => (sizeOf body, vs.length + 1)
  decreasing_by all_goals (simp_wf; omega)
end

/-! ## `instantiate2` -/

/-- The symbolic packed dimensions of every declaration with an explicit
dimension list — the source the `IEnv.dims` geometry table (`dimTable`) is
evaluated from (proofs pin envelope dimensions against it by `rfl`). -/
def packedDimsOf (decls : List PDecl) : List (String × List PDim) :=
  decls.filterMap fun pd =>
    match pd.type with
    | .packed ds _ => some (pd.name, ds)
    | _ => none

@[inherit_doc packedDimsOf]
def PDesign.packedDims (d : PDesign) : List (String × List PDim) := packedDimsOf d.decls

/-- The loud error design of the semantic tier. -/
def Design2.errorDesign (name msg : String) : Design2 :=
  { name, decls := #[], processes := #[.unsupported "Instantiate" msg] }

/-- Instantiate a parametric design at concrete parameter values into the
semantic tier (`Design2`). Same discipline as `PDesign.instantiate`:
loud `.unsupported` on bad parameters, `.timeout` on generate fuel; out-of-
tier constructs become in-design loud nodes, never silent. -/
def PDesign.instantiate2From (envI : IEnv) (d : PDesign) (args : List Int)
    (iterFuel : Nat := 4096) : Res Design2 :=
  if args.length != d.params.length then
    .unsupported s!"parameter arity: got {args.length}, want {d.params.length}"
  else do
    let env0 ← bindParamsRes envI d.params args
    let env1 ← bindLocals env0 d.localParams
    let env2 ← bindEnums env1 d.enums
    -- Declared widths of typed parameters/localparams (self-determined
    -- widths of ParamRefs in value positions; untyped = 32-bit int).
    let pws ← (d.params.map (fun p => (p.name, p.type?))
                ++ d.localParams.map (fun lp => (lp.name, lp.type?))).filterMapM
      fun (n, ty?) =>
        match ty? with
        | none => pure none
        | some ty =>
            match ty.width env2 with
            | .ok w => pure (some (n, w))
            | .error e => Res.unsupported s!"parameter '{n}' type: {e}"
    let env2 := { env2 with pwidths := pws }
    -- The packed-array geometry, evaluated ONCE in the declaration scope:
    -- no genvar bound during generate expansion reaches a declared range.
    let env2 := { env2 with dims := dimTable env2 d.decls }
    let decls ← buildDecls env2 d.decls
    let elems ← buildElems env2 d.decls
    let envP := { env2 with widths := decls.map fun dc => (dc.name, dc.width) }
    let gens ← expandList2 envP elems iterFuel d.generates
    .ok { name := d.name
          decls := decls.toArray
          processes :=
            ((d.processes.map (instProcess2 envP elems)) ++ gens
              ++ d.others.map fun (k, t) => Process2.unsupported k t).toArray }

/-- `instantiate2From` from the empty environment — THE semantic-tier
instantiation (`name.sem`, every proof): INT-class constants on the
unbounded fast path (`Param.lean`'s ledger). -/
def PDesign.instantiate2 (d : PDesign) (args : List Int) (iterFuel : Nat := 4096) :
    Res Design2 :=
  d.instantiate2From {} args iterFuel

/-- **The 32-bit `int` agreement check** at a parameter point: the design
`instantiate2` builds equals the one built with exact 32-bit `int`
arithmetic (`IEnv.int32`) — i.e. no INT-class parameter/localparam
expression leaves the 32-bit range on the way (`v[(N*N) >> 30 +: 4]` at
`N = 65536` wraps to `v[3:0]` in every simulator; the unbounded fast path
says `v[7:4]`). `false` = the proof-facing family describes a different
circuit than a simulator builds HERE: the differential runner and
`load_design_sv2` (at the defaults) refuse it, and a checker instantiating
a family at concrete parameters should too. Genvar and unsized-literal-only
arithmetic stays unbounded in both (recorded restriction). -/
def PDesign.int32Agrees (d : PDesign) (args : List Int) : Bool :=
  let F := PDesign.surfaceFuel args
  match d.instantiate2From {} args F, d.instantiate2From { int32 := true } args F with
  | .ok m₁, .ok m₂ =>
      m₁.decls.toList == m₂.decls.toList &&
        toString (repr m₁.processes) == toString (repr m₂.processes)
  | .unsupported a, .unsupported b => a == b
  | .timeout, .timeout => true
  | _, _ => false

/-- Total `Design2` family (the `load_design_sv2` binder encoding's
semantic-tier twin): errors collapse to the loud error design. -/
def PDesign.instantiateD2 (d : PDesign) (args : List Int) : Design2 :=
  match d.instantiate2 args (PDesign.surfaceFuel args) with
  | .ok m => m
  | .timeout => .errorDesign d.name "generate expansion fuel exhausted"
  | .unsupported msg => .errorDesign d.name msg

/-! ## Hand-built smoke: a mini ff_one (select writes from a generate
family), a case FSM, and an async-reset register — all three semantic-tier
mechanisms end-to-end under `run2`. -/

private def wm1' : PDim := ⟨.binary (.m0 .sub) (.paramRef "W" none) (.int 1), .int 0⟩

/-- `gen_or(W)`: `assign y[j] = a[j] | a[j+1]` for j < W-1 — select reads
AND select writes with genvar-constant indices, expanded structurally. -/
private def pGenOr : PDesign :=
  { name := "gen_or"
    params := [{ name := "W", default? := some (.int 4), resolved? := some 4 }]
    localParams := []
    enums := []
    decls := [
      { name := "a", type := .packed [wm1'] (some 4), isInput := true },
      { name := "y", type := .packed [wm1'] (some 4), isOutput := true }]
    processes := []
    generates := [
      .genFor (some "g") "j" (.int 0)
        (.binary .slt (.genvarRef "j")
          (.binary (.m0 .sub) (.paramRef "W" none) (.int 1)))
        (.unary .inc (.genvarRef "j")) (some 3)
        [.process (.assignL (.bitSel "y" (.genvarRef "j"))
          (.binary (.m0 .or)
            (.bitSel (.ident "a") (.genvarRef "j"))
            (.bitSel (.ident "a") (.binary (.m0 .add) (.genvarRef "j") (.int 1)))))]]
    others := [] }

#guard pGenOr.crossCheck == []
-- W=4: y[2:0] driven, y[3] undriven (stays x): a=1000 → y=x100.
#guard (Res.toOption (run2 (pGenOr.instantiateD2 [4]) σ_src 64
        [[("a", LVec.lit "1000")]])).map
        (fun tr => tr.map fun st => SvState.showSignal st "y")
      == some ["x100"]
-- Same family at W=8, nothing re-extracted: a=00010010 → y=x0011011.
#guard (Res.toOption (run2 (pGenOr.instantiateD2 [8]) σ_src 64
        [[("a", LVec.lit "00010010")]])).map
        (fun tr => tr.map fun st => SvState.showSignal st "y")
      == some ["x0011011"]

/-- `rcase(W)`: async-reset register + plain case over a 2-bit opcode —
`alwaysFFR`, `caseStmt`, dynamic `index` write, and `Fill` reset values
in one design. -/
private def pRcase : PDesign :=
  { name := "rcase"
    params := [{ name := "W", default? := some (.int 4), resolved? := some 4 }]
    localParams := []
    enums := []
    decls := [
      { name := "clk", type := .packed [] (some 1), isInput := true },
      { name := "rst_n", type := .packed [] (some 1), isInput := true },
      { name := "op", type := .packed [⟨.int 1, .int 0⟩] (some 2), isInput := true },
      { name := "i", type := .packed [⟨.int 1, .int 0⟩] (some 2), isInput := true },
      { name := "q", type := .packed [wm1'] (some 4), isOutput := true }]
    processes := [
      .alwaysFFR "clk" "rst_n"
        (.ifStmt (.unary (.m0 .lnot) (.ident "rst_n"))
          (.nbaAssign "q" (.fill .l0))
          (some (.caseStmt (.ident "op")
            [([.lit (.ofNat 2 1)], .nbaAssignL (.bitSel "q" (.ident "i")) (.lit (.ofNat 1 1))),
             ([.lit (.ofNat 2 2)], .nbaAssign "q" (.unary (.m0 .bnot) (.ident "q")))]
            (some (.nbaAssign "q" (.ident "q"))) false .none)))]
    generates := []
    others := [] }

#guard pRcase.crossCheck == []
-- reset, then set bit 2, then set bit 0, then invert; then an x index
-- write (no-op: q holds), then reset again mid-stream.
#guard (Res.toOption (run2 (pRcase.instantiateD2 [4]) σ_src 64
        [[("rst_n", LVec.lit "0"), ("op", LVec.ofNat 2 0), ("i", LVec.ofNat 2 0)],
         [("rst_n", LVec.lit "1"), ("op", LVec.ofNat 2 1), ("i", LVec.ofNat 2 2)],
         [("i", LVec.ofNat 2 0)],
         [("op", LVec.ofNat 2 2)],
         [("op", LVec.ofNat 2 1), ("i", LVec.lit "xx")],
         [("rst_n", LVec.lit "0")]])).map
        (fun tr => tr.map fun st => SvState.showSignal st "q")
      == some ["0000", "0100", "0101", "1010", "1010", "0000"]

-- Bad parameters stay loud on the semantic tier too.
#guard (match pRcase.instantiate2 [] with
        | .unsupported msg => msg == "parameter arity: got 0, want 1"
        | _ => false)
#guard run2 (pRcase.instantiateD2 []) σ_src 64 [[]]
        == .unsupported "unsupported process 'Instantiate'"

/-- Regression (2026-10-28, verifier row `va2` and `cs1`): a plain `case`
compares at the widest of its subject and items (§12.5). `case (b) -1:` on a
2-bit `b` compares at 32 bits, where `-1` is 32 ones and `b` is
zero-extended: no `b` matches (Icarus 12.0 and Yosys 0.53 agree); the item
`4` likewise never matches a 2-bit `b` (it used to match `b = 0`). -/
private def pCaseW : PDesign :=
  { name := "casew"
    params := []
    localParams := []
    enums := []
    decls := [
      { name := "b", type := .packed [⟨.int 1, .int 0⟩] (some 2), isInput := true },
      { name := "o", type := .packed [] (some 1), isOutput := true },
      { name := "p", type := .packed [] (some 1), isOutput := true }]
    processes := [
      .alwaysComb (.block [
        .caseStmt (.resize 32 (.ident "b"))
          [([.unary (.m0 .neg) (.int 1)], .blockingAssign "o" (.lit (.ofNat 1 1)))]
          (some (.blockingAssign "o" (.lit (.ofNat 1 0)))) false .none,
        .caseStmt (.resize 32 (.ident "b"))
          [([.int 4], .blockingAssign "p" (.lit (.ofNat 1 1)))]
          (some (.blockingAssign "p" (.lit (.ofNat 1 0)))) false .none])]
    generates := []
    others := [] }

#guard (Res.toOption (run2 (pCaseW.instantiateD2 []) σ_src 64
        [[("b", LVec.lit "11")], [("b", LVec.lit "00")]])).map
        (fun tr => tr.map fun st => (SvState.showSignal st "o", SvState.showSignal st "p"))
      == some [("0", "0"), ("0", "0")]

/-- Regression (cv32e40p_fifo `empty_o`, diff rows `fifo_d8_w32`/
`fifo_d4_w8` vs Xcelium AND Icarus): a DECLARED 1-bit parameter type
(`parameter bit P`) must give ParamRefs self-determined width 1.
The envelope used to drop 2-state/signed declared parameter types to
`type: null` (indistinguishable from implicit = 32-bit int), so
`(cnt == 0) & ~(P & push)` widened `~(P & push)` to 32 bits against the
1-bit `==` — a width-mismatched `&` whose x poisoned `empty_o` on every
cycle. The extractor now emits a width-only `PackedType` for such types
(`_param_width_type`); this design replays the shape at both `P` values. -/
private def pBitParam : PDesign :=
  { name := "bp"
    params := [{ name := "P", type? := some (.packed [] (some 1)),
                 default? := some (.lit (LVec.lit "0")), resolved? := some 0 }]
    localParams := []
    enums := []
    decls := [
      { name := "cnt", type := .packed [⟨.int 3, .int 0⟩] (some 4), isInput := true },
      { name := "push", type := .packed [] (some 1), isInput := true },
      { name := "e", type := .packed [] (some 1), isOutput := true }]
    processes := [
      .assign "e" (.binary (.m0 .and)
        (.binary (.m0 .eq) (.ident "cnt") (.int 0))
        (.unary (.m0 .bnot)
          (.binary (.m0 .and) (.paramRef "P" none) (.ident "push"))))]
    generates := []
    others := [] }

#guard pBitParam.crossCheck == []
-- P=0: e = (cnt == 0) — known at every row, never x (the pinned fact).
#guard (Res.toOption (run2 (pBitParam.instantiateD2 [0]) σ_src 64
        [[("cnt", LVec.ofNat 4 0), ("push", LVec.lit "1")],
         [("cnt", LVec.ofNat 4 3), ("push", LVec.lit "1")],
         [("cnt", LVec.ofNat 4 0), ("push", LVec.lit "0")]])).map
        (fun tr => tr.map fun st => SvState.showSignal st "e")
      == some ["1", "0", "1"]
-- P=1: the push side masks the empty flag (fall-through shape).
#guard (Res.toOption (run2 (pBitParam.instantiateD2 [1]) σ_src 64
        [[("cnt", LVec.ofNat 4 0), ("push", LVec.lit "1")],
         [("cnt", LVec.ofNat 4 0), ("push", LVec.lit "0")]])).map
        (fun tr => tr.map fun st => SvState.showSignal st "e")
      == some ["0", "1"]

/-! ## Packed-array select paths: label normalization, per-dimension range
checks, partial part selects (`arrayElemWindow`/`arrayPartGeom`) -/

/-- `m` is `[1:0][2:0][3:0]` (3-D, 24 bits); `q` is `[0:3][7:4]` (ascending
outer, non-zero-based inner, 16 bits). -/
private def arrEnv : IEnv :=
  { dims := [("m", [(1, 0), (2, 0), (3, 0)]), ("q", [(0, 3), (7, 4)]),
             ("v", [(7, 0)]), ("r", [(7, 4)]), ("u", [(0, 7)])]
    widths := [("m", 24), ("q", 16), ("v", 8), ("r", 4), ("u", 8), ("sel", 3), ("s32", 32),
               ("s40", 40)] }

private def lhsIs (r : Except String (Lhs2 × Nat)) (l : Lhs2) (w : Nat) : Bool :=
  match r with
  | .ok (l', w') => l' == l && w' == w
  | .error _ => false

-- 3-D strides: m[1][2] is the 4-bit element at 1*12 + 2*4; m[1][2][3] one bit.
#guard arrayElemRead arrEnv "m" [.int 1, .int 2] == .slice (.ident "m") 20 4
#guard arrayElemRead arrEnv "m" [.int 1, .int 2, .int 3] == .slice (.ident "m") 23 1
-- Per-dimension range: m[0][3] is out of [2:0] (never the flat m[1][0]).
#guard arrayElemRead arrEnv "m" [.int 0, .int 3] == .lit (LVec.xVec 4)
-- Ascending outer [0:3]: label 0 is the MSB element (offset 3).
#guard arrayElemRead arrEnv "q" [.int 0] == .slice (.ident "q") 12 4
-- Non-zero-based inner [7:4]: label 5 is offset 1.
#guard arrayElemRead arrEnv "q" [.int 3, .int 5] == .slice (.ident "q") 1 1
-- q[1][6:5]: element offset 2 (pb 8), bits 1..2 of it.
#guard arrayPartRead arrEnv "q" [.int 1] .range (.int 6) (.int 5) == .slice (.ident "q") 9 2
-- q[1:2] on the ascending outer dimension = q[1 +: 2] = elements 1..2 by offset.
#guard arrayPartRead arrEnv "q" [] .range (.int 1) (.int 2) == .slice (.ident "q") 4 8
#guard arrayPartRead arrEnv "q" [] .up (.int 1) (.int 2) == .slice (.ident "q") 4 8
#guard arrayPartRead arrEnv "q" [] .down (.int 2) (.int 2) == .slice (.ident "q") 4 8
-- A reversed [2:1] on the ascending dimension is loud.
#guard match arrayPartRead arrEnv "q" [] .range (.int 2) (.int 1) with
  | .unsupported "ArraySel" _ => true
  | _ => false
-- m[0][4:2] overhangs [2:0] on the msb side: x for elements 4..3, then m[0][2].
#guard arrayPartRead arrEnv "m" [.int 0] .range (.int 4) (.int 2) ==
  .concat #[.lit (LVec.xVec 8), .slice (.ident "m") 8 4]
-- Targets: in range, out of range (zero-width no-op), msb overhang clipped,
-- lsb overhang loud.
#guard lhsIs (arrayElemTarget arrEnv "m" [.int 1, .int 2]) (.slice "m" 20 4) 4
#guard lhsIs (arrayElemTarget arrEnv "m" [.int 0, .int 3]) (.slice "m" 0 0) 4
#guard lhsIs (arrayPartTarget arrEnv "m" [.int 0] .range (.int 4) (.int 2)) (.slice "m" 8 4) 12
-- m[0][1:-1] overhangs [2:0] on the LSB side: m[0][1:0] (bits 0..7) takes
-- RHS bits 11..4; RHS bits 3..0 land in the sink past m's msb (bit 24).
#guard lhsIs (arrayPartTarget arrEnv "m" [.int 0] .range (.int 1) (.int (-1)))
  (.concat [.slice "m" 0 8, .slice "m" 24 4]) 12
-- Too many selects for the declared dimensions is loud.
#guard match arrayElemRead arrEnv "q" [.int 0, .int 4, .int 0] with
  | .unsupported "ArraySel" _ => true
  | _ => false

/-- `arr2`: a `[1:0][3:0]` array written through select-path targets (a whole
row, two row part-selects, one out-of-range bit) and read back through
paths — the end-to-end `run2` smoke. -/
private def pArr2 : PDesign :=
  { name := "arr2"
    params := []
    localParams := []
    enums := []
    decls := [
      { name := "a", type := .packed [⟨.int 3, .int 0⟩] (some 4), isInput := true },
      { name := "m", type := .packed [⟨.int 1, .int 0⟩, ⟨.int 3, .int 0⟩] (some 8) },
      { name := "y", type := .packed [⟨.int 3, .int 0⟩] (some 4), isOutput := true },
      { name := "z", type := .packed [⟨.int 1, .int 0⟩] (some 2), isOutput := true }]
    processes := [
      .assignL (.arrayElem "m" [.int 0]) (.ident "a"),
      .assignL (.arrayPart "m" [.int 1] .range (.int 3) (.int 2))
        (.partSel (.ident "a") (.int 1) (.int 0)),
      .assignL (.arrayPart "m" [.int 1] .range (.int 1) (.int 0))
        (.partSel (.ident "a") (.int 3) (.int 2)),
      .assignL (.arrayElem "m" [.int 0, .int 5]) (.lit (LVec.ofNat 1 1)),
      .assign "y" (.arrayElem "m" [.int 1]),
      .assign "z" (.concat [.arrayElem "m" [.int 0, .int 4], .arrayElem "m" [.int 1, .int 3]])]
    generates := []
    others := [] }

#guard pArr2.crossCheck == []

/-- `gvcat(W)`: genvar-CONSTANT selects in self-determined positions —
`y[j] = a[j] ^ {j[0]}` and `z[j] = a[j] & ^{{2{j[0]}}, j[1]}`. A bit select
of a genvar is one bit (§11.5.1); before `selfWidth2` knew that, the
concat parts materialized as 32-bit literals and the gates read x.
Differential row `gvcat`. -/
private def pGvCat : PDesign :=
  { name := "gvcat"
    params := [{ name := "W", default? := some (.int 4), resolved? := some 4 }]
    localParams := []
    enums := []
    decls := [
      { name := "a", type := .packed [wm1'] (some 4), isInput := true },
      { name := "y", type := .packed [wm1'] (some 4), isOutput := true },
      { name := "z", type := .packed [wm1'] (some 4), isOutput := true }]
    processes := []
    generates := [
      .genFor (some "g") "j" (.int 0) (.binary .slt (.genvarRef "j") (.paramRef "W" none))
        (.unary .inc (.genvarRef "j")) (some 4)
        [.process (.assignL (.bitSel "y" (.genvarRef "j"))
          (.binary (.m0 .xor) (.bitSel (.ident "a") (.genvarRef "j"))
            (.concat [.bitSel (.genvarRef "j") (.int 0)]))),
         .process (.assignL (.bitSel "z" (.genvarRef "j"))
          (.binary (.m0 .and) (.bitSel (.ident "a") (.genvarRef "j"))
            (.reduce .xor (.concat [.repl (.int 2) (.bitSel (.genvarRef "j") (.int 0)),
              .bitSel (.genvarRef "j") (.int 1)]))))]]
    others := [] }

-- a = 0110: y = a ^ 1010 = 1100; z[j] = a[j] & j[1] = 0100.
#guard (Res.toOption (run2 (pGvCat.instantiateD2 [4]) σ_src 64
        [[("a", LVec.lit "0110")]])).map
        (fun tr => tr.map fun st => (SvState.showSignal st "y", SvState.showSignal st "z"))
      == some [("1100", "0100")]

/-- `gvshadow`: a generate loop whose genvar REUSES the name of the
parameter `K` in `m`'s declared range `[3:0][K:0]` (legal SV — slang,
Icarus and Yosys accept it). The range is the module's (`K = 2`, stride 3,
evaluated once by `dimTable`), so `m[1][0]` inside the loop is flat bit 3;
evaluating the range at the select site would read bit 2 (stride `K+1` at
the genvar's `K = 1`). Differential row `array_gvshadow`. -/
private def pGvShadow : PDesign :=
  { name := "gvshadow"
    params := [{ name := "K", default? := some (.int 2), resolved? := some 2 }]
    localParams := []
    enums := []
    decls := [
      { name := "src", type := .packed [⟨.int 11, .int 0⟩] (some 12), isInput := true },
      { name := "m", type := .packed [⟨.int 3, .int 0⟩, ⟨.paramRef "K" none, .int 0⟩] (some 12) },
      { name := "y", type := .packed [] (some 1), isOutput := true }]
    processes := [.assign "m" (.ident "src")]
    generates := [
      .genFor (some "g") "K" (.int 1) (.binary .slt (.genvarRef "K") (.int 2))
        (.unary .inc (.genvarRef "K")) (some 4)
        [.process (.assign "y" (.arrayElem "m" [.int 1, .int 0]))]]
    others := [] }

#guard (Res.toOption (run2 (pGvShadow.instantiateD2 [2]) σ_src 64
        [[("src", LVec.lit "000000001000")], [("src", LVec.lit "000000000100")]])).map
        (fun tr => tr.map fun st => SvState.showSignal st "y")
      == some ["1", "0"]
-- a = 0011: m[0] = 0011, m[1] = {a[1:0], a[3:2]} = 1100; m[0][5] writes
-- nothing; z = {m[0][4] (out of range: x), m[1][3]}.
#guard (Res.toOption (run2 (pArr2.instantiateD2 []) σ_src 64
        [[("a", LVec.lit "0011")], [("a", LVec.lit "1001")]])).map
        (fun tr => tr.map fun st =>
          (SvState.showSignal st "m", SvState.showSignal st "y", SvState.showSignal st "z"))
      == some [("11000011", "1100", "x1"), ("01101001", "0110", "x0")]

/-! ## Indexed part-selects: lsb-side overhang targets and run-time bases
(`arrayPartTarget`'s sink leaf, `dynPartPlan`/`dynPartRead`) -/

-- 1-D `v` is `[7:0]`. v[-2 +: 4] = v[1 -: 4] = labels 1..-2: v[1:0] takes the
-- RHS's bits 3..2, the low two RHS bits land in the sink past bit 7.
#guard lhsIs (arrayPartTarget arrEnv "v" [] .up (.int (-2)) (.int 4))
  (.concat [.slice "v" 0 2, .slice "v" 8 2]) 4
#guard lhsIs (arrayPartTarget arrEnv "v" [] .down (.int 1) (.int 4))
  (.concat [.slice "v" 0 2, .slice "v" 8 2]) 4
-- Both ends at once (v[-1 +: 10]): all of v, between the truncated RHS top
-- bit and the one-bit sink.
#guard lhsIs (arrayPartTarget arrEnv "v" [] .up (.int (-1)) (.int 10))
  (.concat [.slice "v" 0 8, .slice "v" 8 1]) 10
-- msb overhang (v[6 +: 4]) is the clipped window; fully below is a no-op.
#guard lhsIs (arrayPartTarget arrEnv "v" [] .up (.int 6) (.int 4)) (.slice "v" 6 2) 4
#guard lhsIs (arrayPartTarget arrEnv "v" [] .up (.int (-6)) (.int 4)) (.slice "v" 0 0) 4

private def dynPlanIs (r : Option (Except String (Nat × Nat × Nat))) (p : Nat × Nat × Nat) : Bool :=
  match r with
  | some (.ok p') => p' == p
  | _ => false

private def dynPlanLoud (r : Option (Except String (Nat × Nat × Nat))) : Bool :=
  match r with
  | some (.error _) => true
  | _ => false

-- Run-time bases: `+:` pads nothing below a zero-based range, `-:` pads
-- `w - 1`, a range `[7:4]` pads its lsb label (the shift amount IS the base).
#guard dynPlanIs (dynPartPlan arrEnv "v" [] .up (.ident "sel") (.int 4)) (4, 0, 8)
#guard dynPlanIs (dynPartPlan arrEnv "v" [] .down (.ident "sel") (.int 4)) (4, 3, 8)
#guard dynPlanIs (dynPartPlan arrEnv "r" [] .up
  (.binary (.m0 .mul) (.ident "sel") (.int 2)) (.int 2)) (2, 4, 4)
-- Out of the tier, loudly: an ascending range, a multi-dim array, a
-- non-positive width, a dynamic `[msb:lsb]`.
#guard dynPlanLoud (dynPartPlan arrEnv "u" [] .up (.ident "sel") (.int 2))
#guard dynPlanLoud (dynPartPlan arrEnv "m" [] .up (.ident "sel") (.int 2))
#guard dynPlanLoud (dynPartPlan arrEnv "v" [] .up (.ident "sel") (.int 0))
#guard dynPlanLoud (dynPartPlan arrEnv "v" [] .range (.ident "sel") (.int 0))
-- Not dynamic: a constant base, and a constant that only fails `evalInt`
-- (width-dependent `~3`) — both stay on the static path.
#guard (dynPartPlan arrEnv "v" [] .up (.int 3) (.int 4)).isNone
#guard (dynPartPlan arrEnv "v" [] .up (.unary (.m0 .bnot) (.int 3)) (.int 4)).isNone
-- Read lowering, and the loud forms on a read and on a target.
#guard instExpr2 arrEnv [] none (.arrayPart "v" [] .up (.ident "sel") (.int 4))
  == dynPartRead "v" 4 0 8 (.ident "sel")
#guard match instExpr2 arrEnv [] none (.arrayPart "u" [] .up (.ident "sel") (.int 2)) with
  | .unsupported "ArraySel:dynamic" _ => true
  | _ => false
#guard (arrayPartTarget arrEnv "v" [] .up (.ident "sel") (.int 4)).toOption.isNone
#guard selfWidth2 arrEnv [] (.arrayPart "v" [] .down (.ident "sel") (.int 4)) == some 4
-- The base's width picks the reading: a 32-bit base is two's complement
-- (`dynPartRead32`), a wider one is loud (Icarus and Yosys disagree).
#guard instExpr2 arrEnv [] none (.arrayPart "v" [] .up (.ident "s32") (.int 4))
  == dynPartRead32 "v" 4 0 8 (.ident "s32")
#guard match instExpr2 arrEnv [] none (.arrayPart "v" [] .up (.ident "s40") (.int 4)) with
  | .unsupported "ArraySel:dynamic" _ => true
  | _ => false
-- A constant label far outside the dimension (a 32-bit unsigned wrap such as
-- `UI - 1` at `UI = 0`: 2^32 - 1) is loud on a read and on a target, where
-- an ordinary overhang is modelled.
#guard match arrayPartRead arrEnv "v" [] .up (.int 4294967295) (.int 4) with
  | .unsupported "ArraySel:index-range" _ => true
  | _ => false
#guard (arrayPartTarget arrEnv "v" [] .up (.int 4294967295) (.int 4)).toOption.isNone
#guard match arrayPartRead arrEnv "v" [] .up (.int 6) (.int 4) with
  | .concat _ => true
  | _ => false
-- A concatenation-target leaf must write exactly its declared width: an
-- overhanging part (`r[6 +: 4]` on `[7:4]` clips to 2 bits) is refused there
-- rather than shifting the RHS split; an in-range one is admitted.
#guard (instLhs2 arrEnv [] (.concat [.ident "v", .arrayPart "r" [] .up (.int 6) (.int 4)])).toOption.isNone
#guard lhsIs (instLhs2 arrEnv [] (.concat [.ident "v", .arrayPart "r" [] .up (.int 4) (.int 2)]))
  (.concat [.ident "v", .slice "r" 0 2]) 10

/-- `dynpart`: run-time indexed part-select READS (`v[sel +: 4]` and
`v[sel -: 4]` over `[7:0]`, `r[sel +: 2]` over `[7:4]`) and a constant-base
TARGET overhanging the lsb (`w[-2 +: 4] = b` in an always_comb). The pinned
values are what Icarus 12.0 prints for the same SystemVerilog (x/z base:
all x; out-of-range bits: x; the overhanging write lands `b[3:2]` in
`w[1:0]`); the envelope-level twin is row `partsel`. -/
private def pDynPart : PDesign :=
  { name := "dynpart"
    params := []
    localParams := []
    enums := []
    decls := [
      { name := "v", type := .packed [⟨.int 7, .int 0⟩] (some 8), isInput := true },
      { name := "r", type := .packed [⟨.int 7, .int 4⟩] (some 4), isInput := true },
      { name := "sel", type := .packed [⟨.int 2, .int 0⟩] (some 3), isInput := true },
      { name := "b", type := .packed [⟨.int 3, .int 0⟩] (some 4), isInput := true },
      { name := "du", type := .packed [⟨.int 3, .int 0⟩] (some 4), isOutput := true },
      { name := "dd", type := .packed [⟨.int 3, .int 0⟩] (some 4), isOutput := true },
      { name := "dr", type := .packed [⟨.int 1, .int 0⟩] (some 2), isOutput := true },
      { name := "w", type := .packed [⟨.int 7, .int 0⟩] (some 8), isOutput := true }]
    processes := [
      .assign "du" (.arrayPart "v" [] .up (.ident "sel") (.int 4)),
      .assign "dd" (.arrayPart "v" [] .down (.ident "sel") (.int 4)),
      .assign "dr" (.arrayPart "r" [] .up (.ident "sel") (.int 2)),
      .alwaysComb (.block [.blockingAssign "w" (.fill .l0),
        .blockingAssignL (.arrayPart "w" [] .up (.int (-2)) (.int 4)) (.ident "b")])]
    generates := []
    others := [] }

#guard pDynPart.crossCheck == []
#guard (Res.toOption (run2 (pDynPart.instantiateD2 []) σ_src 64
        [[("v", LVec.lit "10110100"), ("r", LVec.lit "1001"), ("b", LVec.lit "1011"),
          ("sel", LVec.ofNat 3 0)],
         [("sel", LVec.ofNat 3 3)], [("sel", LVec.ofNat 3 5)], [("sel", LVec.ofNat 3 7)],
         [("sel", LVec.lit "x1x")]])).map
        (fun tr => tr.map fun st =>
          (SvState.showSignal st "du", SvState.showSignal st "dd",
           SvState.showSignal st "dr", SvState.showSignal st "w"))
      == some [("0100", "0xxx", "xx", "00000010"), ("0110", "0100", "1x", "00000010"),
               ("x101", "1101", "00", "00000010"), ("xxx1", "1011", "x1", "00000010"),
               ("xxxx", "xxxx", "xx", "00000010")]

/-- `dyn32`: 32-bit run-time bases (`v[s - 2 +: 4]` and `v[s - 2 -: 4]`, `s`
4 bits: the unsized `2` makes the base `Resize32(s) - 2`, 32-bit unsigned)
read as two's complement, as Icarus 12.0 and Yosys 0.53 both do (verifier
probe `pa.sv`, `v = 10110111`: `s = 0` gives `11xx`). Envelope twin: rows
`dyn32_*`. -/
private def pDyn32 : PDesign :=
  { name := "dyn32"
    params := []
    localParams := []
    enums := []
    decls := [
      { name := "v", type := .packed [⟨.int 7, .int 0⟩] (some 8), isInput := true },
      { name := "s", type := .packed [⟨.int 3, .int 0⟩] (some 4), isInput := true },
      { name := "du", type := .packed [⟨.int 3, .int 0⟩] (some 4), isOutput := true },
      { name := "dd", type := .packed [⟨.int 3, .int 0⟩] (some 4), isOutput := true }]
    processes := [
      .assign "du" (.arrayPart "v" [] .up
        (.binary (.m0 .sub) (.resize 32 (.ident "s")) (.int 2)) (.int 4)),
      .assign "dd" (.arrayPart "v" [] .down
        (.binary (.m0 .sub) (.resize 32 (.ident "s")) (.int 2)) (.int 4))]
    generates := []
    others := [] }

#guard (Res.toOption (run2 (pDyn32.instantiateD2 []) σ_src 64
        [[("v", LVec.lit "10110111"), ("s", LVec.ofNat 4 0)],
         [("s", LVec.ofNat 4 1)], [("s", LVec.ofNat 4 2)], [("s", LVec.ofNat 4 9)],
         [("s", LVec.ofNat 4 15)], [("s", LVec.lit "x001")]])).map
        (fun tr => tr.map fun st => (SvState.showSignal st "du", SvState.showSignal st "dd"))
      == some [("11xx", "xxxx"), ("111x", "xxxx"), ("0111", "1xxx"), ("xxx1", "1011"),
               ("xxxx", "xxxx"), ("xxxx", "xxxx")]

/-! ## Width and typing at non-default parameter points (2026-10-28)

`-a`/`~a` extend a narrower operand to the context before the operator; `+`
with an operand wider than the context runs at the operand's width (an x
bit above the context collapses the sum) and is truncated. An untyped
parameter with a sized default (`parameter P = 3'd5`) has the default's
type at the default point (`atPoint`) and is loud in value positions where
an integer override retypes it; INT arithmetic leaving 32 bits is caught by
`int32Agrees`. -/

private def pCtx : PDesign :=
  { name := "ctx"
    params := [{ name := "N", default? := some (.int 4), resolved? := some 4,
                 type? := some (.packed [⟨.int 31, .int 0⟩] (some 32)) }]
    localParams := []
    enums := []
    decls := [
      { name := "a", type := .packed [⟨.binary (.m0 .sub) (.paramRef "N" none) (.int 1), .int 0⟩] none,
        isInput := true },
      { name := "v", type := .packed [⟨.int 7, .int 0⟩] (some 8), isInput := true },
      { name := "on", type := .packed [⟨.int 3, .int 0⟩] (some 4), isOutput := true },
      { name := "oa", type := .packed [⟨.int 3, .int 0⟩] (some 4), isOutput := true }]
    processes := [
      .assign "on" (.unary (.m0 .neg) (.ident "a")),
      .assign "oa" (.binary (.m0 .add) (.arrayPart "v" [] .up (.int 1) (.paramRef "N" none))
        (.lit (LVec.ofNat 4 9)))]
    generates := []
    others := [] }

-- N = 2: `-a` is computed at 4 bits (`a = 10` gives `1110`, not `0010`).
#guard (Res.toOption (run2 (pCtx.instantiateD2 [2]) σ_src 64
        [[("a", LVec.lit "10"), ("v", LVec.lit "00000000")]])).map
        (fun tr => tr.map fun st => SvState.showSignal st "on") == some ["1110"]
-- N = 8: `v[1 +: 8]` reads x at bit 8, which collapses the 8-bit sum.
#guard (Res.toOption (run2 (pCtx.instantiateD2 [8]) σ_src 64
        [[("a", LVec.lit "00000000"), ("v", LVec.lit "10010001")]])).map
        (fun tr => tr.map fun st => SvState.showSignal st "oa") == some ["xxxx"]
-- N = 4 (equal widths): exactly the unchanged lowering.
#guard match pCtx.instantiate2 [4] with
  | .ok m => toString (repr m.processes.toList) ==
      toString (repr [Process2.assign (.ident "on") (.unary .neg (.ident "a")),
        Process2.assign (.ident "oa") (.binary .add (.slice (.ident "v") 1 4) (.lit (LVec.ofNat 4 9)))])
  | _ => false

private def pStale : PDesign :=
  { name := "stale"
    params := [{ name := "P", default? := some (.lit (LVec.ofNat 3 5)), resolved? := some 5 }]
    localParams := []
    enums := []
    decls := [{ name := "o", type := .packed [⟨.int 3, .int 0⟩] (some 4), isOutput := true }]
    processes := [.assign "o" (.paramRef "P" none)]
    generates := []
    others := [] }

-- The untyped `P = 3'd5` is retyped at its default point (3-bit unsigned)…
#guard match pStale.atPoint [] with
  | .ok (d, args) => args == [5] && d.params.map (·.type?.isSome) == [true]
  | .error _ => false
#guard pStale.markOverrideRetypes.params.map (·.overrideRetypes) == [true]
-- …reads normally there, and loudly where an integer override retypes it.
private def staleReads (r : Res Design2) : Nat :=
  match r with
  | .ok m => ((toString (repr m.processes.toList)).splitOn "ParamRef:override-type").length - 1
  | _ => 99
#guard match pStale.markOverrideRetypes.atPoint [] with
  | .ok (d, args) => staleReads (d.instantiate2 args) == 0
  | .error _ => false
#guard staleReads (pStale.markOverrideRetypes.instantiate2 [5]) == 1
#guard staleReads (pStale.instantiate2 [5]) == 0  -- unmarked: the bare int reading

private def pOvf : PDesign :=
  { name := "ovf"
    params := [{ name := "N", default? := some (.int 4), resolved? := some 4,
                 type? := some (.packed [⟨.int 31, .int 0⟩] (some 32)) }]
    localParams := []
    enums := []
    decls := [{ name := "o", type := .packed [⟨.int 3, .int 0⟩] (some 4), isOutput := true }]
    processes := [.assign "o" (.binary .shr (.binary .mul (.paramRef "N" none)
      (.paramRef "N" none)) (.int 30))]
    generates := []
    others := [] }

-- `(N*N) >> 30`: no 32-bit overflow at N = 4; at N = 65536 the product
-- wraps to 0 in every simulator but not on the unbounded fast path.
#guard pOvf.int32Agrees [4]
#guard !pOvf.int32Agrees [65536]

/-! ### Round 3 folds (2026-10-28) -/

private def nm1 : PExpr := .binary (.m0 .add) (.paramRef "N" none) (.int 1)

/-- `a + P` (with the same-width marker), `a + P * 2`, `c = a + b`
(truncated at the default point) and `a ^ g` with a genvar `g`. -/
private def pFold : PDesign :=
  { name := "fold"
    params := [{ name := "N", default? := some (.int 7), resolved? := some 7,
                 type? := some (.packed [⟨.int 31, .int 0⟩] (some 32)) },
               { name := "P", default? := some (.unary (.m0 .neg) (.int 3)), resolved? := some (-3),
                 type? := some (.packed [⟨.int 31, .int 0⟩] (some 32)) }]
    localParams := []
    enums := []
    decls := [
      { name := "a", type := .packed [⟨nm1, .int 0⟩] none, isInput := true },
      { name := "b", type := .packed [⟨.int 3, .int 0⟩] (some 4), isInput := true },
      { name := "o1", type := .packed [⟨nm1, .int 0⟩] none, isOutput := true },
      { name := "o5", type := .packed [⟨nm1, .int 0⟩] none, isOutput := true },
      { name := "c", type := .packed [⟨.binary (.m0 .sub) (.paramRef "N" none) (.int 1), .int 0⟩] none,
        isOutput := true },
      { name := "o7", type := .packed [⟨nm1, .int 0⟩] none, isOutput := true }]
    processes := [
      .assign "o1" (.resize 9 (.binary (.m0 .add) (.resize 32 (.ident "a"))
        (.resize 32 (.paramRef "P" none)))),
      .assign "o5" (.resize 9 (.binary (.m0 .add) (.resize 32 (.ident "a"))
        (.binary (.m0 .mul) (.resize 32 (.paramRef "P" none)) (.int 2)))),
      .assign "c" (.resize 7 (.binary (.m0 .add) (.ident "b") (.ident "b")))]
    generates := [.genFor none "g" (.unary (.m0 .neg) (.int 1))
      (.binary .slt (.genvarRef "g") (.int 0)) (.unary .inc (.genvarRef "g")) none
      [.process (.assign "o7" (.resize 9 (.binary (.m0 .xor) (.resize 32 (.ident "a"))
        (.resize 32 (.genvarRef "g")))))]]
    others := [] }

/-- One run of `pFold` (without its genvar loop, which is loud at a point
wider than 32 bits — `gen`) at `N = n`. -/
private def foldRun (n : Int) (a b : String) (sig : String) (gen : Bool := false) :
    Option (List String) :=
  let d := if gen then pFold else { pFold with generates := [] }
  (Res.toOption (run2 (d.instantiateD2 [n, -3]) σ_src 64
    [[("a", LVec.lit a), ("b", LVec.lit b)]])).map (·.map fun st => SvState.showSignal st sig)

private def ones (n : Nat) : String := String.ofList (List.replicate n '1')
private def zeros (n : Nat) : String := String.ofList (List.replicate n '0')

-- N = 7 (`a` is `[N+1:0]`, 9 bits; a 32-bit context): `a + P` at a = 0 is
-- -3 truncated to 9 bits.
#guard foldRun 7 (zeros 9) "0000" "o1" == some ["111111101"]
-- N = 40 (42 bits): `P` is zero-extended (§11.8.2): `a + P` at a = 0 is
-- 2^32 - 3, `a + P * 2` is (2^32 - 3) * 2 = 2^33 - 6 at the 42-bit width.
#guard foldRun 40 (zeros 42) "0000" "o1" == some [zeros 10 ++ ones 30 ++ "01"]
#guard foldRun 40 (zeros 42) "0000" "o5" == some [zeros 9 ++ ones 30 ++ "010"]
-- `c = b + b` (4-bit operands into `[N-1:0]`): truncated at N = 3, the
-- carry kept at N = 8.
#guard foldRun 3 (zeros 5) "1111" "c" == some ["110"]
#guard foldRun 8 (zeros 10) "1111" "c" == some ["00011110"]
-- The negative genvar: agreed by every tool up to 32 bits, refused beyond.
#guard foldRun 7 (zeros 9) "0000" "o7" (gen := true) == some [ones 9]
#guard (pFold.instantiateD2 [40, -3]).hasUnsupported
#guard !({ pFold with generates := [] }.instantiateD2 [40, -3]).hasUnsupported

/-- `$high`/`$size` of declared signals at a point (`dimQuery`). -/
private def qEnv : IEnv :=
  { dims := [("v", [(-1, 0)]), ("u", [(7, 4)]), ("m", [(3, 0), (5, 0)])] }

#guard (evalInt qEnv (.sysCall .high (.ident "u"))).toOption == some 7
#guard (evalInt qEnv (.sysCall .high (.ident "v"))).toOption == some 0
#guard (evalInt qEnv (.sysCall .size (.ident "v"))).toOption == some 2
#guard (evalInt qEnv (.sysCall .size (.ident "m"))).toOption == some 4
#guard (evalInt qEnv (.sysCall .high (.ident "x"))).toOption.isNone

/-- A select of a parameter with a parameter-dependent range: exact while it
is `[m:0]`, `m ≥ 0`, loud elsewhere (`paramSelectOk`). -/
private def psEnv (lr : Int × Int) : IEnv :=
  { nvals := [("P", (3, (lr.1 - lr.2).natAbs + 1, false))], pdims := [("P", [lr])] }

#guard (evalInt (psEnv (3, 0)) (.bitSel (.paramRef "P" none) (.int 1))).toOption == some 1
#guard (evalInt (psEnv (-1, 0)) (.bitSel (.paramRef "P" none) (.int 1))).toOption.isNone
#guard (evalInt (psEnv (0, 0)) (.bitSel (.paramRef "P" none) (.int 1))).toOption.isNone
#guard (evalInt (psEnv (3, 0)) (.partSel (.paramRef "P" none) (.int 1) (.int 0))).toOption == some 3

end LeanModels.Sv
