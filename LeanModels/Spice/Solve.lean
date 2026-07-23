import LeanModels.Spice.Semantics

/-!
# Exact linear-DC MNA solver

The solver assembles the modified nodal-analysis system over `Rat` and runs a
total Gauss-Jordan elimination.  Its result is checked against the definitional
`Satisfies` predicate before it is exposed.  Consequently `solve_satisfies`
depends only on the checker, not on trusting the matrix assembly or eliminator.

Unknowns are the non-ground node voltages followed by voltage-source and
inductor branch currents.  KCL stamping follows `currentInto`: branch currents
enter `n1` with coefficient `-1` and enter `n2` with coefficient `1`.
-/

namespace LeanModels.Spice

/-- An MNA unknown is either a non-ground voltage or a named branch current. -/
inductive Unknown where
  | voltage (node : String)
  | current (name : String)
deriving Repr, BEq, DecidableEq, Inhabited

@[simp] theorem Unknown.beq_voltage_voltage (left right : String) :
    ((Unknown.voltage left == Unknown.voltage right) : Bool) = (left == right) := rfl

@[simp] theorem Unknown.beq_current_current (left right : String) :
    ((Unknown.current left == Unknown.current right) : Bool) = (left == right) := rfl

@[simp] theorem Unknown.beq_voltage_current (left right : String) :
    ((Unknown.voltage left == Unknown.current right) : Bool) = false := rfl

@[simp] theorem Unknown.beq_current_voltage (left right : String) :
    ((Unknown.current left == Unknown.voltage right) : Bool) = false := rfl

/-- Loud failures from validation, elimination, or the final semantic check. -/
inductive SolveError where
  | zeroResistance (name : String)
  | duplicateBranchName (name : String)
  | singular (column : Nat) (unknown : Option Unknown := none)
  | candidateRejected
deriving Repr, BEq, DecidableEq, Inhabited

/-- Human-readable solver failure, including the first unconstrained MNA
unknown when elimination can identify it. -/
def SolveError.describe : SolveError → String
  | .zeroResistance name => s!"zero resistance in '{name}'"
  | .duplicateBranchName name => s!"duplicate branch-current name '{name}'"
  | .singular column (some (.voltage node)) =>
      s!"singular MNA system at column {column}: unconstrained voltage '{node}'"
  | .singular column (some (.current name)) =>
      s!"singular MNA system at column {column}: unconstrained branch current '{name}'"
  | .singular column none => s!"singular MNA system at column {column}"
  | .candidateRejected => "the computed candidate does not satisfy the circuit equations"

/-- A square linear system `A x = b`, stored as augmented rows `[A | b]`. -/
structure LinearSystem where
  unknowns : List Unknown
  rows : List (List Rat)
deriving Repr, BEq, Inhabited

/-- Finite, decidable output of exact elimination. Unlike `Assignment`, this
data has decidable equality and can therefore be embedded in generated proof
artifacts. -/
structure Solution where
  unknowns : List Unknown
  values : List Rat
deriving Repr, BEq, DecidableEq, Inhabited

def Unknown.describe : Unknown → String
  | .voltage node => s!"V({node})"
  | .current name => s!"I({name})"

/-- Exact operating-point table for interactive inspection. -/
def Solution.describe (solution : Solution) : String :=
  solution.unknowns.zip solution.values
    |>.map (fun (unknown, value) => s!"{unknown.describe} = {value}")
    |> String.intercalate "\n"

private def nonGroundNodes (netlist : FlatNetlist) : List String :=
  netlist.nodes.filter (· != "0")

private def unknowns (netlist : FlatNetlist) : List Unknown :=
  (nonGroundNodes netlist).map .voltage ++ netlist.branchNames.map .current

private def duplicate? [BEq α] : List α → Option α
  | [] => none
  | x :: xs => if xs.contains x then some x else duplicate? xs

private def validate (netlist : FlatNetlist) : Except SolveError Unit := do
  for element in netlist.elements do
    if element.kind == .resistor && element.value == 0 then
      throw (.zeroResistance element.name)
  if let some name := duplicate? netlist.branchNames then
    throw (.duplicateBranchName name)

private def coefficient (unknown : Unknown) (element : Element)
    (node : String) : Rat :=
  match unknown, element.kind with
  | .voltage sought, .resistor =>
      if sought == element.n1 then
        if node == element.n1 then -(1 / element.value)
        else if node == element.n2 then 1 / element.value else 0
      else if sought == element.n2 then
        if node == element.n1 then 1 / element.value
        else if node == element.n2 then -(1 / element.value) else 0
      else 0
  | .current sought, .vsource | .current sought, .inductor =>
      if sought == element.name then
        if node == element.n1 then -1 else if node == element.n2 then 1 else 0
      else 0
  | _, _ => 0

private def kclCoefficient (netlist : FlatNetlist) (unknown : Unknown)
    (node : String) : Rat :=
  netlist.elements.foldl (fun total element =>
    total + coefficient unknown element node) 0

private def kclRhs (netlist : FlatNetlist) (node : String) : Rat :=
  netlist.elements.foldl (fun total element =>
    if element.kind == .isource then
      if node == element.n1 then total + element.value
      else if node == element.n2 then total - element.value
      else total
    else total) 0

private def deviceCoefficient (unknown : Unknown) (element : Element) : Rat :=
  match unknown with
  | .voltage node =>
      if node == element.n1 then 1 else if node == element.n2 then -1 else 0
  | .current _ => 0

private def deviceRow (us : List Unknown) (element : Element) : List Rat :=
  us.map (deviceCoefficient · element) ++
    [if element.kind == .vsource then element.value else 0]

/-- Assemble the exact rational MNA equations in deterministic support order. -/
def assemble (netlist : FlatNetlist) : LinearSystem :=
  let us := unknowns netlist
  let kclRows := nonGroundNodes netlist |>.map fun node =>
    us.map (kclCoefficient netlist · node) ++ [kclRhs netlist node]
  let lawRows := netlist.elements.toList.filterMap fun element =>
    match element.kind with
    | .vsource | .inductor => some (deviceRow us element)
    | _ => none
  { unknowns := us, rows := kclRows ++ lawRows }

/-- Exact augmented MNA system for interactive inspection. -/
def LinearSystem.describe (system : LinearSystem) : String :=
  let header := system.unknowns.map Unknown.describe |> String.intercalate ", "
  let rows := system.rows.map fun row =>
    match row.reverse with
    | [] => "[]"
    | rhs :: reversedCoefficients =>
        let coefficients := reversedCoefficients.reverse.map toString
          |> String.intercalate ", "
        s!"[{coefficients}] = {rhs}"
  String.intercalate "\n" (s!"unknowns: {header}" :: rows)

private def replaceAt (xs : List α) (index : Nat) (value : α) : List α :=
  xs.take index ++ value :: xs.drop (index + 1)

private def swapAt (xs : List α) (left right : Nat) : List α :=
  match xs[left]?, xs[right]? with
  | some x, some y => replaceAt (replaceAt xs left y) right x
  | _, _ => xs

private def findPivot (rows : List (List Rat)) (column : Nat) : Nat → Option Nat
  | row =>
      if row < rows.length then
        if (rows[row]?.bind (·[column]?)).getD 0 != 0 then some row
        else findPivot rows column (row + 1)
      else none
termination_by row => rows.length - row

private def scaleRow (factor : Rat) (row : List Rat) : List Rat :=
  row.map (factor * ·)

private def addScaled (factor : Rat) (source target : List Rat) : List Rat :=
  List.zipWith (fun x y => x + factor * y) target source

private def eliminateColumn (rows : List (List Rat)) (pivotRow column : Nat) :
    List (List Rat) :=
  match rows[pivotRow]? with
  | none => rows
  | some pivot => rows.zipIdx.map fun (row, index) =>
      if index == pivotRow then row
      else addScaled (-row[column]!) pivot row

private def gaussJordan.go (dimension : Nat) : Nat → List (List Rat) →
    Except SolveError (List (List Rat))
  | column, rows =>
      if h : column < dimension then do
        let pivotRow ← match findPivot rows column column with
          | some row => pure row
          | none => throw (.singular column)
        let rows := swapAt rows column pivotRow
        let pivot := (rows[column]?.bind (·[column]?)).getD 0
        if pivot == 0 then throw (.singular column)
        let rows := replaceAt rows column (scaleRow (1 / pivot) rows[column]!)
        let rows := eliminateColumn rows column column
        go dimension (column + 1) rows
      else pure rows
termination_by column => dimension - column

/-- Total exact Gauss-Jordan elimination of a square augmented system. -/
def gaussJordan (system : LinearSystem) : Except SolveError (List Rat) := do
  let dimension := system.unknowns.length
  match gaussJordan.go dimension 0 system.rows with
  | .error (.singular column _) =>
      .error (.singular column system.unknowns[column]?)
  | .error error => .error error
  | .ok reduced =>
      pure (reduced.take dimension |>.map fun row => row[dimension]!)

def lookupSolution (pairs : List (Unknown × Rat)) (wanted : Unknown) : Rat :=
  (pairs.find? (fun pair => pair.1 == wanted)).map (·.2) |>.getD 0

@[simp] theorem lookupSolution_nil (wanted : Unknown) :
    lookupSolution [] wanted = 0 := by
  rfl

@[simp] theorem lookupSolution_cons (unknown : Unknown) (value : Rat)
    (rest : List (Unknown × Rat)) (wanted : Unknown) :
    lookupSolution ((unknown, value) :: rest) wanted =
      if unknown == wanted then value else lookupSolution rest wanted := by
  unfold lookupSolution
  split <;> simp_all [List.find?]

def assignmentOf (us : List Unknown) (values : List Rat) : Assignment :=
  let pairs := us.zip values
  { volt := fun node =>
      if node == "0" then 0 else lookupSolution pairs (.voltage node)
    cur := fun name => lookupSolution pairs (.current name) }

/-- Convert finite solver output into the semantic total-function assignment. -/
def Solution.assignment (solution : Solution) : Assignment :=
  assignmentOf solution.unknowns solution.values

/-- Unchecked finite MNA candidate. -/
def solveCandidateData (netlist : FlatNetlist) : Except SolveError Solution := do
  validate netlist
  let system := assemble netlist
  let values ← gaussJordan system
  pure { unknowns := system.unknowns, values }

/-- Backward-compatible unchecked assignment projection. -/
def solveCandidate (netlist : FlatNetlist) : Except SolveError Assignment :=
  (solveCandidateData netlist).map Solution.assignment

private def checkedSolutionData (netlist : FlatNetlist) (solution : Solution) :
    Except SolveError Solution :=
  if _h : Satisfies netlist solution.assignment then .ok solution
  else .error .candidateRejected

/-- Exact checked finite solve. This is the proof-generation interface:
successful results have decidable equality and can be stored as literals. -/
def solveData (netlist : FlatNetlist) : Except SolveError Solution :=
  match solveCandidateData netlist with
  | .error error => .error error
  | .ok solution => checkedSolutionData netlist solution

/-- Exact checked DC solve. Singular and malformed systems fail loudly. -/
def solve (netlist : FlatNetlist) : Except SolveError Assignment :=
  (solveData netlist).map Solution.assignment

private theorem checkedSolutionData_satisfies {netlist : FlatNetlist}
    {candidate solution : Solution}
    (h : checkedSolutionData netlist candidate = .ok solution) :
    Satisfies netlist solution.assignment := by
  unfold checkedSolutionData at h
  split at h
  · next hs =>
      simp at h
      subst solution
      exact hs
  · simp at h

/-- A successful finite solution satisfies the definitional circuit laws. -/
theorem solution_satisfies {netlist : FlatNetlist} {solution : Solution}
    (h : solveData netlist = .ok solution) :
    Satisfies netlist solution.assignment := by
  unfold solveData at h
  generalize hr : solveCandidateData netlist = result at h
  cases result with
  | error error => simp at h
  | ok candidate => exact checkedSolutionData_satisfies h

/-- Generic soundness theorem for every successful checked solve. -/
theorem solve_satisfies {netlist : FlatNetlist} {assignment : Assignment}
    (h : solve netlist = .ok assignment) : Satisfies netlist assignment := by
  unfold solve at h
  generalize hr : solveData netlist = result at h
  cases result with
  | error error => cases h
  | ok solution =>
      cases h
      exact solution_satisfies hr

end LeanModels.Spice
