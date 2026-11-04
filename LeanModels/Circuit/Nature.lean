/-!
# Physical dimensions, natures, and disciplines

Source-level natures carry physical dimensions, not a fixed numerical
carrier.  DC, transient, AC, and enclosure interpretations may therefore use
different scalar types without changing the circuit declaration.
-/

namespace LeanModels.Circuit

/-- Integer exponents of the seven SI base dimensions. -/
structure Dimension where
  length : Int := 0
  mass : Int := 0
  time : Int := 0
  current : Int := 0
  temperature : Int := 0
  amount : Int := 0
  luminosity : Int := 0
deriving Repr, BEq, DecidableEq, Inhabited

namespace Dimension

def dimensionless : Dimension := {}
def electricCurrent : Dimension := { current := 1 }
def electricPotential : Dimension :=
  { length := 2, mass := 1, time := -3, current := -1 }
def resistance : Dimension :=
  { length := 2, mass := 1, time := -3, current := -2 }
def capacitance : Dimension :=
  { length := -2, mass := -1, time := 4, current := 2 }
def inductance : Dimension :=
  { length := 2, mass := 1, time := -2, current := -2 }

end Dimension

/-- A source-level nature declaration. Display units and solver tolerances
belong to frontend metadata rather than the semantic identity of a nature. -/
structure NatureDecl where
  name : String
  dimension : Dimension
  derivative : Option String := none
  integral : Option String := none
deriving Repr, BEq, Inhabited

/-- Conservative disciplines equate potentials and conserve flows. Signal
disciplines are deliberately separate and acquire an explicit resolution
relation in their semantic interpretation. -/
inductive DisciplineDecl where
  | conservative (potential flow : NatureDecl)
  | signal (quantity : NatureDecl)
deriving Repr, BEq, Inhabited

def voltageNature : NatureDecl :=
  { name := "Voltage", dimension := .electricPotential }

def currentNature : NatureDecl :=
  { name := "Current", dimension := .electricCurrent }

def electrical : DisciplineDecl :=
  .conservative voltageNature currentNature

#guard voltageNature.dimension == Dimension.electricPotential
#guard electrical == .conservative voltageNature currentNature

end LeanModels.Circuit
