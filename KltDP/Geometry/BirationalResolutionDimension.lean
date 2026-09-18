import KltDP.Geometry.ProperBirationalDimension
import KltDP.Literature.ResolutionDebtLiterals

/-!
# The original dimension input for the resolution constructor

The proved proper birational dimension theorem supplies the whole dimension
predicate used by the older resolution constructor over an algebraically
closed field. No dimension formula or resolution-existence statement is
assumed. The other constructor predicates remain separate obligations.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry

/-- Discharge the original resolution constructor's dimension hypothesis
using the actual proper map and its original birational generic stalk map. -/
theorem birationalResolutionDimension
    (k : Type u) [Field k] [IsAlgClosed k] :
    KltDP.Literature.Stacks.BirationalDimensionLiteral k := by
  constructor
  intro X Y _ π hπ hbir
  letI : IsProper π := hπ
  exact topologicalKrullDim_eq_of_proper_birational π X.structureMorphism hbir

end KltDP.Geometry

#print axioms KltDP.Geometry.birationalResolutionDimension
