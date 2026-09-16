import KltDP.Geometry.Surface
import KltDP.Topology.DimensionTwoIrreducibleClosed

/-!
# Irreducible closed subsets of the original surface

The original surface's `dimension_two` field specializes the generic
topological classification without any extra geometric hypothesis.
-/

namespace KltDP.Geometry.NormalProjectiveSurface

open TopologicalSpace

universe u

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)

/-- A positive-dimensional irreducible closed subset of the original
surface is one-dimensional or has the whole surface as its underlying set. -/
theorem irreducibleClosed_dim_eq_one_or_eq_univ
    (Z : IrreducibleCloseds X.toScheme)
    (hpositive : 0 < topologicalKrullDim (Z : Set X.toScheme)) :
    topologicalKrullDim (Z : Set X.toScheme) = 1 ∨ (Z : Set X.toScheme) = Set.univ :=
  KltDP.Topology.irreducibleClosed_dim_eq_one_or_eq_univ X.dimension_two.le Z hpositive

end KltDP.Geometry.NormalProjectiveSurface
