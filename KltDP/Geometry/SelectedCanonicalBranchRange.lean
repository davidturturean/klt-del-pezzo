import KltDP.Geometry.SelectedPrimeCanonicalBranchMap

/-!
# The original canonical branch has the actual selected closed range

The original ideal equality identifies its support with the selected
finite union. The proved glued-ideal range theorem retains the original
canonical branch map when translating branch disjointness.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] (S : NormalProjectiveSurface k)

/-- The original branch map has precisely the selected original closed union as its range. -/
theorem canonicalBranch_range_eq_selected
    (N : Finset S.PrimeCurve) (E : CartierDivisor S.toScheme)
    (hE : HasRegularCartierEquations S.toScheme E)
    (hIJ : effectiveCartierIdealDataOfRegularEquations S.toScheme E hE =
      Scheme.IdealSheafData.vanishingIdeal (S.selectedPrimeClosedUnion N)) :
    Set.range (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).gluedTo.base =
      (S.selectedPrimeClosedUnion N : Set S.toScheme) := by
  rw [(effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).range_gluedTo]
  change ((effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).support : Set S.toScheme) = _
  rw [hIJ]
  rfl

end KltDP.Geometry.NormalProjectiveSurface

#print axioms KltDP.Geometry.NormalProjectiveSurface.canonicalBranch_range_eq_selected
