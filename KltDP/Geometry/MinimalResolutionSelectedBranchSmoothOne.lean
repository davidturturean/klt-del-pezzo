import KltDP.Geometry.IsolatedExceptionalSelectionGeometry
import KltDP.Geometry.SelectedPrimeUnionSmoothDimension

/-! The actual isolated klt exceptional selection gives the original
canonical Cartier branch relative dimension one, with no smoothness input. -/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.UnbranchedExceptionalBlocks

open NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k] {S X : NormalProjectiveSurface k}
    (π : S.toScheme ⟶ X.toScheme) (N : Finset S.PrimeCurve)
    (hmin : IsMinimalResolution S X π) (hklt : IsKlt X)
    (hiso : IsolatedSelection π N) (hN : ∀ C ∈ N, IsExceptionalCurve π C)

include hmin hklt hiso hN

/-- The actual selected branch is smooth of relative dimension one over the original field. -/
theorem isolatedSelection_canonicalBranch_isSmoothOne
    (E : CartierDivisor S.toScheme) (hE : HasRegularCartierEquations S.toScheme E)
    (hIJ : effectiveCartierIdealDataOfRegularEquations S.toScheme E hE =
      Scheme.IdealSheafData.vanishingIdeal (S.selectedPrimeClosedUnion N)) :
    IsSmoothOfRelativeDimension 1
      ((effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).gluedTo ≫ S.structureMorphism) := by
  rw [hIJ]
  exact S.selectedRationalPrimeUnion_isSmoothOne N
    (isolatedSelection_pairwise π N hiso hN)
    (selectedExceptional_projectiveLine π N hmin hklt hN)

end KltDP.Geometry.UnbranchedExceptionalBlocks

#print axioms KltDP.Geometry.UnbranchedExceptionalBlocks.isolatedSelection_canonicalBranch_isSmoothOne
