import KltDP.Geometry.UnbranchedExceptionalBlockIndex
import KltDP.Geometry.KltResolutionExceptionalProjectiveLine
import KltDP.Geometry.RationalCurveSmooth
import KltDP.Geometry.SelectedPrimeUnionSmooth

/-!
# Original isolated klt exceptional selections supply the branch geometry

The original minimal klt resolution gives each selected exceptional curve
its actual projective-line isomorphism over k. Geometric isolation gives
pairwise disjointness. The selected original union, and therefore the
unchanged canonical Cartier branch with that ideal, is smooth.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.UnbranchedExceptionalBlocks

open NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k] {S X : NormalProjectiveSurface k}
    (π : S.toScheme ⟶ X.toScheme) (N : Finset S.PrimeCurve)
    (hmin : IsMinimalResolution S X π) (hklt : IsKlt X)
    (hiso : IsolatedSelection π N) (hN : ∀ A ∈ N, IsExceptionalCurve π A)

include hiso hN in
/-- The selected original isolated primes are pairwise disjoint. -/
theorem isolatedSelection_pairwise :
    (N : Set S.PrimeCurve).Pairwise fun A B => Disjoint (A : Set S.toScheme) (B : Set S.toScheme) := by
  intro A hA B hB hAB
  exact hiso A hA ⟨B, hN B hB⟩ (Ne.symm hAB)

include hmin hklt hN

/-- The original klt resolution provides all selected projective-line isomorphisms over k. -/
theorem selectedExceptional_projectiveLine :
    ∀ A ∈ N, ∃ η : A.toScheme ≅ projectiveSpace k 1,
      η.hom ≫ projectiveSpaceToSpec k 1 = A.toSpec := by
  intro A hA
  exact hmin.toIsResolution.exceptional_projectiveLine_iso_of_klt hklt A (hN A hA)

/-- Every selected original exceptional curve is smooth for its unchanged map over k. -/
theorem selectedExceptional_isSmooth : ∀ A ∈ N, IsSmooth A.toSpec := by
  intro A hA
  obtain ⟨η, hη⟩ := selectedExceptional_projectiveLine π N hmin hklt hN A hA
  letI : IsSmoothOfRelativeDimension 1 A.toSpec := smoothOne_of_projectiveLineIso A.toSpec η hη
  exact IsSmoothOfRelativeDimension.isSmooth 1 A.toSpec

include hiso in
/-- Smoothness of the original canonical branch is derived from its actual isolated selection. -/
theorem isolatedSelection_canonicalBranch_isSmooth
    (E : CartierDivisor S.toScheme) (hE : HasRegularCartierEquations S.toScheme E)
    (hIJ : effectiveCartierIdealDataOfRegularEquations S.toScheme E hE =
      Scheme.IdealSheafData.vanishingIdeal (S.selectedPrimeClosedUnion N)) :
    IsSmooth ((effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).gluedTo ≫ S.structureMorphism) := by
  rw [hIJ]
  exact S.selectedPrimeUnion_isSmooth N (isolatedSelection_pairwise π N hiso hN)
    (selectedExceptional_isSmooth π N hmin hklt hN)

end KltDP.Geometry.UnbranchedExceptionalBlocks

#print axioms KltDP.Geometry.UnbranchedExceptionalBlocks.isolatedSelection_canonicalBranch_isSmooth
