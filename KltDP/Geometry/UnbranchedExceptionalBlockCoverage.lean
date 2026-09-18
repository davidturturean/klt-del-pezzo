import KltDP.Geometry.UnbranchedExceptionalBlockBranchDisjoint

/-!
# All retained original blocks cover exactly the exceptional locus off the branch

The original block index retains all exceptional primes outside the isolated
selection. Its actual block supports therefore cover precisely the original
exceptional prime support minus the selected branch union. The final form
retains both the original block immersions and original canonical branch map.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.UnbranchedExceptionalBlocks

open NormalProjectiveSurface ActualExceptionalIncidence ExceptionalForestClosedBlocks

variable {k : Type u} [Field k] [IsAlgClosed k] {S X : NormalProjectiveSurface k}
    (π : S.toScheme ⟶ X.toScheme) (N : Finset S.PrimeCurve)
    (hiso : IsolatedSelection π N)

include hiso

/-- All retained block supports are exactly the original exceptional support off the selected branch. -/
theorem iUnion_blockSupport_eq_primeSupport_sdiff_selected :
    (⋃ b : Blocks π N, blockSupport π b.val) =
      ActualExceptionalLocus.primeSupport π \ (S.selectedPrimeClosedUnion N : Set S.toScheme) := by
  ext x
  constructor
  · intro hx
    obtain ⟨b, hxb⟩ := Set.mem_iUnion.mp hx
    refine ⟨blockSupport_subset_primeSupport π b.val hxb, ?_⟩
    intro hxN
    exact Set.disjoint_left.mp (blockSupport_disjoint_selected π N hiso b) hxb hxN
  · rintro ⟨hx, hxN⟩
    obtain ⟨P, hP, hxP⟩ := (ActualExceptionalLocus.mem_primeSupport π x).mp hx
    have hPN : P ∉ N := by
      intro h
      exact hxN (Set.mem_iUnion.mpr ⟨P, Set.mem_iUnion.mpr ⟨h, hxP⟩⟩)
    let v : {v : Vertices π // v.val ∉ N} := ⟨⟨P, hP⟩, hPN⟩
    let i := (outsideVertexEquiv π N hiso).symm v
    have hi : vertex π N i = v.val :=
      congrArg Subtype.val ((outsideVertexEquiv π N hiso).apply_symm_apply v)
    have hP' : i.2.val.val = P := congrArg Subtype.val hi
    refine Set.mem_iUnion.mpr ⟨i.1, Set.mem_iUnion.mpr ⟨i.2, ?_⟩⟩
    simpa only [hP'] using hxP

/-- The actual unchanged block maps cover exactly the original exceptional support off the actual branch. -/
theorem iUnion_blockInclusion_eq_primeSupport_sdiff_canonicalBranch
    [IsProper π] (hbir : IsBirationalScheme π)
    (E : CartierDivisor S.toScheme) (hE : HasRegularCartierEquations S.toScheme E)
    (hIJ : effectiveCartierIdealDataOfRegularEquations S.toScheme E hE =
      Scheme.IdealSheafData.vanishingIdeal (S.selectedPrimeClosedUnion N)) :
    (⋃ b : Blocks π N, Set.range (blockInclusion π hbir b.val).base) =
      ActualExceptionalLocus.primeSupport π \
        Set.range (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).gluedTo.base := by
  simp_rw [range_blockInclusion]
  rw [S.canonicalBranch_range_eq_selected N E hE hIJ]
  exact iUnion_blockSupport_eq_primeSupport_sdiff_selected π N hiso

end KltDP.Geometry.UnbranchedExceptionalBlocks

#print axioms KltDP.Geometry.UnbranchedExceptionalBlocks.iUnion_blockInclusion_eq_primeSupport_sdiff_canonicalBranch
