import KltDP.Geometry.UnbranchedExceptionalBlockIndex
import KltDP.Geometry.SelectedCanonicalBranchRange

/-!
# Every unbranched original exceptional block misses the original branch

All original primes in a retained block lie outside the selection. Each
selected isolated prime is disjoint from all of them, so the whole actual
block misses the selected union and hence the original canonical branch.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.UnbranchedExceptionalBlocks

open NormalProjectiveSurface ActualExceptionalIncidence ExceptionalForestClosedBlocks

variable {k : Type u} [Field k] [IsAlgClosed k] {S X : NormalProjectiveSurface k}
    (π : S.toScheme ⟶ X.toScheme) (N : Finset S.PrimeCurve)
    (hiso : IsolatedSelection π N)

include hiso in
/-- All original unbranched block supports miss the entire actual selected branch union. -/
theorem blockSupport_disjoint_selected (b : Blocks π N) :
    Disjoint (blockSupport π b.val) (S.selectedPrimeClosedUnion N : Set S.toScheme) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  obtain ⟨v, hxv⟩ := Set.mem_iUnion.mp hx
  change x ∈ ⋃ A ∈ N, (A : Set S.toScheme) at hy
  obtain ⟨A, hA⟩ := Set.mem_iUnion.mp hy
  obtain ⟨hAN, hxA⟩ := Set.mem_iUnion.mp hA
  have hne : v.val.val ≠ A := by
    intro h
    apply b.property v.val v.property
    rw [h]
    exact hAN
  exact Set.disjoint_left.mp (hiso A hAN v.val hne) hxA hxv

include hiso in
/-- The unchanged reduced block immersion misses the unchanged canonical branch map. -/
theorem blockInclusion_disjoint_canonicalBranch [IsProper π] (hbir : IsBirationalScheme π)
    (E : CartierDivisor S.toScheme) (hE : HasRegularCartierEquations S.toScheme E)
    (hIJ : effectiveCartierIdealDataOfRegularEquations S.toScheme E hE =
      Scheme.IdealSheafData.vanishingIdeal (S.selectedPrimeClosedUnion N))
    (b : Blocks π N) :
    Disjoint (Set.range (blockInclusion π hbir b.val).base)
      (Set.range (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).gluedTo.base) := by
  rw [range_blockInclusion, S.canonicalBranch_range_eq_selected N E hE hIJ]
  exact blockSupport_disjoint_selected π N hiso b

end KltDP.Geometry.UnbranchedExceptionalBlocks

#print axioms KltDP.Geometry.UnbranchedExceptionalBlocks.blockInclusion_disjoint_canonicalBranch
