import KltDP.Examples.FrobeniusMultiCentreContractingNullRuling

/-!
# Every off-graph M-null curve lies in one original closed ruling fiber

The range of the actual ruling morphism is the image of the original prime
curve support. Thus the proved singleton image identifies a closed fiber
containing the curve, while the proved numerical criterion gives its
geometric disjointness from the original strict graph. These are the two
inputs needed for the finite and infinity fiber classification.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Examples.FrobeniusMultiCentreNullFiberReduction

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open FrobeniusGraphClosed FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
open FrobeniusMultiCentreGraphFiber FrobeniusMultiCentreContractingClass
open FrobeniusMultiCentreContractingNef FrobeniusMultiCentreContractingNullRuling

variable {k : Type u} [Field k] [IsAlgClosed k]
  (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
  (a : Fin n → k) (ha : Function.Injective a)
  (hproj : IsProjectiveOverField (multiStructure (q + 1) n a))
  (C : (multiSurfaceSurface (q + 1) n a ha hproj).PrimeCurve)

/-- A singleton image of the actual curve gives containment of its original support. -/
theorem support_subset_ruling_fiber (z : projectiveSpace k 1)
    (hz : Set.range (rulingMap q n a ha hproj C).base = {z}) :
    (C : Set (multiSurfaceSurface (q + 1) n a ha hproj).toScheme) ⊆
      (multiProjection (q + 1) n a ≫ secondProjection).base ⁻¹' {z} := by
  intro x hx
  rw [← C.range_inclusion] at hx
  obtain ⟨y, rfl⟩ := hx
  have hy : (rulingMap q n a ha hproj C).base y ∈
      Set.range (rulingMap q n a ha hproj C).base := ⟨y, rfl⟩
  rw [hz] at hy
  exact hy

/-- The actual off-graph M-null prime lies in a closed ruling fiber and is disjoint
from the independently defined original graph. -/
theorem null_curve_closed_fiber_and_disjoint (hn : 2 < n)
    (hC : C ≠ graphPrimeCurve q n a ha hproj)
    (hnull : (multiSurfaceSurface (q + 1) n a ha hproj).picardRestrictionDegreeHom C
      (contractingClass q n a ha) = 0) :
    ∃ z : projectiveSpace k 1, IsClosed ({z} : Set (projectiveSpace k 1)) ∧
      (C : Set (multiSurfaceSurface (q + 1) n a ha hproj).toScheme) ⊆
        (multiProjection (q + 1) n a ≫ secondProjection).base ⁻¹' {z} ∧
      Disjoint (C : Set (multiSurfaceSurface (q + 1) n a ha hproj).toScheme)
        (Set.range (graphStrictι (q + 1) n a).base) := by
  obtain ⟨z, hclosed, hz⟩ := null_curve_has_closed_ruling_image q n a ha hproj C hn hC hnull
  exact ⟨z, hclosed, support_subset_ruling_fiber q n a ha hproj C z hz,
    ((null_iff_disjoint_and_ruling_degree_zero q n a ha hproj C hn hC).mp hnull).1⟩

end KltDP.Examples.FrobeniusMultiCentreNullFiberReduction
