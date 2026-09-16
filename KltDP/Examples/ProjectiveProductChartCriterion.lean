import KltDP.Examples.ProjectiveLinePointAtInfinity
import KltDP.Examples.FrobeniusGraphClosed

/-!
# Coordinate criterion for the affine chart of the projective product

The accepted affine chart `planeChart : Spec k[u,v] ⟶ P¹ ×_k P¹` is the product of the finite charts of
the two factors (`affineProductChart = pullback.map …`), so a point lies in its range iff both
projections lie on the finite line `chartOpen k 0` (`mem_range_planeChart_iff`, via the pinned
`Scheme.Pullback.range_map`). The translated charts `translatedPlaneChart p a` have the same range
(`range_translatedPlaneChart`), hence the same criterion (`mem_range_translatedPlaneChart_iff`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace KltDP.Examples.ProjectiveProductChartCriterion

open KltDP.Geometry ProjectiveLineComparison FrobeniusProjectivePoints FrobeniusProductPlaneChart
  FrobeniusGraphClosed FrobeniusTranslatedCharts

variable {k : Type u} [Field k]

theorem range_affineProductChart :
    Set.range (affineProductChart (k := k)).base =
      firstProjection.base ⁻¹' (chartOpen k 0 : Set (projectiveSpace k 1)) ∩
        secondProjection.base ⁻¹' (chartOpen k 0 : Set (projectiveSpace k 1)) := by
  have h0 : Set.range (polynomialChartMap k 0).base = (chartOpen k 0 : Set (projectiveSpace k 1)) :=
    congrArg SetLike.coe (polynomialChartMap_opensRange (k := k) 0)
  rw [affineProductChart, Scheme.Pullback.range_map, h0]

/-- The range of the affine chart of the product is the set of points with both coordinates finite. -/
theorem range_planeChart :
    Set.range (planeChart (k := k)).base =
      firstProjection.base ⁻¹' (chartOpen k 0 : Set (projectiveSpace k 1)) ∩
        secondProjection.base ⁻¹' (chartOpen k 0 : Set (projectiveSpace k 1)) := by
  have h : Set.range (planeChart (k := k)).base = Set.range (affineProductChart (k := k)).base :=
    congrArg SetLike.coe
      (Scheme.Hom.opensRange_comp_of_isIso (planeProductIso (k := k)).hom affineProductChart)
  rw [h, range_affineProductChart]

theorem mem_range_planeChart_iff (y : projectiveProduct k) :
    y ∈ Set.range (planeChart (k := k)).base ↔
      firstProjection.base y ∈ chartOpen k 0 ∧ secondProjection.base y ∈ chartOpen k 0 := by
  rw [range_planeChart]
  exact Iff.rfl

/-- The translated charts have the range of the affine chart. -/
theorem range_translatedPlaneChart (p : ℕ) (a : k) :
    Set.range (translatedPlaneChart p a).base = Set.range (planeChart (k := k)).base :=
  congrArg SetLike.coe
    (Scheme.Hom.opensRange_comp_of_isIso (planeTranslationIso a (a ^ p)).hom planeChart)

theorem mem_range_translatedPlaneChart_iff (p : ℕ) (a : k) (y : projectiveProduct k) :
    y ∈ Set.range (translatedPlaneChart p a).base ↔
      firstProjection.base y ∈ chartOpen k 0 ∧ secondProjection.base y ∈ chartOpen k 0 := by
  rw [range_translatedPlaneChart, mem_range_planeChart_iff]

end KltDP.Examples.ProjectiveProductChartCriterion
