/-
Copyright (c) 2026 KltDP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import KltDP.Geometry.RelativeProjectiveCoefficientPreimage
import KltDP.Geometry.RelativeProjectiveCoordinateBaseChange

/-!
# The two original chart pullback squares for whole-Proj base change

The first square identifies the actual source coordinate chart with the
preimage of the actual target coordinate chart. The second is the cartesian
coefficient square over the original base rings. Together they are the local
input for the native local-at-target criterion for the whole square.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
namespace KltDP.Geometry.RelativeProjectiveChart
attribute [local instance] MvPolynomial.gradedAlgebra

variable {R S : Type u} [CommRing R] [CommRing S] (n : ℕ) (φ : R →+* S)

/-- The actual source coordinate chart is the actual target-chart pullback. -/
theorem isPullback_coefficientMorphism_chart (i : Fin (n + 1)) :
    IsPullback (coordinateChartMorphism S n i)
      (Spec.map (CommRingCat.ofHom (coefficientChartMap n φ i)))
      (coefficientMorphism n φ) (coordinateChartMorphism R n i) := by
  have hrange : Set.range (coordinateChartMorphism S n i).base =
      Set.range (pullback.fst (coefficientMorphism n φ) (coordinateChartMorphism R n i)).base := by
    rw [Scheme.Pullback.range_fst]
    change ((coordinateChartMorphism S n i).opensRange : Set (freeProjectivization S n)) =
      ((coefficientMorphism n φ ⁻¹ᵁ (coordinateChartMorphism R n i).opensRange) :
        Set (freeProjectivization S n))
    rw [coordinateChartMorphism_opensRange, coordinateChartMorphism_opensRange,
      coefficientMorphism_preimage_coordinateOpen]
  let e := IsOpenImmersion.isoOfRangeEq (coordinateChartMorphism S n i)
    (pullback.fst (coefficientMorphism n φ) (coordinateChartMorphism R n i)) hrange
  have he : e.hom ≫ pullback.fst _ _ = coordinateChartMorphism S n i :=
    IsOpenImmersion.isoOfRangeEq_hom_fac _ _ hrange
  refine IsPullback.of_iso_pullback
    ⟨coordinateChartMorphism_coefficientMorphism n φ i⟩ e he ?_
  rw [← cancel_mono (coordinateChartMorphism R n i), Category.assoc,
    ← pullback.condition, ← Category.assoc, he,
    coordinateChartMorphism_coefficientMorphism]

/-- The local cartesian square retains the original whole-Proj structure maps. -/
theorem isPullback_coordinateChart_over_base (i : Fin (n + 1)) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (coefficientChartMap n φ i)))
      (coordinateChartMorphism S n i ≫ freeProjectivizationToBase S n)
      (coordinateChartMorphism R n i ≫ freeProjectivizationToBase R n)
      (Spec.map (CommRingCat.ofHom φ)) := by
  simpa only [coordinateChartMorphism_over_base] using isPullback_coordinateChart n φ i

end KltDP.Geometry.RelativeProjectiveChart

#print axioms KltDP.Geometry.RelativeProjectiveChart.isPullback_coefficientMorphism_chart
#print axioms KltDP.Geometry.RelativeProjectiveChart.isPullback_coordinateChart_over_base
