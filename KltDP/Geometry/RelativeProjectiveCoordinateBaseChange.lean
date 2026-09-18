/-
Copyright (c) 2026 KltDP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import KltDP.Geometry.RelativeProjectiveCoefficientCharts

/-!
# Cartesian base change on every original coordinate chart

The coefficient map on original fractions agrees with the verified first-chart
map. Original coordinate permutations commute with coefficient change and
preserve original constants. Transport of the first-chart cartesian square
therefore gives the cartesian square on every actual coordinate chart.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
namespace KltDP.Geometry.RelativeProjectiveChart
attribute [local instance] MvPolynomial.gradedAlgebra

variable {R S : Type u} [CommRing R] [CommRing S] (n : ℕ) (φ : R →+* S)

private theorem dehomogenizePolynomial_map (p : homogeneousRing R n) :
    dehomogenizePolynomial S n (MvPolynomial.map φ p) =
      MvPolynomial.map φ (dehomogenizePolynomial R n p) := by
  have h : (dehomogenizePolynomial S n).comp (MvPolynomial.map φ) =
      (MvPolynomial.map φ).comp (dehomogenizePolynomial R n) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [dehomogenizePolynomial]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [dehomogenizePolynomial]
      · simp [dehomogenizePolynomial]
  exact RingHom.congr_fun h p

/-- The fraction-defined coefficient map is the already verified first-chart map. -/
theorem coefficientChartMap_zero : coefficientChartMap n φ 0 = chartMap n φ := by
  apply HomogeneousAway.ringHom_ext (grading R n) (coordinate_mem R n 0)
  intro m p hp
  apply (coordinateRingEquiv S n).injective
  rw [coefficientChartMap, coefficientMap_mk]
  simp only [chartMap, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
  change dehomogenize S n _ = MvPolynomial.map φ (dehomogenize R n _)
  rw [dehomogenize_mk, dehomogenize_mk]
  exact dehomogenizePolynomial_map n φ p

/-- Original coordinate permutation preserves the original coefficient map. -/
theorem firstChartEquivCoordinateChart_constants (i : Fin (n + 1)) (r : R) :
    firstChartEquivCoordinateChart R n i (constants R n r) =
      coordinateChartConstants R n i r := by
  apply HomogeneousLocalization.val_injective
  change Localization.mk (MvPolynomial.rename (Equiv.swap 0 i) (MvPolynomial.C r))
      ⟨MvPolynomial.rename (Equiv.swap 0 i) 1, _⟩ =
    Localization.mk (MvPolynomial.C r) 1
  simp only [MvPolynomial.rename_C, map_one]
  rfl

/-- Original coordinate permutation commutes with the actual coefficient map. -/
theorem coefficientChartMap_firstChartEquiv (i : Fin (n + 1)) (z : chartRing R n) :
    coefficientChartMap n φ i (firstChartEquivCoordinateChart R n i z) =
      firstChartEquivCoordinateChart S n i (coefficientChartMap n φ 0 z) := by
  obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective z
  apply HomogeneousLocalization.val_injective
  change Localization.mk (MvPolynomial.map φ
      (MvPolynomial.rename (Equiv.swap 0 i) (c.num : homogeneousRing R n)))
      ⟨MvPolynomial.map φ (MvPolynomial.rename (Equiv.swap 0 i) (c.den : homogeneousRing R n)), _⟩ =
    Localization.mk (MvPolynomial.rename (Equiv.swap 0 i)
      (MvPolynomial.map φ (c.num : homogeneousRing R n)))
      ⟨MvPolynomial.rename (Equiv.swap 0 i) (MvPolynomial.map φ (c.den : homogeneousRing R n)), _⟩
  simp only [MvPolynomial.map_rename]

/-- Every original coordinate chart has its actual cartesian coefficient square. -/
theorem isPullback_coordinateChart (i : Fin (n + 1)) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (coefficientChartMap n φ i)))
      (Spec.map (CommRingCat.ofHom (coordinateChartConstants S n i)))
      (Spec.map (CommRingCat.ofHom (coordinateChartConstants R n i)))
      (Spec.map (CommRingCat.ofHom φ)) := by
  refine (isPullback_chartSpec n φ).of_iso
    (Scheme.Spec.mapIso (firstChartEquivCoordinateChart S n i).symm.toCommRingCatIso.op)
    (Scheme.Spec.mapIso (firstChartEquivCoordinateChart R n i).symm.toCommRingCatIso.op)
    (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · change Spec.map (CommRingCat.ofHom (chartMap n φ)) ≫
        Spec.map (CommRingCat.ofHom (firstChartEquivCoordinateChart R n i).symm.toRingHom) =
      Spec.map (CommRingCat.ofHom (firstChartEquivCoordinateChart S n i).symm.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (coefficientChartMap n φ i))
    rw [← Spec.map_comp, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro z
    change chartMap n φ ((firstChartEquivCoordinateChart R n i).symm z) =
      (firstChartEquivCoordinateChart S n i).symm (coefficientChartMap n φ i z)
    apply (firstChartEquivCoordinateChart S n i).injective
    rw [RingEquiv.apply_symm_apply, ← coefficientChartMap_zero,
      ← coefficientChartMap_firstChartEquiv, RingEquiv.apply_symm_apply]
  · simp only [Iso.refl_hom, Category.comp_id]
    change Spec.map (CommRingCat.ofHom (constants S n)) =
      Spec.map (CommRingCat.ofHom (firstChartEquivCoordinateChart S n i).symm.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (coordinateChartConstants S n i))
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    change constants S n r =
      (firstChartEquivCoordinateChart S n i).symm (coordinateChartConstants S n i r)
    apply (firstChartEquivCoordinateChart S n i).injective
    rw [RingEquiv.apply_symm_apply, firstChartEquivCoordinateChart_constants]
  · simp only [Iso.refl_hom, Category.comp_id]
    change Spec.map (CommRingCat.ofHom (constants R n)) =
      Spec.map (CommRingCat.ofHom (firstChartEquivCoordinateChart R n i).symm.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (coordinateChartConstants R n i))
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    change constants R n r =
      (firstChartEquivCoordinateChart R n i).symm (coordinateChartConstants R n i r)
    apply (firstChartEquivCoordinateChart R n i).injective
    rw [RingEquiv.apply_symm_apply, firstChartEquivCoordinateChart_constants]
  · simp

end KltDP.Geometry.RelativeProjectiveChart

#print axioms KltDP.Geometry.RelativeProjectiveChart.coefficientChartMap_zero
#print axioms KltDP.Geometry.RelativeProjectiveChart.isPullback_coordinateChart
