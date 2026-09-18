/-
Copyright (c) 2026 KltDP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import KltDP.Geometry.RelativeProjectiveCoefficientMorphism
import KltDP.Geometry.ProjectiveSpaceChartRange

/-!
# Original coordinate-chart preimages under coefficient change

The existing chart-range calculation works over every commutative ring. Actual
coordinate fractions are preserved by coefficient change, so the original
whole-Proj morphism pulls each coordinate basic open back to the same coordinate
basic open over the new base. No preimage or cartesian premise is assumed.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
namespace KltDP.Geometry.RelativeProjectiveChart
attribute [local instance] MvPolynomial.gradedAlgebra
variable (R : Type u) [CommRing R] (n : ℕ)

/-- The fraction `z_i / z_m` in the chart ring of `z_m` (the pinned localisation element of
`A_{(z_m z_i)} = A_{(z_m)}[1/(z_i/z_m)]`). -/
abbrev chartFraction (m i : Fin (n + 1)) : coordinateChartRing R n m :=
  HomogeneousLocalization.Away.isLocalizationElem (coordinate_mem R n m) (coordinate_mem R n i)

theorem chartFraction_eq (m i : Fin (n + 1)) :
    chartFraction R n m i =
      HomogeneousLocalization.Away.mk (grading R n) (coordinate_mem R n m) 1 (MvPolynomial.X i)
        (by simpa only [one_smul] using coordinate_mem R n i) := by
  unfold chartFraction HomogeneousLocalization.Away.isLocalizationElem
  congr 1
  exact pow_one _

/-- `A_{(z_m z_i)}` is the localisation of `A_{(z_m)}` away from `z_i/z_m`. -/
theorem toOverlapLeft_isLocalization (m i : Fin (n + 1)) :
    letI := (toOverlapLeft R n m i).toAlgebra
    IsLocalization.Away (chartFraction R n m i) (coordinateOverlapRing R n m i) :=
  HomogeneousLocalization.Away.isLocalization_mul (coordinate_mem R n m) (coordinate_mem R n i)
    rfl Nat.one_ne_zero

/-- The range of the restriction `Spec (A_{(z_m z_i)}) ⟶ Spec (A_{(z_m)})` is `D(z_i/z_m)`. -/
theorem range_specMap_toOverlapLeft (m i : Fin (n + 1)) :
    Set.range (Spec.map (CommRingCat.ofHom (toOverlapLeft R n m i))).base =
      (PrimeSpectrum.basicOpen (chartFraction R n m i) :
        Set (PrimeSpectrum (coordinateChartRing R n m))) :=
  ProjectiveChart.range_specMap_of_isLocalization_away _ _ (toOverlapLeft_isLocalization R n m i)

/-- The range of the first projection of the overlap `D(z_m) ∩ D(z_i)` in the chart `D(z_m)`. -/
theorem range_pullback_fst_coordinateCharts (m i : Fin (n + 1)) :
    Set.range (pullback.fst (coordinateChartMorphism R n m) (coordinateChartMorphism R n i)).base =
      (PrimeSpectrum.basicOpen (chartFraction R n m i) :
        Set (PrimeSpectrum (coordinateChartRing R n m))) := by
  rw [← range_specMap_toOverlapLeft, ← coordinateOverlapIso_inv_fst, ProjectiveChart.range_comp_base_of_isIso]

/-- **A point of the chart `D(z_m)` lies in the chart `D(z_i)` iff `z_i/z_m` is invertible
at it.** -/
theorem coordinateChartMorphism_mem_range_iff (m i : Fin (n + 1))
    (q : Spec (CommRingCat.of (coordinateChartRing R n m))) :
    (coordinateChartMorphism R n m).base q ∈ Set.range (coordinateChartMorphism R n i).base ↔
      q ∈ PrimeSpectrum.basicOpen (chartFraction R n m i) := by
  have h := Scheme.Pullback.range_fst (coordinateChartMorphism R n m)
    (coordinateChartMorphism R n i)
  rw [range_pullback_fst_coordinateCharts] at h
  exact (Set.ext_iff.mp h q).symm


variable {R} {S : Type u} [CommRing S] (φ : R →+* S)

@[simp] theorem coefficientChartMap_chartFraction (i j : Fin (n + 1)) :
    coefficientChartMap n φ i (chartFraction R n i j) = chartFraction S n i j := by
  rw [chartFraction_eq, coefficientChartMap, coefficientMap_mk, chartFraction_eq]
  simp only [MvPolynomial.map_X]

/-- Coefficient change has the exact original coordinate-open preimages. -/
theorem coefficientMorphism_preimage_coordinateOpen (j : Fin (n + 1)) :
    coefficientMorphism n φ ⁻¹ᵁ Proj.basicOpen (grading R n) (MvPolynomial.X j) =
      Proj.basicOpen (grading S n) (MvPolynomial.X j) := by
  apply TopologicalSpace.Opens.ext
  ext x
  let i : Fin (n + 1) := (standardAffineCover S n).f x
  obtain ⟨q, hq⟩ := (standardAffineCover S n).covers x
  change (coordinateChartMorphism S n i).base q = x at hq
  rw [← hq]
  change ((coordinateChartMorphism S n i ≫ coefficientMorphism n φ).base q ∈
      Proj.basicOpen (grading R n) (MvPolynomial.X j)) ↔
    (coordinateChartMorphism S n i).base q ∈ Proj.basicOpen (grading S n) (MvPolynomial.X j)
  rw [coordinateChartMorphism_coefficientMorphism, Scheme.comp_base_apply,
    ← coordinateChartMorphism_opensRange, ← coordinateChartMorphism_opensRange]
  change ((coordinateChartMorphism R n i).base
      ((Spec.map (CommRingCat.ofHom (coefficientChartMap n φ i))).base q) ∈
        Set.range (coordinateChartMorphism R n j).base) ↔
    (coordinateChartMorphism S n i).base q ∈ Set.range (coordinateChartMorphism S n j).base
  rw [coordinateChartMorphism_mem_range_iff, coordinateChartMorphism_mem_range_iff,
    ProjectiveChart.specMap_base_mem_basicOpen_iff, coefficientChartMap_chartFraction]

end KltDP.Geometry.RelativeProjectiveChart

#print axioms KltDP.Geometry.RelativeProjectiveChart.coefficientMorphism_preimage_coordinateOpen
