import KltDP.Geometry.PlaneBlowupBoundaryClosure
import KltDP.Geometry.AffineBlowupBoundaryChartSupports
import KltDP.Geometry.AffineBlowupChartBaseChangeFlat
import KltDP.Geometry.SmoothPointBlowupChartBasis
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Actual residual-branch closure on flat étale point-blowup charts

The original flat étale chart map is open. Pulling back the proved closure
identity on the original plane chart therefore identifies the residual
branch in the original extended-centre chart, without a density or
strict-transform equation premise. No regular-parameter claim is inferred
from the differential basis.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace KltDP.Geometry.SmoothPointBlowupChartBasis

open AffineBlowup AffineBlowupChartBaseChange
open KltDP.Examples.FrobeniusBlowupContact
open KltDP.Examples.FrobeniusBlowupSmooth

universe u

attribute [local instance] sourceAlgebra

variable (k : Type u) [Field k]
variable {S : Type u} [CommRing S] [Algebra k S] (φ : planeRing k →ₐ[k] S)
variable [hFlat : Flat (Spec.map (CommRingCat.ofHom φ.toRingHom))]
variable [hEtale : IsEtale (Spec.map (CommRingCat.ofHom φ.toRingHom))]

include hFlat hEtale in
/-- The literal residual fraction defines the closure of the original
branch away from the exceptional equation in this actual Rees chart. -/
theorem fraction_zeroLocus_closure :
    closure (PrimeSpectrum.zeroLocus {fractionCoordinate k φ} \
      PrimeSpectrum.zeroLocus {exceptionalParameter k φ}) =
      PrimeSpectrum.zeroLocus {fractionCoordinate k φ} := by
  let ψ := Spec.map (CommRingCat.ofHom (chartMapAlgHom k φ).toRingHom)
  letI : Flat ψ := chartMap_isFlat centerIdeal φ.toRingHom centerU
  letI : IsEtale ψ := chartMap_isEtale centerIdeal φ.toRingHom centerU
  letI : IsSmooth ψ := IsSmoothOfRelativeDimension.isSmooth 0 ψ
  have h := ψ.isOpenMap.preimage_closure_eq_closure_preimage ψ.continuous
    (PrimeSpectrum.zeroLocus {chartW (k := k)} \
      PrimeSpectrum.zeroLocus {chartU (k := k)})
  rw [PlaneBlowupBoundaryClosure.residual_closure] at h
  change PrimeSpectrum.comap (chartMapAlgHom k φ).toRingHom ⁻¹'
      PrimeSpectrum.zeroLocus {chartW (k := k)} =
    closure (PrimeSpectrum.comap (chartMapAlgHom k φ).toRingHom ⁻¹'
      (PrimeSpectrum.zeroLocus {chartW (k := k)} \
        PrimeSpectrum.zeroLocus {chartU (k := k)})) at h
  simp only [Set.preimage_diff, PrimeSpectrum.preimage_comap_zeroLocus] at h
  have hw : (chartMapAlgHom k φ).toRingHom chartW = fractionCoordinate k φ :=
    chartMapAlgHom_w k φ
  have hu : (chartMapAlgHom k φ).toRingHom chartU = exceptionalParameter k φ :=
    chartMapAlgHom_u k φ
  simpa only [Set.image_singleton, hw, hu] using h.symm

include hFlat hEtale in
/-- The conventional strict-support closure is the actual residual-fraction
zero locus for the original centre, chart inclusion and blowup projection. -/
theorem original_branch_strict_support :
    closure ((AffineBlowup.chartι (Ideal.map φ.toRingHom centerIdeal)
        (mappedElement centerIdeal φ.toRingHom centerU) ≫
      AffineBlowup.toSpec (Ideal.map φ.toRingHom centerIdeal)).base ⁻¹'
      (PrimeSpectrum.zeroLocus {φ vCoord} \
        PrimeSpectrum.zeroLocus (Ideal.map φ.toRingHom centerIdeal : Set S))) =
      PrimeSpectrum.zeroLocus {fractionCoordinate k φ} := by
  change closure ((AffineBlowup.chartι (Ideal.map φ.toRingHom centerIdeal)
        (mappedElement centerIdeal φ.toRingHom centerU) ≫
      AffineBlowup.toSpec (Ideal.map φ.toRingHom centerIdeal)).base ⁻¹'
      (PrimeSpectrum.zeroLocus
          {(mappedElement centerIdeal φ.toRingHom centerV : S)} \
        PrimeSpectrum.zeroLocus (Ideal.map φ.toRingHom centerIdeal : Set S))) = _
  rw [chart_second_branch_off_center]
  exact fraction_zeroLocus_closure k φ

end KltDP.Geometry.SmoothPointBlowupChartBasis
