import Mathlib.AlgebraicGeometry.AffineScheme

/-! The original principal affine chart contains the original point whenever
its denominator avoids the actual corresponding prime. -/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.AffinePrincipalNeighborhoodPoint

/-- This is the literal Spec-localization map composed with the original
fromSpec chart, with an actual source point mapping to x. -/
theorem exists_chart_point {Y : Scheme.{u}} (x : Y)
    {U : Y.Opens} (hU : IsAffineOpen U) (hx : x ∈ U)
    (r : Γ(Y, U)) (hr : r ∉ (hU.primeIdealOf ⟨x, hx⟩).asIdeal) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(Y, U) (Localization.Away r))) ≫ hU.fromSpec) ∧
    ∃ y : Spec (CommRingCat.of (Localization.Away r)),
      (Spec.map (CommRingCat.ofHom
        (algebraMap Γ(Y, U) (Localization.Away r))) ≫ hU.fromSpec).base y = x := by
  letI : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(Y, U) (Localization.Away r)))) :=
    IsOpenImmersion.of_isLocalization r
  have hp : hU.primeIdealOf ⟨x, hx⟩ ∈ Set.range
      (PrimeSpectrum.comap (algebraMap Γ(Y, U) (Localization.Away r))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
    exact hr
  obtain ⟨y, hy⟩ := hp
  refine ⟨inferInstance, y, ?_⟩
  change hU.fromSpec.base
    (PrimeSpectrum.comap (algebraMap Γ(Y, U) (Localization.Away r)) y) = x
  rw [hy]
  exact hU.fromSpec_primeIdealOf ⟨x, hx⟩

end KltDP.Geometry.AffinePrincipalNeighborhoodPoint
