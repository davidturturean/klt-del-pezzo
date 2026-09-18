import KltDP.Geometry.AffineBlowupRefinedTensorFactor
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Normalized global-map factors on an original principal chart cover

The actual native factors on the principal refinements are transported to
pullbacks of the original global source and exceptional tensor. Localization
derives both open immersion and regularity; neither is an additional input.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Geometry.AffineBlowupTopDifferential

open AffineBlowup AffineNativeTopDifferential

local instance coverModuleTensor (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

variable (k R : Type u) [Field k] [CommRing R] [Algebra k R] (I : Ideal R) (a : I)
variable [Algebra k (chartRing I a)]
variable (ψ : ∀ r : chartRing I a, R →ₐ[k] Localization.Away r)
variable (hψ : ∀ r, (algebraMap (chartRing I a) (Localization.Away r)).comp
  (chartBaseMap I a) = (ψ r).toRingHom)

include hψ in
/-- The original refined factors preserve the original global differential and inclusion. -/
theorem exists_refined_factor_on_principal_cover (p : PrimeSpectrum (chartRing I a))
    (hnative : ∃ r : chartRing I a, r ∉ p.asIdeal ∧
      ∃ e : (schemeModulePullback (Spec.map (CommRingCat.ofHom (ψ r).toRingHom))).obj
          (intrinsic k R 2) ≅
        (ModuleCat.of (Localization.Away r)
          (refinedCenterIdeal I a (algebraMap (chartRing I a) (Localization.Away r)))).tilde ⊗
            intrinsic k (Localization.Away r) 2,
        e.hom ≫ AffineNativeTopDifferentialIdealTensor.tensorInclusion
            k (Localization.Away r)
            (refinedCenterIdeal I a (algebraMap (chartRing I a) (Localization.Away r))) =
          intrinsicMap k (ψ r) 2) :
    ∃ r : chartRing I a, r ∉ p.asIdeal ∧
      ∃ e : (schemeModulePullback
          (refinedChartMap I a (algebraMap (chartRing I a) (Localization.Away r)))).obj
          ((schemeModulePullback (toSpec I)).obj (intrinsic k R 2)) ≅
        (schemeModulePullback
          (refinedChartMap I a (algebraMap (chartRing I a) (Localization.Away r)))).obj
          (exceptionalTensor k R I),
        e.hom ≫ (schemeModulePullback
            (refinedChartMap I a (algebraMap (chartRing I a) (Localization.Away r)))).map
            (exceptionalInclusion k R I) =
          (schemeModulePullback
            (refinedChartMap I a (algebraMap (chartRing I a) (Localization.Away r)))).map
            (blowdownMap k R I) := by
  obtain ⟨r, hr, e, he⟩ := hnative
  let θ := algebraMap (chartRing I a) (Localization.Away r)
  have hregular : θ (chartBaseMap I a (a : R)) ∈ nonZeroDivisors (Localization.Away r) :=
    IsLocalization.nonZeroDivisors_le_comap (Submonoid.powers r) (Localization.Away r)
      (chartBaseMap_equation_mem_nonZeroDivisors I a)
  letI : IsOpenImmersion (Spec.map (CommRingCat.ofHom θ)) :=
    IsOpenImmersion.of_isLocalization r
  letI : IsOpenImmersion (refinedChartMap I a θ) := by
    change IsOpenImmersion (Spec.map (CommRingCat.ofHom θ) ≫ chartι I a)
    infer_instance
  exact ⟨r, hr, refinedFactorIso k R I a θ (ψ r) (hψ r) hregular e,
    refinedFactorIso_factor k R I a θ (ψ r) (hψ r) hregular e he⟩

end KltDP.Geometry.AffineBlowupTopDifferential
