import KltDP.Geometry.AffineBlowupRefinedFactorCover

/-!
# Transport the actual native ideal family before specializing the factor

This ordinary equality-elimination adapter keeps the original maps and
inclusions. The ideal equality is checked independently of the full sheaf
factor proposition, whose coefficient ring remains abstract in this proof.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Geometry.AffineBlowupTopDifferential

open AffineBlowup AffineNativeTopDifferential

local instance idealTransportModuleTensor (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

variable (k R : Type u) [Field k] [CommRing R] [Algebra k R] (I : Ideal R) (a : I)
variable [Algebra k (chartRing I a)]
variable (ψ : ∀ r : chartRing I a, R →ₐ[k] Localization.Away r)
variable (hψ : ∀ r, (algebraMap (chartRing I a) (Localization.Away r)).comp
  (chartBaseMap I a) = (ψ r).toRingHom)

include hψ in
/-- A proved equality of original ideal families transports the actual native
factor to the original global-map factor without a new compatibility premise. -/
theorem exists_refined_factor_on_principal_cover_of_ideal_eq
    (J : ∀ r : chartRing I a, @Ideal (Localization.Away r)
      (inferInstance : CommRing (Localization.Away r)).toSemiring)
    (hJ : J = fun r : chartRing I a => refinedCenterIdeal I a
      (algebraMap (chartRing I a) (Localization.Away r)))
    (p : PrimeSpectrum (chartRing I a))
    (hnative : ∃ r : chartRing I a, r ∉ p.asIdeal ∧
      ∃ e : (schemeModulePullback (Spec.map (CommRingCat.ofHom (ψ r).toRingHom))).obj
          (intrinsic k R 2) ≅
        (ModuleCat.of (Localization.Away r)
          (J r)).tilde ⊗
            intrinsic k (Localization.Away r) 2,
        e.hom ≫ AffineNativeTopDifferentialIdealTensor.tensorInclusion
            k (Localization.Away r)
            (J r) =
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
  subst J
  exact exists_refined_factor_on_principal_cover k R I a ψ hψ p hnative

end KltDP.Geometry.AffineBlowupTopDifferential
