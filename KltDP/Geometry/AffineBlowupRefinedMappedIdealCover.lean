import KltDP.Geometry.AffineBlowupRefinedFactorCover

/-!
# Refinement with the original mapped ideal kept abstract

The supplied native factor uses `Ideal.map (ψ r).toRingHom I`. The original
refined-center ideal uses the composite localization and Rees-chart map.
Their equality is transported once, while these maps remain abstract, before
applying the existing global-map refinement theorem. No local factor or map
compatibility is added to the final smooth-point theorem's assumptions.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Geometry.AffineBlowupTopDifferential

open AffineBlowup AffineNativeTopDifferential

local instance mappedCoverModuleTensor (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

variable (k R : Type u) [Field k] [CommRing R] [Algebra k R] (I : Ideal R) (a : I)
variable [Algebra k (chartRing I a)]
variable (ψ : ∀ r : chartRing I a, R →ₐ[k] Localization.Away r)
variable (hψ : ∀ r, (algebraMap (chartRing I a) (Localization.Away r)).comp
  (chartBaseMap I a) = (ψ r).toRingHom)

include hψ in
/-- The original mapped-center native factor yields the unchanged original global factor. -/
theorem exists_refined_factor_of_mapped_ideal (p : PrimeSpectrum (chartRing I a))
    (hnative : ∃ r : chartRing I a, r ∉ p.asIdeal ∧
      ∃ e : (schemeModulePullback (Spec.map (CommRingCat.ofHom (ψ r).toRingHom))).obj
          (intrinsic k R 2) ≅
        (ModuleCat.of (Localization.Away r)
          (Ideal.map (ψ r).toRingHom I)).tilde ⊗ intrinsic k (Localization.Away r) 2,
        e.hom ≫ AffineNativeTopDifferentialIdealTensor.tensorInclusion
            k (Localization.Away r) (Ideal.map (ψ r).toRingHom I) =
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
  apply exists_refined_factor_on_principal_cover k R I a ψ hψ p
  obtain ⟨r, hr, e, he⟩ := hnative
  refine ⟨r, hr, ?_⟩
  have hI : refinedCenterIdeal I a (algebraMap (chartRing I a) (Localization.Away r)) =
      Ideal.map (ψ r).toRingHom I :=
    congrArg (fun q : R →+* Localization.Away r => Ideal.map q I) (hψ r)
  rw [hI]
  exact ⟨e, he⟩

#print axioms exists_refined_factor_of_mapped_ideal

end KltDP.Geometry.AffineBlowupTopDifferential
