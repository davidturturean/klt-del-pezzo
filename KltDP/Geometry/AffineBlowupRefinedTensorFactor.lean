import KltDP.Geometry.AffineBlowupExceptionalTopTensor
import KltDP.Geometry.AffineNativeTopDifferentialIdealTensor

/-!
# The original normalized exceptional tensor factor on a refined chart

Compose the original source-composition map, the already proved local native
factor, and the original global-kernel tensor comparison. Their whole-map
equations give the normalized factor required by the existing global theorem.
This ordinary adapter is later supplied with the derived actual chart factors.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Geometry.AffineBlowupTopDifferential

open AffineBlowup AffineNativeTopDifferential

local instance refinedModuleTensor (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

private theorem normalizedFactorIso_comp {C : Type*} [Category C]
    {A B D T U V : C} (s : A ≅ B) (e : B ≅ D) (t : T ≅ D) (u : U ≅ V)
    (a : A ⟶ U) (b : T ⟶ U) (m : B ⟶ V) (j : D ⟶ V)
    (he : e.hom ≫ j = m) (ht : t.hom ≫ j = b ≫ u.hom)
    (hs : a ≫ u.hom = s.hom ≫ m) :
    (s ≪≫ e ≪≫ t.symm).hom ≫ b = a := by
  apply (cancel_mono u.hom).mp
  rw [Category.assoc, ← ht]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
  rw [he, hs]

private theorem tensorInclusion_eq_structure (k B : Type u)
    [CommRing k] [CommRing B] [Algebra k B] (J : Ideal B) :
    AffineNativeTopDifferentialIdealTensor.tensorInclusion k B J =
      schemeStructureTensorInclusion (AffinePrincipalIdealTildeFrame.inclusion J)
        (intrinsic k B 2) := by
  simp only [AffineNativeTopDifferentialIdealTensor.tensorInclusion,
    AffineNativeTopDifferentialIdealTensor.idealInclusionSheaf,
    AffineNativeTopDifferentialIdealTensor.inclusionMorphism,
    AffineNativeTopDifferentialIdealTensor.ringTildeUnitIso,
    AffinePrincipalIdealTildeFrame.inclusion, schemeStructureTensorInclusion,
    Iso.trans_hom, Category.assoc]

variable (k R : Type u) [Field k] [CommRing R] [Algebra k R] (I : Ideal R) (a : I)
variable {B : Type u} [CommRing B] [Algebra k B]
variable (θ : chartRing I a →+* B) (ψ : R →ₐ[k] B)
variable (hψ : θ.comp (chartBaseMap I a) = ψ.toRingHom)
variable (hregular : θ (chartBaseMap I a (a : R)) ∈ nonZeroDivisors B)

include hψ in
theorem refinedChartMap_toSpec :
    refinedChartMap I a θ ≫ toSpec I = Spec.map (CommRingCat.ofHom ψ.toRingHom) := by
  rw [refinedChartMap, Category.assoc, chartι_toSpec, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  change Spec.map (CommRingCat.ofHom (θ.comp (chartBaseMap I a))) = _
  rw [hψ]

variable [IsOpenImmersion (refinedChartMap I a θ)]

/-- The two original geometric comparisons followed by the original tensorator. -/
def refinedTensorIso :
    (schemeModulePullback (refinedChartMap I a θ)).obj (exceptionalTensor k R I) ≅
      (ModuleCat.of B (refinedCenterIdeal I a θ)).tilde ⊗ intrinsic k B 2 :=
  schemeModulePullbackTensorIso (refinedChartMap I a θ)
      (exceptionalIdealModule I) (topSheaf k R I) ≪≫
    tensorIso (refinedIdealTildeGlobalIso I a θ hregular).symm
      (chartGlobalIso k R I ψ (refinedChartMap I a θ) (refinedChartMap_toSpec k R I a θ ψ hψ))

/-- The actual global tensor inclusion restricts to the same actual native ideal tensor inclusion. -/
theorem refinedTensorIso_inclusion :
    (refinedTensorIso k R I a θ ψ hψ hregular).hom ≫
        AffineNativeTopDifferentialIdealTensor.tensorInclusion k B (refinedCenterIdeal I a θ) =
      (schemeModulePullback (refinedChartMap I a θ)).map (exceptionalInclusion k R I) ≫
        (chartGlobalIso k R I ψ (refinedChartMap I a θ)
          (refinedChartMap_toSpec k R I a θ ψ hψ)).hom := by
  rw [tensorInclusion_eq_structure]
  exact schemeModulePullbackTensorIso_comparison_inclusion (refinedChartMap I a θ)
    (schemeKernelIdealι (exceptionalι I)) (topSheaf k R I)
    (refinedIdealTildeGlobalIso I a θ hregular)
    (chartGlobalIso k R I ψ (refinedChartMap I a θ) (refinedChartMap_toSpec k R I a θ ψ hψ))
    (AffinePrincipalIdealTildeFrame.inclusion (refinedCenterIdeal I a θ))
    (refinedIdealTildeGlobalIso_inclusion I a θ hregular)

variable (e : (schemeModulePullback (Spec.map (CommRingCat.ofHom ψ.toRingHom))).obj
  (intrinsic k R 2) ≅ (ModuleCat.of B (refinedCenterIdeal I a θ)).tilde ⊗ intrinsic k B 2)
variable (he : e.hom ≫
  AffineNativeTopDifferentialIdealTensor.tensorInclusion k B (refinedCenterIdeal I a θ) =
  intrinsicMap k ψ 2)

/-- The original global source and original exceptional tensor on this same refined chart. -/
def refinedFactorIso :
    (schemeModulePullback (refinedChartMap I a θ)).obj
        ((schemeModulePullback (toSpec I)).obj (intrinsic k R 2)) ≅
      (schemeModulePullback (refinedChartMap I a θ)).obj (exceptionalTensor k R I) :=
  chartSourceIso k R I ψ (refinedChartMap I a θ) (refinedChartMap_toSpec k R I a θ ψ hψ) ≪≫
    e ≪≫ (refinedTensorIso k R I a θ ψ hψ hregular).symm

include he in
/-- The whole original inclusion and blowdown differential agree under this actual factor. -/
theorem refinedFactorIso_factor :
    (refinedFactorIso k R I a θ ψ hψ hregular e).hom ≫
        (schemeModulePullback (refinedChartMap I a θ)).map (exceptionalInclusion k R I) =
      (schemeModulePullback (refinedChartMap I a θ)).map (blowdownMap k R I) := by
  exact normalizedFactorIso_comp
    (chartSourceIso k R I ψ (refinedChartMap I a θ)
      (refinedChartMap_toSpec k R I a θ ψ hψ)) e
    (refinedTensorIso k R I a θ ψ hψ hregular)
    (chartGlobalIso k R I ψ (refinedChartMap I a θ)
      (refinedChartMap_toSpec k R I a θ ψ hψ))
    ((schemeModulePullback (refinedChartMap I a θ)).map (blowdownMap k R I))
    ((schemeModulePullback (refinedChartMap I a θ)).map (exceptionalInclusion k R I))
    (intrinsicMap k ψ 2)
    (AffineNativeTopDifferentialIdealTensor.tensorInclusion k B (refinedCenterIdeal I a θ))
    he (refinedTensorIso_inclusion k R I a θ ψ hψ hregular) (by
      rw [chartGlobalIso_hom]
      exact chart_square k R I ψ (refinedChartMap I a θ)
        (refinedChartMap_toSpec k R I a θ ψ hψ))

end KltDP.Geometry.AffineBlowupTopDifferential
