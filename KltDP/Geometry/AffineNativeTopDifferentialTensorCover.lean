import KltDP.Geometry.AffineNativeTopDifferentialIdealTensor
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# The actual intrinsic tensor factor on an original principal cover

An ordinary family adapter applies the proved sheaf construction to each
actual native factor. Keeping the coefficient ring abstract retains the exact
original maps while avoiding reconstruction of concrete Rees-ring carriers.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory

namespace KltDP.Geometry.AffineNativeTopDifferential

open AffineKaehlerTildeDerivation AffineTopDifferentialFrame
open AffineNativeTopDifferentialIdealTensor

universe u

local instance targetMonoidal (R : Type u) [CommRing R] :
    MonoidalCategory (Spec (CommRingCat.of R)).Modules := Scheme.Modules.monoidalCategory _

variable (k : Type u) [CommRing k]
variable {A C : Type u} [CommRing A] [CommRing C] [Algebra k A] [Algebra k C]
variable (ψ : ∀ r : C, A →ₐ[k] Localization.Away r)
variable (J : ∀ r : C, Ideal (Localization.Away r))
variable (β : Basis (Fin 2) A (KaehlerDifferential k A)) (x : Fin 2 → A)
variable (hx : ∀ i, β i = KaehlerDifferential.D k A (x i))

include hx in
/-- A proved native factor on an actual principal neighborhood gives the
whole original intrinsic tensor factor on the same neighborhood. -/
theorem exists_tensor_factor_on_principal_cover (p : PrimeSpectrum C)
    (hcover : ∃ r : C, r ∉ p.asIdeal ∧
      ∃ γ : Basis (Fin 2) (Localization.Away r)
          (KaehlerDifferential k (Localization.Away r)),
      ∃ e : (ModuleCat.extendScalars (ψ r).toRingHom).obj
          ((differentialModule k A).exteriorPower 2) ≃ₗ[Localization.Away r] J r,
        (determinantEquiv γ).symm.toLinearMap.comp
          ((J r).subtype.comp e.toLinearMap) = (map k (ψ r) 2).hom) :
    ∃ r : C, r ∉ p.asIdeal ∧
      ∃ e : (schemeModulePullback (Spec.map (CommRingCat.ofHom (ψ r).toRingHom))).obj
          (intrinsic k A 2) ≅
            (ModuleCat.of (Localization.Away r) (J r)).tilde ⊗ intrinsic k (Localization.Away r) 2,
        e.hom ≫ tensorInclusion k (Localization.Away r) (J r) = intrinsicMap k (ψ r) 2 := by
  obtain ⟨r, hr, γ, e, he⟩ := hcover
  exact ⟨r, hr, tensorIso k (Localization.Away r) γ (J r) (ψ r) β e,
    tensorIso_factor k (Localization.Away r) γ (J r) (ψ r) β e he x hx⟩

end KltDP.Geometry.AffineNativeTopDifferential
