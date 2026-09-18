import KltDP.Geometry.AffineNativeTopDifferentialImage
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Carry the actual native image factor across an original principal cover

Keep the coefficient ring abstract while constructing the dependent ideal
factor. The supplied maps, ideals, functions, and basis cover are unchanged;
the existing native image theorem derives the whole factor on one of those
original principal neighborhoods.
-/

noncomputable section

namespace KltDP.Geometry.AffineNativeTopDifferential

open AffineKaehlerTildeDerivation AffineTopDifferentialFrame

universe u

private theorem inclusion_ofEq {R : Type u} [CommRing R]
    (I J : Ideal R) (h : I = J) :
    J.subtype.comp (LinearEquiv.ofEq I J h).toLinearMap = I.subtype := by
  cases h
  rfl

variable (k : Type u) [CommRing k]
variable {A C : Type u} [CommRing A] [CommRing C] [Algebra k A] [Algebra k C]
variable (ψ : ∀ r : C, A →ₐ[k] Localization.Away r)
variable (J : ∀ r : C, Ideal (Localization.Away r))
variable (β : Basis (Fin 2) A (KaehlerDifferential k A)) (a b : A) (s t : C)
variable (hβ0 : β 0 = KaehlerDifferential.D k A a)
variable (hβ1 : β 1 = KaehlerDifferential.D k A b)
variable (hs : ∀ r, ψ r a = algebraMap C (Localization.Away r) s)
variable (hrel : ∀ r, ψ r a * algebraMap C (Localization.Away r) t = ψ r b)
variable (hregular : ∀ r, ψ r a ∈ nonZeroDivisors (Localization.Away r))
variable (hJ : ∀ r, J r = Ideal.span {ψ r a})

include hβ0 hβ1 hs hrel hregular hJ in
/-- The original principal basis cover and original relation determine the
entire native image factor, without an image or injectivity premise. -/
theorem exists_factor_on_principal_cover (p : PrimeSpectrum C)
    (hcover : ∃ r : C, r ∉ p.asIdeal ∧
      ∃ γ : Basis (Fin 2) (Localization.Away r)
          (KaehlerDifferential k (Localization.Away r)),
        γ 0 = KaehlerDifferential.D k (Localization.Away r)
          (algebraMap C (Localization.Away r) s) ∧
        γ 1 = KaehlerDifferential.D k (Localization.Away r)
          (algebraMap C (Localization.Away r) t)) :
    ∃ r : C, r ∉ p.asIdeal ∧
      ∃ γ : Basis (Fin 2) (Localization.Away r)
          (KaehlerDifferential k (Localization.Away r)),
      ∃ e : (ModuleCat.extendScalars (ψ r).toRingHom).obj
          ((differentialModule k A).exteriorPower 2) ≃ₗ[Localization.Away r] J r,
        (determinantEquiv γ).symm.toLinearMap.comp
          ((J r).subtype.comp e.toLinearMap) = (map k (ψ r) 2).hom := by
  obtain ⟨r, hr, γ, hγ0, hγ1⟩ := hcover
  have hγ0' : γ 0 = KaehlerDifferential.D k (Localization.Away r) (ψ r a) :=
    hγ0.trans (congrArg (KaehlerDifferential.D k (Localization.Away r)) (hs r).symm)
  let e₀ := parameterIdealEquiv k (ψ r) β γ a b
    (algebraMap C (Localization.Away r) t) hβ0 hβ1 hγ0' hγ1 (hrel r) (hregular r)
  let e := e₀.trans (LinearEquiv.ofEq _ _ (hJ r).symm)
  refine ⟨r, hr, γ, e, ?_⟩
  have he : (J r).subtype.comp e.toLinearMap =
      (Ideal.span {ψ r a}).subtype.comp e₀.toLinearMap := by
    change (J r).subtype.comp
      ((LinearEquiv.ofEq _ _ (hJ r).symm).toLinearMap.comp e₀.toLinearMap) = _
    rw [← LinearMap.comp_assoc, inclusion_ofEq]
  rw [he]
  exact map_factor k (ψ r) β γ a b (algebraMap C (Localization.Away r) t)
    hβ0 hβ1 hγ0' hγ1 (hrel r) (hregular r)

end KltDP.Geometry.AffineNativeTopDifferential
