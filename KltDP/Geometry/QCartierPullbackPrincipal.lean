import KltDP.Geometry.QCartierPullback
import KltDP.Geometry.CartierPicardEndpointRationalClasses

/-!
The localized pullback takes each original principal Cartier numerator
to the principal numerator of its actual function-field image. Positive
denominator clearing then proves preservation of the existing rational
principal submodule and of the existing rational linear equivalence.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry

namespace NormalProjectiveSurface

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)

/-- Rationalization retains the original principal Cartier-Weil comparison. -/
@[simp]
theorem rationalCartierToWeilHom_principal (f : X.toScheme.functionFieldˣ) :
    X.rationalCartierToWeilHom (principalCartierDivisorHom X.toScheme (Additive.ofMul f)) =
      X.rationalPrincipalDivisorHom (Additive.ofMul f) :=
  congrArg (rationalizeWeilDivisor X) (X.cartierToWeilHom_principal f)

end NormalProjectiveSurface

namespace QCartierPullback

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y : NormalProjectiveSurface k}
variable (π : X.toScheme ⟶ Y.toScheme) [GenericPointPreserving π]

/-- The actual rational principal numerator pulls back by the original
generic-stalk function-field homomorphism. -/
theorem pullbackToWeil_principal (f : Y.toScheme.functionFieldˣ) :
    pullbackToWeil π
        (Y.rationalCartierMap (principalCartierDivisorHom Y.toScheme (Additive.ofMul f))) =
      X.rationalPrincipalDivisorHom
        (Additive.ofMul (Units.map (functionFieldMap π).hom.toMonoidHom f)) := by
  rw [pullbackToWeil_cartier, DominantCartierPullback.pullbackHom_principal,
    NormalProjectiveSurface.rationalCartierToWeilHom_principal]

/-- Rationally principal divisors remain in the original rational
principal submodule after pullback. -/
theorem pullbackToWeil_mem_principal (D : Y.rationalCartierSubmodule)
    (hD : (D : Y.RationalWeilDivisor) ∈ Y.rationalPrincipalSubmodule) :
    pullbackToWeil π D ∈ X.rationalPrincipalSubmodule := by
  have hlin : Y.QLinearlyEquivalent (D : Y.RationalWeilDivisor) 0 := by
    simpa only [NormalProjectiveSurface.QLinearlyEquivalent, sub_zero] using hD
  obtain ⟨n, hn, f, hf⟩ :=
    (Y.qLinearlyEquivalent_iff_positive_principal_multiple (D : Y.RationalWeilDivisor) 0).mp hlin
  have hA : Y.rationalCartierToWeilHom
      (principalCartierDivisorHom Y.toScheme (Additive.ofMul f)) =
        n • (D : Y.RationalWeilDivisor) := by
    rw [NormalProjectiveSurface.rationalCartierToWeilHom_principal]
    simpa only [sub_zero] using hf.symm
  rw [pullbackToWeil_eq_of_positive_multiple π D n hn _ hA,
    DominantCartierPullback.pullbackHom_principal,
    NormalProjectiveSurface.rationalCartierToWeilHom_principal]
  exact X.rationalPrincipalSubmodule.smul_mem ((n : ℚ)⁻¹)
    (Submodule.subset_span
      ⟨Additive.ofMul (Units.map (functionFieldMap π).hom.toMonoidHom f), rfl⟩)

/-- Pullback preserves the existing rational linear equivalence of
original Q-Cartier Weil divisors. -/
theorem pullback_qLinearlyEquivalent (D E : Y.RationalWeilDivisor)
    (hD : Y.QCartier D) (hE : Y.QCartier E) (h : Y.QLinearlyEquivalent D E) :
    X.QLinearlyEquivalent (pullback π D hD) (pullback π E hE) := by
  let D' : Y.rationalCartierSubmodule := ⟨D, hD⟩
  let E' : Y.rationalCartierSubmodule := ⟨E, hE⟩
  have hmem : ((D' - E' : Y.rationalCartierSubmodule) : Y.RationalWeilDivisor) ∈
      Y.rationalPrincipalSubmodule := by
    change D - E ∈ Y.rationalPrincipalSubmodule
    exact h
  have hp := pullbackToWeil_mem_principal (X := X) (Y := Y) π (D' - E') hmem
  change pullbackToWeil π ⟨D, hD⟩ - pullbackToWeil π ⟨E, hE⟩ ∈
    X.rationalPrincipalSubmodule
  simpa only [map_sub] using hp

end QCartierPullback

end KltDP.Geometry
