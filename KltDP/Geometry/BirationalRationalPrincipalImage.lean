import KltDP.Geometry.BirationalRationalWeilPushforward
import KltDP.Geometry.BirationalPrincipalPushforwardSource
import KltDP.Geometry.CartierPicardEndpointRationalClasses
import Mathlib.LinearAlgebra.Span.Basic

/-!
# Exact image of the original rational principal submodule

The original proper birational pushforward maps the source rational
principal submodule onto the target rational principal submodule. The
forward inclusion uses the inverse of the original function-field map;
the reverse inclusion uses that original map itself. No Cartier descent
or numerical-class identification is assumed.
-/

set_option autoImplicit false

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.BirationalWeilPushforward

variable {k : Type u} [Field k] {S X : NormalProjectiveSurface k}
  (π : S.toScheme ⟶ X.toScheme) [IsProper π] (hbir : IsBirationalScheme π)

/-- Every original source principal divisor has an actual target principal
image, after the original coefficient rationalization. -/
theorem rationalPushforward_principal_exists (f : S.toScheme.functionFieldˣ) :
    ∃ g : X.toScheme.functionFieldˣ,
      rationalPushforward π hbir (S.rationalPrincipalDivisorHom (Additive.ofMul f)) =
        X.rationalPrincipalDivisorHom (Additive.ofMul g) := by
  obtain ⟨g, hg⟩ := pushforward_principalDivisor_exists π hbir f
  refine ⟨g, ?_⟩
  change rationalPushforward π hbir
    (NormalProjectiveSurface.rationalizeWeilDivisor S (S.principalDivisor f)) = _
  exact (rationalPushforward_rationalize π hbir (S.principalDivisor f)).trans
    (congrArg (NormalProjectiveSurface.rationalizeWeilDivisor X) hg)

/-- The image is exactly the original rational principal submodule. -/
theorem rationalPushforward_map_principalSubmodule :
    S.rationalPrincipalSubmodule.map (rationalPushforward π hbir) =
      X.rationalPrincipalSubmodule := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    apply Submodule.span_le.mpr
    rintro _ ⟨f, rfl⟩
    change rationalPushforward π hbir (S.rationalPrincipalDivisorHom f) ∈
      X.rationalPrincipalSubmodule
    obtain ⟨g, hg⟩ := rationalPushforward_principal_exists π hbir f.toMul
    change rationalPushforward π hbir (S.rationalPrincipalDivisorHom f) =
      X.rationalPrincipalDivisorHom (Additive.ofMul g) at hg
    rw [hg]
    exact Submodule.subset_span ⟨Additive.ofMul g, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨f, rfl⟩
    letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
    let g := Units.map (functionFieldMap π).hom.toMonoidHom f.toMul
    refine ⟨S.rationalPrincipalDivisorHom (Additive.ofMul g),
      Submodule.subset_span ⟨Additive.ofMul g, rfl⟩, ?_⟩
    change rationalPushforward π hbir
      (NormalProjectiveSurface.rationalizeWeilDivisor S (S.principalDivisor g)) = _
    exact (rationalPushforward_rationalize π hbir (S.principalDivisor g)).trans
      (congrArg (NormalProjectiveSurface.rationalizeWeilDivisor X)
        (pushforward_principalDivisor π hbir f.toMul))

end KltDP.Geometry.BirationalWeilPushforward

#check @KltDP.Geometry.BirationalWeilPushforward.rationalPushforward_map_principalSubmodule
#print axioms KltDP.Geometry.BirationalWeilPushforward.rationalPushforward_map_principalSubmodule
