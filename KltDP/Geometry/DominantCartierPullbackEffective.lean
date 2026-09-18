import KltDP.Geometry.DominantCartierRegularPullback
import KltDP.Geometry.SectionEffectiveWeil

/-!
# Nonnegative coefficients for the original signed pullback

The accepted original signed pullback preserves regular equations. The
accepted DVR order calculation therefore supplies nonnegative coefficients
at every actual source prime, without a multiplicity premise.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.DominantCartierPullback

/-- At each actual source prime, a pulled regular equation has nonnegative order. -/
theorem pullbackHom_effective_of_regularEquations
    {k : Type u} [Field k] {X Y : NormalProjectiveSurface k}
    (π : X.toScheme ⟶ Y.toScheme) [GenericPointPreserving π]
    (D : CartierDivisor Y.toScheme) (hD : HasRegularCartierEquations Y.toScheme D) :
    NormalProjectiveSurface.EffectiveDivisor (X.cartierToWeilHom (pullbackHom π D)) :=
  X.effective_cartierToWeilHom_of_regularEquations (pullbackHom π D)
    (pullbackHom_hasRegularEquations π D hD)

end KltDP.Geometry.DominantCartierPullback
