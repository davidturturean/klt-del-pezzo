import KltDP.Geometry.QCartierPullbackPrincipal

/-!
The existing Q-Cartier pullback transports an actual rational divisor
class relation with an original Cartier numerator. The proof uses the
already proved preservation of rational linear equivalence and the
original linear pullback, without constructing another class group.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.QCartierPullback

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y : NormalProjectiveSurface k}
    (π : X.toScheme ⟶ Y.toScheme) [GenericPointPreserving π]

/-- A rational class relation with an actual Cartier divisor pulls back
to the corresponding relation with its actual signed Cartier pullback. -/
theorem rationalWeilClassMap_pullback_eq_smul_cartier
    (D : Y.RationalWeilDivisor) (hD : Y.QCartier D)
    (B : CartierDivisor Y.toScheme) (c : ℚ)
    (hclass : Y.rationalWeilClassMap D =
      c • Y.rationalWeilClassMap (Y.rationalCartierToWeilHom B)) :
    X.rationalWeilClassMap (pullback π D hD) =
      c • X.rationalWeilClassMap
        (X.rationalCartierToWeilHom (DominantCartierPullback.pullbackHom π B)) := by
  let E : Y.rationalCartierSubmodule := c • Y.rationalCartierMap B
  have hlin : Y.QLinearlyEquivalent D (E : Y.RationalWeilDivisor) := by
    apply (Y.rationalWeilClassMap_eq_iff _ _).mp
    exact hclass.trans (Y.rationalWeilClassMap.map_smul c
      (Y.rationalCartierToWeilHom B)).symm
  have hp := pullback_qLinearlyEquivalent π D (E : Y.RationalWeilDivisor)
    hD E.property hlin
  have heq : pullback π (E : Y.RationalWeilDivisor) E.property =
      c • X.rationalCartierToWeilHom (DominantCartierPullback.pullbackHom π B) := by
    change pullbackToWeil π (c • Y.rationalCartierMap B) = _
    rw [map_smul, pullbackToWeil_cartier]
  exact ((X.rationalWeilClassMap_eq_iff _ _).mpr hp).trans
    ((congrArg X.rationalWeilClassMap heq).trans (X.rationalWeilClassMap.map_smul _ _))

end KltDP.Geometry.QCartierPullback
