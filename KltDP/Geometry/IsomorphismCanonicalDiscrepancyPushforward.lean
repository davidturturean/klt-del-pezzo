import KltDP.Geometry.IsomorphismCanonicalDiscrepancyBoundary
import KltDP.Geometry.BirationalCartierPullbackPushforward

/-!
# The canonical isomorphism step retains the exact original Weil divisor

All data refer to the literal signed Cartier pullbacks. The original
proper birational pushforward recovers the original canonical numerator.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.IsomorphismDiscrepancy

open SmoothCanonicalExteriorComparison (relativeDifferentialExterior)

variable {k : Type u} [Field k] [IsAlgClosed k]
  {S T X : NormalProjectiveSurface k}

local instance : IsLocallyNoetherian S.toScheme := S.isLocallyNoetherian
local instance : IsLocallyNoetherian T.toScheme := T.isLocallyNoetherian

theorem iso_isBirational (e : S.toScheme ≅ T.toScheme) : IsBirationalScheme e.hom :=
  ⟨genericPoint_eq_of_isOpenImmersion e.hom, inferInstance⟩

theorem pullback_canonical_boundary_with_pushforward
    (e : S.toScheme ≅ T.toScheme)
    (hover : e.hom ≫ T.structureMorphism = S.structureMorphism)
    (g : T.toScheme ⟶ X.toScheme) [GenericPointPreserving g]
    (K : CartierDivisor T.toScheme)
    (eK : cartierDivisorModule T.toScheme K ≅
      relativeDifferentialExterior T.structureMorphism 2)
    (B : X.RationalWeilDivisor) (hB : X.QCartier B)
    (A : CartierDivisor T.toScheme)
    (hA : IsStrictNormalCrossingsCartier T.toScheme A)
    (hcoeff : ∀ C : T.PrimeCurve,
      T.cartierToWeilHom A C = 0 ∨ T.cartierToWeilHom A C = 1)
    (hsupport : (T.rationalCartierToWeilHom K - QCartierPullback.pullback g B hB).support ⊆
      (T.cartierToWeilHom A).support)
    (hbound : ∀ C : T.PrimeCurve,
      (-1 : ℚ) < (T.rationalCartierToWeilHom K - QCartierPullback.pullback g B hB) C) :
    letI : GenericPointPreserving e.hom := ⟨genericPoint_eq_of_isOpenImmersion e.hom⟩
    let K' := DominantCartierPullback.pullbackHom e.hom K
    let A' := DominantCartierPullback.pullbackHom e.hom A
    Nonempty (cartierDivisorModule S.toScheme K' ≅
      relativeDifferentialExterior S.structureMorphism 2) ∧
    BirationalWeilPushforward.pushforward e.hom (iso_isBirational e)
      (S.cartierToWeilHom K') = T.cartierToWeilHom K ∧
    IsStrictNormalCrossingsCartier S.toScheme A' ∧
    (∀ C : S.PrimeCurve,
      S.cartierToWeilHom A' C = 0 ∨ S.cartierToWeilHom A' C = 1) ∧
    (S.rationalCartierToWeilHom K' -
        QCartierPullback.pullback (e.hom ≫ g) B hB).support ⊆
      (S.cartierToWeilHom A').support ∧
    ∀ C : S.PrimeCurve,
      (-1 : ℚ) < (S.rationalCartierToWeilHom K' -
        QCartierPullback.pullback (e.hom ≫ g) B hB) C := by
  letI : GenericPointPreserving e.hom := ⟨genericPoint_eq_of_isOpenImmersion e.hom⟩
  exact ⟨⟨CanonicalCartierOpenPullback.canonicalModuleIso e.hom
      T.structureMorphism S.structureMorphism hover K eK⟩,
    BirationalWeilPushforward.pushforward_cartier_pullback e.hom (iso_isBirational e) K,
    DominantCartierPullback.isStrictNormalCrossingsCartier_of_iso e A hA,
    pullback_boundary_data e g K B hB A hcoeff hsupport hbound⟩

end KltDP.Geometry.IsomorphismDiscrepancy

#check @KltDP.Geometry.IsomorphismDiscrepancy.pullback_canonical_boundary_with_pushforward
#print axioms KltDP.Geometry.IsomorphismDiscrepancy.pullback_canonical_boundary_with_pushforward
