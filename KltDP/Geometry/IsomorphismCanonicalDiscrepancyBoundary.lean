import KltDP.Geometry.CanonicalCartierOpenPullback
import KltDP.Geometry.StrictNormalCrossingsOpenPullback
import KltDP.Geometry.IsomorphismDiscrepancySupport

/-!
# The original canonical discrepancy boundary under a surface isomorphism

The original field triangle transports the canonical module, and the
original prime correspondence transports both the boundary and all
discrepancy coefficients. This includes the empty point-blowup sequence.
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

theorem exists_canonical_discrepancy_boundary
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
    ∃ (K' A' : CartierDivisor S.toScheme),
      Nonempty (cartierDivisorModule S.toScheme K' ≅
        relativeDifferentialExterior S.structureMorphism 2) ∧
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
  let K' := DominantCartierPullback.pullbackHom e.hom K
  let A' := DominantCartierPullback.pullbackHom e.hom A
  refine ⟨K', A', ⟨?_⟩, ?_, ?_⟩
  · exact CanonicalCartierOpenPullback.canonicalModuleIso e.hom
      T.structureMorphism S.structureMorphism hover K eK
  · exact DominantCartierPullback.isStrictNormalCrossingsCartier_of_iso e A hA
  · exact pullback_boundary_data e g K B hB A hcoeff hsupport hbound

end KltDP.Geometry.IsomorphismDiscrepancy

#check @KltDP.Geometry.IsomorphismDiscrepancy.exists_canonical_discrepancy_boundary
#print axioms KltDP.Geometry.IsomorphismDiscrepancy.exists_canonical_discrepancy_boundary
