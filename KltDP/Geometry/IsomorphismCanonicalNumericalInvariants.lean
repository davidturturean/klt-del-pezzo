import KltDP.Geometry.BirationalCartierIntersectionPullback
import KltDP.Geometry.BirationalNumericalPullback
import KltDP.Geometry.CanonicalRationalCoordinateOpenPullback
import KltDP.Geometry.SurfaceNumericalFinitenessProved

/-!
# Canonical square and numerical rank under the original isomorphism

Both original numerical pullbacks are injective. The canonical Cartier
comparison uses the actual open differential pullback isomorphism, then the
proved original Cartier intersection projection formula.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.IsomorphismSurfaceInvariants

open SmoothCanonicalExteriorComparison

variable {k : Type u} [Field k] [IsAlgClosed k]
  {S T : NormalProjectiveSurface k} (f : S.toScheme ⟶ T.toScheme) [IsIso f]
  (hf : f ≫ T.structureMorphism = S.structureMorphism)
  (hS : ∀ s : S.Point, RegularPoint S.toScheme s)
  (hT : ∀ t : T.Point, RegularPoint T.toScheme t)

include hf hS hT in
/-- The dimensions are those of the two original numerical Picard quotients. -/
theorem picardRank_eq : S.picardRank = T.picardRank := by
  letI : FiniteDimensional ℚ S.NumericalClassGroup :=
    SurfaceNumericalFinitenessProved.numericalClassGroup_finite S hS
  letI : FiniteDimensional ℚ T.NumericalClassGroup :=
    SurfaceNumericalFinitenessProved.numericalClassGroup_finite T hT
  have hbir : IsBirationalScheme f :=
    ⟨genericPoint_eq_of_isOpenImmersion f, inferInstance⟩
  have hbirinv : IsBirationalScheme (inv f) :=
    ⟨genericPoint_eq_of_isOpenImmersion (inv f), inferInstance⟩
  have hinv : inv f ≫ S.structureMorphism = T.structureMorphism := by
    rw [← hf, IsIso.inv_hom_id_assoc]
  apply Nat.le_antisymm
  · exact LinearMap.finrank_le_finrank_of_injective
      (BirationalNumericalPullback.pullback_injective (inv f) hinv hbirinv)
  · exact LinearMap.finrank_le_finrank_of_injective
      (BirationalNumericalPullback.pullback_injective f hf hbir)

include f hf in
/-- Arbitrary original canonical Cartier representatives have the same square
under the original isomorphism over the field. -/
theorem canonical_square_eq
    (KS : CartierDivisor S.toScheme) (KT : CartierDivisor T.toScheme)
    (eKS : cartierDivisorModule S.toScheme KS ≅
      relativeDifferentialExterior S.structureMorphism 2)
    (eKT : cartierDivisorModule T.toScheme KT ≅
      relativeDifferentialExterior T.structureMorphism 2) :
    S.intersectionPairing hS KS KS = T.intersectionPairing hT KT KT := by
  letI : GenericPointPreserving f := ⟨genericPoint_eq_of_isOpenImmersion f⟩
  have hbir : IsBirationalScheme f :=
    ⟨genericPoint_eq_of_isOpenImmersion f, inferInstance⟩
  let D := DominantCartierPullback.pullbackHom f KT
  have hclass : cartierPicardClass S.toScheme KS = cartierPicardClass S.toScheme D :=
    cartierPicardClass_eq_of_iso S.toScheme KS D
      (eKS ≪≫ (CartierRationalCoordinate.canonicalOpenPullbackIso
        f T.structureMorphism S.structureMorphism hf KT eKT).symm)
  calc
    S.intersectionPairing hS KS KS =
        S.picardPairing hS (cartierPicardClass S.toScheme KS)
          (cartierPicardClass S.toScheme KS) := (S.picardPairing_class hS KS KS).symm
    _ = S.picardPairing hS (cartierPicardClass S.toScheme D)
          (cartierPicardClass S.toScheme D) := by rw [hclass]
    _ = S.intersectionPairing hS D D := S.picardPairing_class hS D D
    _ = T.intersectionPairing hT KT KT :=
      BirationalCartierIntersectionPullback.intersectionPairing_pullback
        f hf hbir hS hT KT KT

end KltDP.Geometry.IsomorphismSurfaceInvariants

#check @KltDP.Geometry.IsomorphismSurfaceInvariants.picardRank_eq
#check @KltDP.Geometry.IsomorphismSurfaceInvariants.canonical_square_eq
#print axioms KltDP.Geometry.IsomorphismSurfaceInvariants.picardRank_eq
#print axioms KltDP.Geometry.IsomorphismSurfaceInvariants.canonical_square_eq
