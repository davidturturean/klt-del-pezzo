import KltDP.Geometry.ContractionCanonicalDifference
import KltDP.Geometry.CanonicalWeilBirationalRepresentative
import KltDP.Geometry.CanonicalWeilOfCartier
import KltDP.Geometry.BirationalPicardIntersectionPullback

/-!
# Canonical square under the original minus-one contraction

The compatible canonical representative is constructed from the original
target representative. Its exact signed difference is the actual exceptional
prime. The module identifications compare it with any originally specified
source representative before computing the original intersection square.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.IsContraction

open SmoothCanonicalExteriorComparison

variable {k : Type u} [Field k] [IsAlgClosed k]
  {S T : NormalProjectiveSurface k} {b : S.toScheme ⟶ T.toScheme}
  {E : S.PrimeCurve}

/-- The literal pullback plus the actual exceptional prime has the required
square, by original pullback isometry and contracted degree zero. -/
theorem square_pullback_add_exceptional
    (hb : IsContraction S T b E)
    (hS : ∀ s : S.Point, RegularPoint S.toScheme s)
    (hminus : IsMinusOneCurve hS E) (D : CartierDivisor T.toScheme) :
    letI : GenericPointPreserving b := ⟨hb.birational.map_genericPoint⟩
    S.intersectionPairing hS
      (DominantCartierPullback.pullbackHom b D + S.primeCurveCartier hS E)
      (DominantCartierPullback.pullbackHom b D + S.primeCurveCartier hS E) =
      T.intersectionPairing hb.regular D D - 1 := by
  letI : IsProper b := hb.isProper
  letI : GenericPointPreserving b := ⟨hb.birational.map_genericPoint⟩
  let hbir := (isBirational_iff_isBirationalScheme b).mp hb.birational
  have hcontracted : IsExceptionalCurve b E := (hb.isExceptionalCurve_iff_eq E).mpr rfl
  have hzero : S.intersectionPairing hS
      (DominantCartierPullback.pullbackHom b D) (S.primeCurveCartier hS E) = 0 := by
    rw [S.intersectionPairing_primeCurve hS]
    exact hcontracted.intersectionNumber_pullback_eq_zero b hb.over_base E D
  have hzero' : S.intersectionPairing hS
      (S.primeCurveCartier hS E) (DominantCartierPullback.pullbackHom b D) = 0 :=
    (S.intersectionPairing_symm hS _ _).trans hzero
  have hself : S.intersectionPairing hS
      (S.primeCurveCartier hS E) (S.primeCurveCartier hS E) = -1 := by
    rw [S.intersectionPairing_primeCurve hS]
    exact hminus.selfIntersection
  rw [S.intersectionPairing_add_left hS, S.intersectionPairing_add_right hS,
    S.intersectionPairing_add_right hS,
    BirationalCartierIntersectionPullback.intersectionPairing_pullback
      b hb.over_base hbir hS hb.regular, hzero, hzero', hself]
  ring

/-- Any actual source and target Cartier representatives of their original
top differentials satisfy the canonical-square formula for this contraction.
The compatible representative and exact pushforward are constructed inside. -/
theorem canonical_square_eq_sub_one
    (hb : IsContraction S T b E)
    (hS : ∀ s : S.Point, RegularPoint S.toScheme s)
    (hminus : IsMinusOneCurve hS E)
    (KS : CartierDivisor S.toScheme) (KT : CartierDivisor T.toScheme)
    (eKS : cartierDivisorModule S.toScheme KS ≅ relativeDifferentialExterior S.structureMorphism 2)
    (eKT : cartierDivisorModule T.toScheme KT ≅ relativeDifferentialExterior T.structureMorphism 2) :
    S.intersectionPairing hS KS KS = T.intersectionPairing hb.regular KT KT - 1 := by
  letI : IsProper b := hb.isProper
  letI : GenericPointPreserving b := ⟨hb.birational.map_genericPoint⟩
  letI : IsSmoothOfRelativeDimension 2 S.structureMorphism :=
    S.isSmoothOfRelativeDimension_two_of_regularPoints hS
  letI : IsSmoothOfRelativeDimension 2 T.structureMorphism :=
    T.isSmoothOfRelativeDimension_two_of_regularPoints hb.regular
  let hbir := (isBirational_iff_isBirationalScheme b).mp hb.birational
  obtain ⟨K, ⟨eK⟩, hpush⟩ := IsCanonicalWeilDivisor.exists_compatible_canonical_cartier
    S T b hb.over_base hbir (T.cartierToWeilHom KT) (IsCanonicalWeilDivisor.of_cartier T KT eKT)
  have hclass : cartierPicardClass S.toScheme KS = cartierPicardClass S.toScheme K :=
    SchemeKernelIdealIsoTransport.toPic_eq_of_iso
      (cartierDivisorInvertibleSheaf S.toScheme KS)
      (cartierDivisorInvertibleSheaf S.toScheme K) (eKS ≪≫ eK.symm)
  have hsquare : S.intersectionPairing hS KS KS = S.intersectionPairing hS K K := by
    rw [← S.picardPairing_class hS, ← S.picardPairing_class hS, hclass]
  rw [hsquare, hb.compatible_canonical_difference hS hminus KT K eK hpush]
  exact hb.square_pullback_add_exceptional hS hminus KT

end KltDP.Geometry.IsContraction

#check @KltDP.Geometry.IsContraction.canonical_square_eq_sub_one
#print axioms KltDP.Geometry.IsContraction.canonical_square_eq_sub_one
