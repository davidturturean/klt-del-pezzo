import KltDP.Geometry.ContractionCartierKernel
import KltDP.Geometry.BirationalCartierPullbackPushforward
import KltDP.Geometry.ActualExceptionalPullback
import KltDP.Geometry.CompatibleRationalAdjunctionDegree
import KltDP.Geometry.RegularSurfaceSmoothLiteralUse

/-!
# The literal compatible canonical difference of an actual contraction

Original pushforward compatibility puts the signed difference in the
actual one-prime Cartier kernel. Rational adjunction on the original
minus-one curve determines that integer coefficient to be positive one.
The target Cartier divisor and source canonical module are unchanged.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.IsContraction

variable {k : Type u} [Field k] [IsAlgClosed k]
  {S T : NormalProjectiveSurface k} {b : S.toScheme ⟶ T.toScheme}
  {E : S.PrimeCurve}

/-- The coefficient is derived from the original signed divisor, original
pushforward and adjunction; it is not an independent compatibility input. -/
theorem compatible_canonical_difference
    (hb : IsContraction S T b E)
    (hS : ∀ s : S.Point, RegularPoint S.toScheme s)
    (hminus : IsMinusOneCurve hS E)
    (KT : CartierDivisor T.toScheme) (KS : CartierDivisor S.toScheme)
    (eKS : cartierDivisorModule S.toScheme KS ≅
      SmoothCanonicalExteriorComparison.relativeDifferentialExterior S.structureMorphism 2)
    (hpush :
      letI : IsProper b := hb.isProper
      BirationalWeilPushforward.pushforward b
        ((isBirational_iff_isBirationalScheme b).mp hb.birational)
        (S.cartierToWeilHom KS) = T.cartierToWeilHom KT) :
    letI : GenericPointPreserving b := ⟨hb.birational.map_genericPoint⟩
    KS = DominantCartierPullback.pullbackHom b KT + S.primeCurveCartier hS E := by
  letI : IsProper b := hb.isProper
  letI : GenericPointPreserving b := ⟨hb.birational.map_genericPoint⟩
  letI : IsSmoothOfRelativeDimension 2 S.structureMorphism :=
    S.isSmoothOfRelativeDimension_two_of_regularPoints hS
  let hbir := (isBirational_iff_isBirationalScheme b).mp hb.birational
  let D := KS - DominantCartierPullback.pullbackHom b KT
  have hDpush : BirationalWeilPushforward.pushforward b hbir (S.cartierToWeilHom D) = 0 := by
    dsimp only [D]
    rw [map_sub, map_sub, hpush,
      BirationalWeilPushforward.pushforward_cartier_pullback b hbir KT, sub_self]
  have hD := hb.cartier_eq_zsmul_exceptional hS D hDpush
  obtain ⟨e, he⟩ := hminus.isoProjectiveLine
  have hK : E.intersectionNumber KS = -1 := by
    have h := CompatibleRationalAdjunctionDegree.canonical_intersection_eq
      S hS KS eKS E e he
    rw [hminus.selfIntersection] at h
    norm_num at h
    exact h
  have hE : E.intersectionNumber (S.primeCurveCartier hS E) = -1 := hminus.selfIntersection
  have hcontracted : IsExceptionalCurve b E := (hb.isExceptionalCurve_iff_eq E).mpr rfl
  have hzero : E.intersectionNumber (DominantCartierPullback.pullbackHom b KT) = 0 :=
    hcontracted.intersectionNumber_pullback_eq_zero b hb.over_base E KT
  have hdegree : E.intersectionNumberHom D = -1 := by
    dsimp only [D]
    rw [map_sub, E.intersectionNumberHom_apply, E.intersectionNumberHom_apply, hK, hzero,
      sub_zero]
  let a := S.cartierToWeilHom D E
  change D = a • S.primeCurveCartier hS E at hD
  have ha : a = 1 := by
    have h := congrArg E.intersectionNumberHom hD
    rw [hdegree, map_zsmul, E.intersectionNumberHom_apply, hE] at h
    change (-1 : ℤ) = a * (-1) at h
    omega
  rw [ha, one_zsmul] at hD
  exact (sub_eq_iff_eq_add.mp hD).trans (add_comm _ _)

end KltDP.Geometry.IsContraction

#check @KltDP.Geometry.IsContraction.compatible_canonical_difference
#print axioms KltDP.Geometry.IsContraction.compatible_canonical_difference
