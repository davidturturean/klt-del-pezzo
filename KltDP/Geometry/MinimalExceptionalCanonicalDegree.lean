import KltDP.Geometry.ActualExceptionalNegativeDefinite
import KltDP.Geometry.RationalPrimeCurveAdjunction

/-!
# Minimal exceptional rational curves have nonnegative canonical degree

The original resolution supplies negative self-intersection. Minimality
excludes minus-one curves, so an actual rational exceptional prime has
square at most minus two. The proved actual adjunction formula then gives
nonnegative degree of the original smooth canonical Cartier representative.
Rationality of general klt exceptional curves is a separate obligation.

The negative-square input is derived using the selected Hodge candidate;
this file retains that isolated literature dependency.
-/

set_option autoImplicit false

noncomputable section
open AlgebraicGeometry CategoryTheory Matrix
universe u

namespace KltDP.Geometry

open SmoothCanonicalCartierRepresentative

/-- Every actual exceptional prime of an original resolution has negative
original self-intersection. No numerical negativity is supplied. -/
theorem IsResolution.exceptional_selfIntersection_neg
    {k : Type u} [Field k] [IsAlgClosed k]
    {S X : NormalProjectiveSurface k} {π : S.toScheme ⟶ X.toScheme}
    (hres : IsResolution S X π) (C : S.PrimeCurve) (hC : IsExceptionalCurve π C) :
    C.selfIntersectionNumber hres.regular < 0 := by
  letI : IsProper π := hres.isProper
  have hbir : IsBirationalScheme π :=
    (isBirational_iff_isBirationalScheme π).mp hres.birational
  have hq := ActualExceptionalNegativeDefinite.quadraticForm_neg
    π hres.over_base hbir hres.regular (fun _ : Unit => C)
    (fun _ _ _ => Subsingleton.elim _ _) (fun _ => hC) (fun _ => (1 : ℚ))
    (by intro hz; have h := congrFun hz (); norm_num at h)
  have hneg : (S.intersectionPairing hres.regular
      (S.primeCurveCartier hres.regular C) (S.primeCurveCartier hres.regular C) : ℚ) < 0 := by
    simpa [dotProduct, mulVec, NullCurveIntersectionMatrix.intersectionMatrix] using hq
  rw [S.intersectionPairing_primeCurve hres.regular] at hneg
  exact_mod_cast hneg

/-- Minimality excludes minus one after actual negativity is derived. -/
theorem IsMinimalResolution.rational_exceptional_selfIntersection_le_neg_two
    {k : Type u} [Field k] [IsAlgClosed k]
    {S X : NormalProjectiveSurface k} {π : S.toScheme ⟶ X.toScheme}
    (hmin : IsMinimalResolution S X π) (C : S.PrimeCurve) (hC : IsExceptionalCurve π C)
    (e : C.toScheme ≅ projectiveSpace k 1)
    (he : e.hom ≫ projectiveSpaceToSpec k 1 = C.toSpec) :
    C.selfIntersectionNumber hmin.regular ≤ -2 := by
  have hneg := hmin.toIsResolution.exceptional_selfIntersection_neg C hC
  by_contra hn
  have hval : C.selfIntersectionNumber hmin.regular = -1 := by omega
  exact hmin.no_minusOne_curve C hC ⟨⟨e, he⟩, hval⟩

/-- Actual adjunction gives nonnegative original canonical degree along
every rational exceptional prime of the original minimal resolution. -/
theorem IsMinimalResolution.rational_exceptional_canonical_degree_nonneg
    {k : Type u} [Field k] [IsAlgClosed k]
    {S X : NormalProjectiveSurface k}
    [IsSmoothOfRelativeDimension 2 S.structureMorphism]
    {π : S.toScheme ⟶ X.toScheme}
    (hmin : IsMinimalResolution S X π) (C : S.PrimeCurve) (hC : IsExceptionalCurve π C)
    (e : C.toScheme ≅ projectiveSpace k 1)
    (he : e.hom ≫ projectiveSpaceToSpec k 1 = C.toSpec) :
    0 ≤ C.intersectionNumber (cartierRepresentative S.structureMorphism) := by
  have hbound := hmin.rational_exceptional_selfIntersection_le_neg_two C hC e he
  have hadj := RationalPrimeCurveAdjunction.antiCanonical_degree S C e he
  rw [C.intersectionNumber_neg] at hadj
  omega

end KltDP.Geometry

#print axioms KltDP.Geometry.IsResolution.exceptional_selfIntersection_neg
#print axioms KltDP.Geometry.IsMinimalResolution.rational_exceptional_canonical_degree_nonneg
