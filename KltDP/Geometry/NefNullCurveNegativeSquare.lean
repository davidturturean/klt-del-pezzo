import KltDP.Geometry.DisjointNegativeCurvesRank
import KltDP.Geometry.NumericalHodgeConsequences
import KltDP.Geometry.ProjectiveAmpleCartierWitness
import KltDP.Geometry.AmpleCurveRestrictionPositive

/-!
# Negative square of a prime curve orthogonal to a positive-square divisor

An actual ample Cartier divisor is constructed from the original projective
embedding. Its strictly positive degree on a prime curve proves that the
curve's original numerical class is nonzero. Hodge negativity then applies
to any actual Cartier divisor of positive square orthogonal to that curve.
The conclusion is the original integer-valued curve self-intersection.

The consumer supplies neither an ample witness, numerical nonvanishing,
finite dimensionality, nor a negative-definiteness premise.
-/

noncomputable section

open AlgebraicGeometry

universe u

namespace KltDP.Geometry.NefNullCurveNegativeSquare

open DisjointNegativeCurvesRank

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k)
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

/-- The existing numerical map applied to the original Cartier-Picard map. -/
def cartierClass (D : CartierDivisor X.toScheme) : X.NumericalClassGroup :=
  X.picardNumericalMap (cartierPicardHom X.toScheme D)

/-- Original Cartier intersections are preserved by the actual numerical map. -/
theorem cartierClass_pairing (D E : CartierDivisor X.toScheme) :
    X.numericalIntersectionBilinForm hregular (cartierClass X D) (cartierClass X E) =
      (X.intersectionPairing hregular D E : ℚ) := by
  change X.numericalIntersectionBilinForm hregular
    (X.rationalPicardNumericalMap (X.picardTensorInclusion (cartierPicardHom X.toScheme D)))
    (X.rationalPicardNumericalMap (X.picardTensorInclusion (cartierPicardHom X.toScheme E))) = _
  rw [X.numericalIntersectionBilinForm_mk_mk, X.rationalPicardIntersectionBilinForm_cartier]

/-- Every actual prime curve has nonzero original numerical class, witnessed
by strict positive degree against a constructed actual ample Cartier divisor. -/
theorem curveClass_ne_zero (C : X.PrimeCurve) : curveClass X hregular C ≠ 0 := by
  obtain ⟨A, hA⟩ := X.exists_isAmple_cartier
  have hdegree : 0 < C.intersectionNumber A := by
    rw [C.intersectionNumber_eq_restrictionDegree]
    exact AmpleCurveRestrictionPositive.restrictionDegree_pos_of_isAmple X
      (cartierDivisorInvertibleSheaf X.toScheme A) hA C
  have hpositive : 0 < X.numericalIntersectionBilinForm hregular
      (cartierClass X A) (curveClass X hregular C) := by
    change 0 < X.numericalIntersectionBilinForm hregular
      (cartierClass X A) (cartierClass X (X.primeCurveCartier hregular C))
    rw [cartierClass_pairing, X.intersectionPairing_primeCurve hregular]
    exact_mod_cast hdegree
  intro hzero
  rw [hzero, map_zero] at hpositive
  exact (lt_irrefl 0) hpositive

/-- A prime curve orthogonal to an original Cartier divisor of positive square
has strictly negative original self-intersection. -/
theorem selfIntersectionNumber_neg_of_null (D : CartierDivisor X.toScheme)
    (hpositive : 0 < X.intersectionPairing hregular D D)
    (C : X.PrimeCurve) (hnull : C.intersectionNumber D = 0) :
    C.selfIntersectionNumber hregular < 0 := by
  have hD : 0 < X.numericalIntersectionBilinForm hregular
      (cartierClass X D) (cartierClass X D) := by
    rw [cartierClass_pairing]
    exact_mod_cast hpositive
  have hDC : X.numericalIntersectionBilinForm hregular
      (cartierClass X D) (curveClass X hregular C) = 0 := by
    change X.numericalIntersectionBilinForm hregular
      (cartierClass X D) (cartierClass X (X.primeCurveCartier hregular C)) = 0
    rw [cartierClass_pairing, X.intersectionPairing_primeCurve hregular, hnull, Int.cast_zero]
  have hnegative := NumericalHodgeConsequences.neg_of_orthogonal_to_positive X hregular
    (cartierClass X D) (curveClass X hregular C) hD hDC (curveClass_ne_zero X hregular C)
  rw [curveClass_self] at hnegative
  exact_mod_cast hnegative

end KltDP.Geometry.NefNullCurveNegativeSquare
