import KltDP.Geometry.NullCurveIndependenceRank
import KltDP.LinearAlgebra.NegativeGramDimension
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# The actual intersection matrix of null curves is negative definite

The entries are the original prime Cartier intersection numbers, cast to
rationals. The existing negative-Gram identity identifies the matrix's
quadratic value with the square of the actual numerical linear combination.
The proved null-curve independence theorem makes this combination nonzero,
and Hodge negativity on its actual span makes its square strictly negative.
Matrix nondegeneracy and determinant nonvanishing follow through pinned APIs.
No independence, nondegeneracy, or negative-definiteness premise is supplied.
-/

noncomputable section

open AlgebraicGeometry Matrix
open scoped BigOperators

universe u v

namespace KltDP.Geometry.NullCurveIntersectionMatrix

open DisjointNegativeCurvesRank
open KltDP.LinearAlgebra.CanonicalCorrection

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k)
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)
  {ι : Type v}

/-- The rational matrix of the original integer-valued prime intersections. -/
def intersectionMatrix (C : ι → X.PrimeCurve) : Matrix ι ι ℚ :=
  fun i j => (X.intersectionPairing hregular
    (X.primeCurveCartier hregular (C i)) (X.primeCurveCartier hregular (C j)) : ℚ)

/-- The original matrix agrees with the already implemented Gram construction. -/
theorem intersectionMatrix_eq_neg_negativeGram (C : ι → X.PrimeCurve) :
    intersectionMatrix X hregular C =
      -negativeGram (X.numericalIntersectionBilinForm hregular)
        (fun i => curveClass X hregular (C i)) := by
  ext i j
  change (X.intersectionPairing hregular
    (X.primeCurveCartier hregular (C i)) (X.primeCurveCartier hregular (C j)) : ℚ) =
      -(-X.numericalIntersectionBilinForm hregular
        (curveClass X hregular (C i)) (curveClass X hregular (C j)))
  rw [neg_neg, curveClass_pairing]

variable [Fintype ι]

/-- Evaluating the actual matrix computes the original numerical square. -/
theorem quadraticForm_eq (C : ι → X.PrimeCurve) (c : ι → ℚ) :
    dotProduct c (intersectionMatrix X hregular C *ᵥ c) =
      X.numericalIntersectionBilinForm hregular
        (∑ i, c i • curveClass X hregular (C i))
        (∑ i, c i • curveClass X hregular (C i)) := by
  rw [intersectionMatrix_eq_neg_negativeGram, Matrix.neg_mulVec, dotProduct_neg,
    KltDP.LinearAlgebra.negativeGram_quadratic_form, neg_neg]

/-- Every nonzero coefficient vector has strictly negative quadratic value. -/
theorem quadraticForm_neg (D : CartierDivisor X.toScheme)
    (hpositive : 0 < X.intersectionPairing hregular D D)
    (C : ι → X.PrimeCurve) (hinj : Function.Injective C)
    (hnull : ∀ i, (C i).intersectionNumber D = 0)
    (c : ι → ℚ) (hc : c ≠ 0) :
    dotProduct c (intersectionMatrix X hregular C *ᵥ c) < 0 := by
  rw [quadraticForm_eq]
  apply NullCurveNumericalSpan.square_neg_on_span X hregular D hpositive C hnull
  · exact Submodule.sum_mem _ fun i hi =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · intro hzero
    apply hc
    funext i
    exact Fintype.linearIndependent_iff.mp
      (NullCurveIndependenceRank.linearIndependent X hregular D hpositive C hinj hnull)
      c hzero i

/-- The same conclusion for Mathlib's original matrix quadratic-map object. -/
theorem toQuadraticMap_neg [DecidableEq ι] (D : CartierDivisor X.toScheme)
    (hpositive : 0 < X.intersectionPairing hregular D D)
    (C : ι → X.PrimeCurve) (hinj : Function.Injective C)
    (hnull : ∀ i, (C i).intersectionNumber D = 0)
    (c : ι → ℚ) (hc : c ≠ 0) :
    (intersectionMatrix X hregular C).toQuadraticMap' c < 0 := by
  change Matrix.toLinearMap₂' ℚ (intersectionMatrix X hregular C) c c < 0
  rw [Matrix.toLinearMap₂'_apply']
  exact quadraticForm_neg X hregular D hpositive C hinj hnull c hc

/-- Nondegeneracy follows from the proved negative quadratic values. -/
theorem nondegenerate (D : CartierDivisor X.toScheme)
    (hpositive : 0 < X.intersectionPairing hregular D D)
    (C : ι → X.PrimeCurve) (hinj : Function.Injective C)
    (hnull : ∀ i, (C i).intersectionNumber D = 0) :
    (intersectionMatrix X hregular C).Nondegenerate := by
  classical
  intro c hzero
  by_cases hc : c = 0
  · exact hc
  · exact False.elim ((ne_of_lt
      (quadraticForm_neg X hregular D hpositive C hinj hnull c hc)) (hzero c))

/-- The actual rational intersection matrix has nonzero determinant. -/
theorem det_ne_zero [DecidableEq ι] (D : CartierDivisor X.toScheme)
    (hpositive : 0 < X.intersectionPairing hregular D D)
    (C : ι → X.PrimeCurve) (hinj : Function.Injective C)
    (hnull : ∀ i, (C i).intersectionNumber D = 0) :
    (intersectionMatrix X hregular C).det ≠ 0 :=
  (nondegenerate X hregular D hpositive C hinj hnull).det_ne_zero

end KltDP.Geometry.NullCurveIntersectionMatrix
