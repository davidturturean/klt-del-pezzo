import KltDP.Geometry.ActualExceptionalNegativeDefinite
import KltDP.LinearAlgebra.OrthogonalCopyGram

/-!
# The actual exceptional negative Gram matrix is positive definite

The already proved strictly negative original intersection quadratic
values and the original numerical pairing symmetry give Mathlib's
positive-definite predicate for the negative Gram matrix of the actual
contracted prime classes. The contraction, its projective target and
its actual contracted primes supply all the geometric inputs.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Matrix
universe u v

namespace KltDP.Geometry.ActualExceptionalNegativeDefinite

open DisjointNegativeCurvesRank KltDP.LinearAlgebra.CanonicalCorrection

variable {k : Type u} [Field k] [IsAlgClosed k] {S X : NormalProjectiveSurface k}
    (π : S.toScheme ⟶ X.toScheme) [IsProper π]
    (hπ : π ≫ X.structureMorphism = S.structureMorphism)
    (hbir : IsBirationalScheme π)
    (hregular : ∀ x : S.Point, RegularPoint S.toScheme x)

include hπ hbir in
/-- The actual negative Gram matrix is positive definite, without a matrix-sign premise. -/
theorem negativeGram_posDef {I : Type v} [Fintype I]
    (C : I → S.PrimeCurve) (hinj : Function.Injective C)
    (hcontracted : ∀ i, IsExceptionalCurve π (C i)) :
    (negativeGram (S.numericalIntersectionBilinForm hregular)
      (fun i => curveClass S hregular (C i))).PosDef := by
  refine ⟨Matrix.IsHermitian.ext (fun i j => ?_), ?_⟩
  · simpa only [negativeGram, star_trivial] using congrArg Neg.neg
      (S.numericalIntersectionBilinForm_isSymm hregular
        (curveClass S hregular (C j)) (curveClass S hregular (C i)))
  · intro a ha
    have hn := quadraticForm_neg π hπ hbir hregular C hinj hcontracted a ha
    rw [NullCurveIntersectionMatrix.intersectionMatrix_eq_neg_negativeGram,
      Matrix.neg_mulVec, dotProduct_neg] at hn
    simpa only [star_trivial] using (neg_lt_zero.mp hn)

end KltDP.Geometry.ActualExceptionalNegativeDefinite

#print axioms KltDP.Geometry.ActualExceptionalNegativeDefinite.negativeGram_posDef
