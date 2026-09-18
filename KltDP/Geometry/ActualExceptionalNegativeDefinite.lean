import KltDP.Geometry.BirationalAmplePullbackPositiveSquare
import KltDP.Geometry.ProjectiveAmpleCartierWitness
import KltDP.Geometry.ActualResolutionExceptionalCount

/-!
# Exceptional numerical independence and negative definiteness from the actual map

Projectivity of the actual normal target produces an ample Cartier divisor.
Its original pullback has positive square and is orthogonal to every prime
contracted by the original proper birational morphism. The compiled Hodge
and distinct-prime independence arguments now give the actual exceptional
numerical independence and strictly negative intersection-matrix quadratic
values. No positive-square, null-degree, independence, semidefiniteness, or
matrix nondegeneracy premise is supplied.

The Hodge argument is the existing selected geometric proof. This file does
not construct a resolution, a contraction, a rational forest, or its weights.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Matrix

universe u v

namespace KltDP.Geometry.ActualExceptionalNegativeDefinite

variable {k : Type u} [Field k] [IsAlgClosed k] {S X : NormalProjectiveSurface k}
  (π : S.toScheme ⟶ X.toScheme) [IsProper π]
  (hπ : π ≫ X.structureMorphism = S.structureMorphism)
  (hbir : IsBirationalScheme π)
  (hregular : ∀ x : S.Point, RegularPoint S.toScheme x)

include hπ hbir in
/-- A positive-square divisor orthogonal to all actual contracted primes
is produced from an actual ample divisor on the original target. -/
theorem exists_positive_square_orthogonal_divisor :
    ∃ H : CartierDivisor S.toScheme, 0 < S.intersectionPairing hregular H H ∧
      ∀ C : S.PrimeCurve, IsExceptionalCurve π C → C.intersectionNumber H = 0 := by
  letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
  obtain ⟨D, hD⟩ := X.exists_isAmple_cartier
  refine ⟨DominantCartierPullback.pullbackHom π D,
    BirationalAmplePullbackPositiveSquare.intersectionPairing_signedPullback_pos
      π hbir hregular D hD, ?_⟩
  intro C hC
  exact hC.intersectionNumber_pullback_eq_zero π hπ C D

include hπ hbir in
/-- The original numerical classes of all actual contracted prime curves
are linearly independent. -/
theorem linearIndependent : LinearIndependent ℚ
    (fun C : {C : S.PrimeCurve // IsExceptionalCurve π C} =>
      DisjointNegativeCurvesRank.curveClass S hregular C.val) := by
  obtain ⟨H, hH, hnull⟩ := exists_positive_square_orthogonal_divisor π hπ hbir hregular
  exact NullCurveIndependenceRank.linearIndependent S hregular H hH
    Subtype.val Subtype.val_injective (fun C => hnull C.val C.property)

include hπ hbir in
/-- The family is finite as an actual prime set, and its original
numerical classes are linearly independent. -/
theorem finite_and_linearIndependent :
    Finite {C : S.PrimeCurve // IsExceptionalCurve π C} ∧
      LinearIndependent ℚ
        (fun C : {C : S.PrimeCurve // IsExceptionalCurve π C} =>
          DisjointNegativeCurvesRank.curveClass S hregular C.val) :=
  ⟨(exceptionalCurves_finite_of_proper_birational π hbir).to_subtype,
    linearIndependent π hπ hbir hregular⟩

include hπ hbir in
/-- Every finite distinct family of actual contracted primes has strictly
negative original intersection quadratic value on nonzero coefficients. -/
theorem quadraticForm_neg {I : Type v} [Fintype I]
    (C : I → S.PrimeCurve) (hinj : Function.Injective C)
    (hcontracted : ∀ i, IsExceptionalCurve π (C i)) (a : I → ℚ) (ha : a ≠ 0) :
    dotProduct a (NullCurveIntersectionMatrix.intersectionMatrix S hregular C *ᵥ a) < 0 := by
  obtain ⟨H, hH, hnull⟩ := exists_positive_square_orthogonal_divisor π hπ hbir hregular
  exact NullCurveIntersectionMatrix.quadraticForm_neg S hregular H hH C hinj
    (fun i => hnull (C i) (hcontracted i)) a ha

include hπ hbir in
/-- The original exceptional intersection matrix is nondegenerate. -/
theorem matrix_nondegenerate {I : Type v} [Fintype I]
    (C : I → S.PrimeCurve) (hinj : Function.Injective C)
    (hcontracted : ∀ i, IsExceptionalCurve π (C i)) :
    (NullCurveIntersectionMatrix.intersectionMatrix S hregular C).Nondegenerate := by
  obtain ⟨H, hH, hnull⟩ := exists_positive_square_orthogonal_divisor π hπ hbir hregular
  exact NullCurveIntersectionMatrix.nondegenerate S hregular H hH C hinj
    (fun i => hnull (C i) (hcontracted i))

end KltDP.Geometry.ActualExceptionalNegativeDefinite

#print axioms KltDP.Geometry.ActualExceptionalNegativeDefinite.exists_positive_square_orthogonal_divisor
#print axioms KltDP.Geometry.ActualExceptionalNegativeDefinite.linearIndependent
#print axioms KltDP.Geometry.ActualExceptionalNegativeDefinite.quadraticForm_neg
