import KltDP.Geometry.ExceptionalCurveFieldPointFactor
import KltDP.Geometry.PrimeCurveInclusionLift
import KltDP.Geometry.DominantCartierPullbackModule
import KltDP.Geometry.NullCurveIntersectionMatrix

/-!
# Actual exceptional curves are orthogonal to original Cartier pullbacks

Topological contraction of an actual prime curve produces its field-point
factorization. Its degree against any original pulled line sheaf is zero.
The signed Cartier pullback comparison gives the same assertion for every
original Cartier divisor, without an off-support or effectiveness assumption.

The final Hodge consumers retain positive square of that actual pullback
as an explicit condition. They prove independence and negative quadratic
values; they do not assert that this positive-square witness has already
been constructed for every resolution.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Matrix

universe u v

namespace KltDP.Geometry

variable {k : Type u} [Field k] [IsAlgClosed k]
  {S X : NormalProjectiveSurface k}

/-- Every original pulled line sheaf has degree zero on a topologically
contracted original prime curve. The factorization is derived internally. -/
theorem IsExceptionalCurve.restrictionDegree_pullback_eq_zero
    (π : S.toScheme ⟶ X.toScheme)
    (hπ : π ≫ X.structureMorphism = S.structureMorphism)
    (C : S.PrimeCurve) (hC : IsExceptionalCurve π C) (L : InvertibleSheaf X.toScheme) :
    C.restrictionDegree (pullbackInvertibleSheaf π L) = 0 := by
  obtain ⟨p, hp, _⟩ := hC.exists_fieldPoint_factor π hπ C
  exact PrimeCurveInclusionLift.restrictionDegree_pullback_eq_zero
    C C.inclusion C.range_inclusion.symm π C.toSpec p hp L

/-- The same degree-zero assertion for the actual signed Cartier pullback. -/
theorem IsExceptionalCurve.intersectionNumber_pullback_eq_zero
    (π : S.toScheme ⟶ X.toScheme) [GenericPointPreserving π]
    (hπ : π ≫ X.structureMorphism = S.structureMorphism)
    (C : S.PrimeCurve) (hC : IsExceptionalCurve π C) (D : CartierDivisor X.toScheme) :
    C.intersectionNumber (DominantCartierPullback.pullbackHom π D) = 0 := by
  change C.restrictionDegree
    (cartierDivisorInvertibleSheaf S.toScheme (DominantCartierPullback.pullbackHom π D)) = 0
  exact (C.restrictionDegree_eq_of_iso
    (DominantCartierPullback.modulePullbackIso π D).symm).trans
    (hC.restrictionDegree_pullback_eq_zero π hπ C
      (cartierDivisorInvertibleSheaf X.toScheme D))

namespace ActualExceptionalPullback

variable (π : S.toScheme ⟶ X.toScheme) [GenericPointPreserving π]
  (hπ : π ≫ X.structureMorphism = S.structureMorphism)
  (hregular : ∀ x : S.Point, RegularPoint S.toScheme x)
  (D : CartierDivisor X.toScheme)
  (hpositive : 0 < S.intersectionPairing hregular
    (DominantCartierPullback.pullbackHom π D) (DominantCartierPullback.pullbackHom π D))

include hπ hpositive in
/-- A positive-square actual pullback makes the original numerical classes
of all contracted primes linearly independent. No independence is supplied. -/
theorem linearIndependent : LinearIndependent ℚ
    (fun C : {C : S.PrimeCurve // IsExceptionalCurve π C} =>
      DisjointNegativeCurvesRank.curveClass S hregular C.val) :=
  NullCurveIndependenceRank.linearIndependent S hregular
    (DominantCartierPullback.pullbackHom π D) hpositive Subtype.val Subtype.val_injective
    (fun C => C.property.intersectionNumber_pullback_eq_zero π hπ C.val D)

include hπ hpositive in
/-- The original intersection matrix of any finite distinct contracted
prime family has strictly negative quadratic values. -/
theorem quadraticForm_neg {I : Type v} [Fintype I]
    (C : I → S.PrimeCurve) (hinj : Function.Injective C)
    (hcontracted : ∀ i, IsExceptionalCurve π (C i))
    (a : I → ℚ) (ha : a ≠ 0) :
    dotProduct a (NullCurveIntersectionMatrix.intersectionMatrix S hregular C *ᵥ a) < 0 :=
  NullCurveIntersectionMatrix.quadraticForm_neg S hregular
    (DominantCartierPullback.pullbackHom π D) hpositive C hinj
    (fun i => (hcontracted i).intersectionNumber_pullback_eq_zero π hπ (C i) D) a ha

end ActualExceptionalPullback

end KltDP.Geometry

#print axioms KltDP.Geometry.IsExceptionalCurve.intersectionNumber_pullback_eq_zero
#print axioms KltDP.Geometry.ActualExceptionalPullback.linearIndependent
