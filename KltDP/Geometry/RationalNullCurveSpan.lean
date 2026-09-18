import KltDP.Geometry.NullCurveIndependenceRank
import KltDP.Support.NegativeDefiniteCore

/-!
# Strict negativity on the actual rational Picard span of null curves

The original numerical quotient is injective on the span of the null-curve
classes because their images are linearly independent. Hodge negativity
therefore transports back to the original rational Picard group. This
constructs both the semidefiniteness and nondegeneracy inputs used by the
existing exceptional-intersection interface, for actual null-curve families.
-/

noncomputable section

open AlgebraicGeometry

universe u v

namespace KltDP.Geometry.RationalNullCurveSpan

open DisjointNegativeCurvesRank

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k)
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

/-- The original rational Picard curve class maps to its original numerical class. -/
theorem numericalMap_curveClass (C : X.PrimeCurve) :
    X.rationalPicardNumericalMap (X.primeCurveRationalPicardClass hregular C) =
      curveClass X hregular C := rfl

/-- The actual rational Picard classes themselves are independent, as their
images in the actual numerical quotient are independent. -/
theorem linearIndependent {ι : Type v} (D : CartierDivisor X.toScheme)
    (hpositive : 0 < X.intersectionPairing hregular D D)
    (C : ι → X.PrimeCurve) (hinj : Function.Injective C)
    (hnull : ∀ i, (C i).intersectionNumber D = 0) :
    LinearIndependent ℚ (fun i => X.primeCurveRationalPicardClass hregular (C i)) := by
  apply LinearIndependent.of_comp X.rationalPicardNumericalMap
  exact NullCurveIndependenceRank.linearIndependent X hregular D hpositive C hinj hnull

/-- Every nonzero actual rational Picard combination of the original null
curves has strictly negative square in the original rational Picard pairing. -/
theorem square_neg_on_span {ι : Type v} (D : CartierDivisor X.toScheme)
    (hpositive : 0 < X.intersectionPairing hregular D D)
    (C : ι → X.PrimeCurve) (hinj : Function.Injective C)
    (hnull : ∀ i, (C i).intersectionNumber D = 0)
    (c : X.RationalPicard)
    (hc : c ∈ Submodule.span ℚ
      (Set.range (fun i => X.primeCurveRationalPicardClass hregular (C i))))
    (hne : c ≠ 0) : X.rationalPicardIntersectionBilinForm hregular c c < 0 := by
  have hcomp : LinearIndependent ℚ
      (X.rationalPicardNumericalMap ∘
        (fun i => X.primeCurveRationalPicardClass hregular (C i))) :=
    NullCurveIndependenceRank.linearIndependent X hregular D hpositive C hinj hnull
  have hdisjoint := Submodule.range_ker_disjoint hcomp
  have hmap_ne : X.rationalPicardNumericalMap c ≠ 0 := by
    intro hzero
    exact hne (Submodule.disjoint_def.mp hdisjoint c hc hzero)
  have hspan : Submodule.span ℚ
      (Set.range (fun i => X.primeCurveRationalPicardClass hregular (C i))) ≤
      (Submodule.span ℚ (Set.range (fun i => curveClass X hregular (C i)))).comap
        X.rationalPicardNumericalMap := by
    apply Submodule.span_le.mpr
    rintro c ⟨i, rfl⟩
    exact Submodule.subset_span ⟨i, rfl⟩
  have hnegative := NullCurveNumericalSpan.square_neg_on_span X hregular D hpositive
    C hnull (X.rationalPicardNumericalMap c) (hspan hc) hmap_ne
  rwa [X.numericalIntersectionBilinForm_mk_mk] at hnegative

/-- The existing named semidefiniteness condition is proved for the original
rational Picard span of an actual null-curve family. -/
theorem negSemidefiniteOn {ι : Type v} (D : CartierDivisor X.toScheme)
    (hpositive : 0 < X.intersectionPairing hregular D D)
    (C : ι → X.PrimeCurve) (hinj : Function.Injective C)
    (hnull : ∀ i, (C i).intersectionNumber D = 0) :
    KltDP.Support.NegativeDefinite.NegSemidefiniteOn
      (X.rationalPicardIntersectionBilinForm hregular)
      (Set.range (fun i => X.primeCurveRationalPicardClass hregular (C i))) := by
  intro c hc
  by_cases hzero : c = 0
  · simp only [hzero, map_zero, LinearMap.zero_apply, le_refl]
  · exact (square_neg_on_span X hregular D hpositive C hinj hnull c hc hzero).le

/-- Nondegeneracy on that actual span follows from strict negativity;
the same nonzero class supplies its nonzero pairing witness. -/
theorem nondegenerateOn {ι : Type v} (D : CartierDivisor X.toScheme)
    (hpositive : 0 < X.intersectionPairing hregular D D)
    (C : ι → X.PrimeCurve) (hinj : Function.Injective C)
    (hnull : ∀ i, (C i).intersectionNumber D = 0) :
    KltDP.Support.NegativeDefinite.NondegenerateOn
      (X.rationalPicardIntersectionBilinForm hregular)
      (Set.range (fun i => X.primeCurveRationalPicardClass hregular (C i))) := by
  intro c hc hne
  exact ⟨c, hc, ne_of_lt (square_neg_on_span X hregular D hpositive C hinj hnull c hc hne)⟩

end KltDP.Geometry.RationalNullCurveSpan
