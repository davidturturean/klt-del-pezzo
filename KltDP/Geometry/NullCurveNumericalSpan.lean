import KltDP.Geometry.NefNullCurveNegativeSquare

/-!
# The numerical span of the original null curves

Every linear combination of degree-zero curves remains orthogonal to the
original Cartier divisor. When that divisor has positive square, Hodge
negativity holds on their whole numerical span. A separately constructed
ample Cartier divisor supplies one linear functional strictly positive on
every actual prime-curve class. These are the inputs for independence of
the null-curve classes; no independence or rank statement is assumed here.
-/

noncomputable section

open AlgebraicGeometry

universe u v

namespace KltDP.Geometry.NullCurveNumericalSpan

open DisjointNegativeCurvesRank NefNullCurveNegativeSquare

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k)
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

/-- Pairing with the actual Cartier class evaluates the original degree
on the original prime curve. -/
theorem cartierClass_curveClass (D : CartierDivisor X.toScheme) (C : X.PrimeCurve) :
    X.numericalIntersectionBilinForm hregular
      (cartierClass X D) (curveClass X hregular C) = (C.intersectionNumber D : ℚ) := by
  change X.numericalIntersectionBilinForm hregular
    (cartierClass X D) (cartierClass X (X.primeCurveCartier hregular C)) = _
  rw [cartierClass_pairing, X.intersectionPairing_primeCurve hregular]

/-- Orthogonality of actual null curves extends to their entire numerical span. -/
theorem span_le_ker {ι : Type v} (D : CartierDivisor X.toScheme)
    (C : ι → X.PrimeCurve) (hnull : ∀ i, (C i).intersectionNumber D = 0) :
    Submodule.span ℚ (Set.range (fun i => curveClass X hregular (C i))) ≤
      LinearMap.ker (X.numericalIntersectionBilinForm hregular (cartierClass X D)) := by
  apply Submodule.span_le.mpr
  rintro c ⟨i, rfl⟩
  change X.numericalIntersectionBilinForm hregular
    (cartierClass X D) (curveClass X hregular (C i)) = 0
  rw [cartierClass_curveClass, hnull, Int.cast_zero]

/-- The actual pairing is strictly negative on every nonzero vector in
the numerical span of the original null curves. -/
theorem square_neg_on_span {ι : Type v} (D : CartierDivisor X.toScheme)
    (hpositive : 0 < X.intersectionPairing hregular D D)
    (C : ι → X.PrimeCurve) (hnull : ∀ i, (C i).intersectionNumber D = 0)
    (c : X.NumericalClassGroup)
    (hc : c ∈ Submodule.span ℚ (Set.range (fun i => curveClass X hregular (C i))))
    (hne : c ≠ 0) : X.numericalIntersectionBilinForm hregular c c < 0 := by
  have hD : 0 < X.numericalIntersectionBilinForm hregular
      (cartierClass X D) (cartierClass X D) := by
    rw [cartierClass_pairing]
    exact_mod_cast hpositive
  exact NumericalHodgeConsequences.neg_of_orthogonal_to_positive X hregular
    (cartierClass X D) c hD (span_le_ker X hregular D C hnull hc) hne

/-- An actual ample Cartier witness constructs a single rational linear
functional positive on every original prime-curve class. -/
theorem exists_positive_curve_functional :
    ∃ l : X.NumericalClassGroup →ₗ[ℚ] ℚ,
      ∀ C : X.PrimeCurve, 0 < l (curveClass X hregular C) := by
  obtain ⟨A, hA⟩ := X.exists_isAmple_cartier
  refine ⟨X.numericalIntersectionBilinForm hregular (cartierClass X A), ?_⟩
  intro C
  rw [cartierClass_curveClass]
  have hpositive : 0 < C.intersectionNumber A := by
    rw [C.intersectionNumber_eq_restrictionDegree]
    exact AmpleCurveRestrictionPositive.restrictionDegree_pos_of_isAmple X
      (cartierDivisorInvertibleSheaf X.toScheme A) hA C
  exact_mod_cast hpositive

end KltDP.Geometry.NullCurveNumericalSpan
