import KltDP.Geometry.NullCurveNumericalSpan
import KltDP.LinearAlgebra.NegativePairingPositiveFunctional
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Independence and rank bound for the original null curves

Distinct actual null curves have nonnegative off-diagonal intersections.
Hodge gives strict negativity on their numerical span, while a constructed
ample divisor gives a functional positive on each curve. The proved linear
algebra criterion therefore makes their original numerical classes independent.
Adjoining the original positive-square divisor proves the Picard-rank bound.
Numerical finiteness also proves finiteness of the whole null-curve set.
No nefness, smoothness, finite family, or matrix hypothesis is needed for
the independence and finiteness statements on a regular projective surface.
-/

noncomputable section

open AlgebraicGeometry

universe u v

namespace KltDP.Geometry.NullCurveIndependenceRank

open DisjointNegativeCurvesRank NefNullCurveNegativeSquare NullCurveNumericalSpan

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k)
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

/-- Distinct original curves of degree zero against a positive-square
Cartier divisor have linearly independent original numerical classes. -/
theorem linearIndependent {ι : Type v} (D : CartierDivisor X.toScheme)
    (hpositive : 0 < X.intersectionPairing hregular D D)
    (C : ι → X.PrimeCurve) (hinj : Function.Injective C)
    (hnull : ∀ i, (C i).intersectionNumber D = 0) :
    LinearIndependent ℚ (fun i => curveClass X hregular (C i)) := by
  obtain ⟨l, hl⟩ := exists_positive_curve_functional X hregular
  apply KltDP.LinearAlgebra.NegativePairingPositiveFunctional.linearIndependent
    (X.numericalIntersectionBilinForm hregular) l
    (fun i => curveClass X hregular (C i))
  · intro c hc hne
    exact square_neg_on_span X hregular D hpositive C hnull c hc hne
  · intro i j hij
    rw [curveClass_pairing]
    have hnonneg := PrimeCurvePairingSupport.intersectionPairing_primeCurves_nonneg
      X hregular (C i) (C j) (fun h => hij (hinj h))
    exact_mod_cast hnonneg
  · intro i
    exact hl (C i)

/-- The entire actual null-curve set is finite. The independence proof
and the proved numerical finiteness theorem supply both ingredients. -/
theorem finite_null_curves (D : CartierDivisor X.toScheme)
    (hpositive : 0 < X.intersectionPairing hregular D D) :
    {C : X.PrimeCurve | C.intersectionNumber D = 0}.Finite := by
  letI : FiniteDimensional ℚ X.NumericalClassGroup :=
    SurfaceNumericalFinitenessProved.numericalSpaceFiniteDimensional X hregular
  have hli := linearIndependent X hregular D hpositive
    (fun C : {C : X.PrimeCurve // C.intersectionNumber D = 0} => C.1)
    Subtype.val_injective (fun C => C.2)
  exact Set.finite_coe_iff.mp hli.finite

/-- Any finite family of distinct original null curves uses at most
rho minus one numerical directions; the original D gives the extra one. -/
theorem card_add_one_le_picardRank {ι : Type v} [Fintype ι]
    (D : CartierDivisor X.toScheme)
    (hpositive : 0 < X.intersectionPairing hregular D D)
    (C : ι → X.PrimeCurve) (hinj : Function.Injective C)
    (hnull : ∀ i, (C i).intersectionNumber D = 0) :
    Fintype.card ι + 1 ≤ X.picardRank := by
  letI : FiniteDimensional ℚ X.NumericalClassGroup :=
    SurfaceNumericalFinitenessProved.numericalSpaceFiniteDimensional X hregular
  have hli := linearIndependent X hregular D hpositive C hinj hnull
  have hnot : cartierClass X D ∉
      Submodule.span ℚ (Set.range (fun i => curveClass X hregular (C i))) := by
    intro hmem
    have hzero := span_le_ker X hregular D C hnull hmem
    change X.numericalIntersectionBilinForm hregular
      (cartierClass X D) (cartierClass X D) = 0 at hzero
    rw [cartierClass_pairing] at hzero
    have hpositiveQ : (0 : ℚ) < (X.intersectionPairing hregular D D : ℚ) := by
      exact_mod_cast hpositive
    exact (ne_of_gt hpositiveQ) hzero
  have hext := hli.option hnot
  change Fintype.card ι + 1 ≤ Module.finrank ℚ X.NumericalClassGroup
  simpa only [Fintype.card_option] using hext.fintype_card_le_finrank

/-- The number of all actual null curves satisfies the same Picard-rank
bound; its finiteness is proved here before taking cardinality. -/
theorem null_curves_card_add_one_le_picardRank (D : CartierDivisor X.toScheme)
    (hpositive : 0 < X.intersectionPairing hregular D D) :
    Nat.card {C : X.PrimeCurve // C.intersectionNumber D = 0} + 1 ≤ X.picardRank := by
  letI : Fintype {C : X.PrimeCurve // C.intersectionNumber D = 0} :=
    (finite_null_curves X hregular D hpositive).fintype
  simpa only [Nat.card_eq_fintype_card] using
    card_add_one_le_picardRank X hregular D hpositive
      (fun C : {C : X.PrimeCurve // C.intersectionNumber D = 0} => C.1)
      Subtype.val_injective (fun C => C.2)

end KltDP.Geometry.NullCurveIndependenceRank
