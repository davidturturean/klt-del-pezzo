import KltDP.Geometry.FiniteCartierSumEquation
import KltDP.Geometry.StrictNormalCrossingsFiniteProduct
import KltDP.Geometry.StrictNormalCrossingsCartierLocality
import KltDP.Geometry.SmoothPrimeCurveSingleSNC
import KltDP.Geometry.PrimeCurveIntersectionOneSNC

/-!
# The actual reduced sum of a finite smooth-curve configuration is SNC

The product-chart construction provides a genuine equation of the actual
sum divisor. Its nonunit factors are precisely the original curves through
the selected point. Original pairwise intersection at most one produces
the double-branch equations, smoothness produces the single-branch ones,
and no triple point leaves no further factors. This proves the global
all-equation-charts SNC predicate for the actual finite Cartier sum.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u v

namespace KltDP.Geometry

open NormalProjectiveSurface.PrimeCurve

/-- A finite injective family of smooth original prime curves with no
triple point and pairwise intersection at most one has an SNC Cartier sum. -/
theorem finite_smooth_primeCurve_sum_isStrictNormalCrossings
    {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)
    (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)
    {I : Type v} [Fintype I] (C : I → X.PrimeCurve) (hinj : Function.Injective C)
    [∀ i, IsSmooth (C i).toSpec]
    (hpair : ∀ i j, i ≠ j → X.intersectionPairing hregular
      (X.primeCurveCartier hregular (C i)) (X.primeCurveCartier hregular (C j)) ≤ 1)
    (hno : ∀ i j l (x : X.toScheme), x ∈ (C i : Set X.toScheme) →
      x ∈ (C j : Set X.toScheme) → x ∈ (C l : Set X.toScheme) →
        i = j ∨ i = l ∨ j = l) :
    letI : IsLocallyNoetherian X.toScheme := X.isLocallyNoetherian
    IsStrictNormalCrossingsCartier X.toScheme (∑ i, X.primeCurveCartier hregular (C i)) := by
  classical
  letI : IsLocallyNoetherian X.toScheme := X.isLocallyNoetherian
  apply isStrictNormalCrossingsCartier_of_local_equations
  intro x
  choose c hc using fun i => X.primeCurveCartier_hasRegularEquations hregular (C i) x
  let f : I → X.toScheme.presheaf.stalk x := fun i =>
    X.toScheme.presheaf.germ (c i).chart.openSet x (hc i) (c i).coefficient
  have hmem (i : I) : x ∈ (C i : Set X.toScheme) ↔ ¬ IsUnit (f i) := by
    have hm := mem_support_iff_not_isUnit_germ (X.primeCurveCartier hregular (C i))
      (X.primeCurveCartier_hasRegularEquations hregular (C i)) (c i) x (hc i)
    change x ∈ ((effectiveCartierIdealDataOfRegularEquations X.toScheme
      (X.primeCurveCartier hregular (C i))
      (X.primeCurveCartier_hasRegularEquations hregular (C i))).support : Set X.toScheme) ↔
        ¬ IsUnit (f i) at hm
    rw [X.primeCurveCartier_support hregular (C i)] at hm
    exact hm
  obtain ⟨a, ha, hgerm⟩ := exists_finset_sum_cartier_chart_germ X.toScheme
    (fun i => X.primeCurveCartier hregular (C i)) c x hc Finset.univ
  refine ⟨a, ha, ?_⟩
  rw [hgerm]
  change IsStrictNormalCrossingsEquation (X.toScheme.presheaf.stalk x) (∏ i, f i)
  apply IsStrictNormalCrossingsEquation.finprod_of_no_three_nonunits f
  · intro i
    by_cases hxi : x ∈ (C i : Set X.toScheme)
    · have hxrange : x ∈ Set.range (C i).inclusion.base := by
        rwa [(C i).range_inclusion]
      obtain ⟨y, rfl⟩ := hxrange
      exact SmoothPrimeCurveSingleSNC.equation_snc X hregular (C i) y (c i) (hc i)
    · exact Or.inl (not_not.mp
        (fun hn : ¬ IsUnit (f i) => hxi ((hmem i).mpr hn)))
  · intro i j hij hi hj
    exact PrimeCurveIntersectionOneSNC.product_isStrictNormalCrossingsEquation_of_pairing_le_one
      X hregular (C i) (C j) (fun h => hij (hinj h)) (hpair i j hij)
      x ((hmem i).mpr hi) ((hmem j).mpr hj) (c i) (hc i) (c j) (hc j)
  · intro i j l hi hj hl
    exact hno i j l x ((hmem i).mpr hi) ((hmem j).mpr hj) ((hmem l).mpr hl)

end KltDP.Geometry

#print axioms KltDP.Geometry.finite_smooth_primeCurve_sum_isStrictNormalCrossings
