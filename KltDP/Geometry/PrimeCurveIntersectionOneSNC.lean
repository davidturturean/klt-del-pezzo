import KltDP.Geometry.PrimeCurveIntersectionOneCrossing
import KltDP.Geometry.StrictNormalCrossings
import KltDP.Geometry.ClosedPointDimension

/-!
# Strict normal crossings for the original pair of prime-curve equations

An original intersection bound at most one forces the two actual Cartier
germs to generate the maximal ideal. Their common point is closed by the
proved finite intersection theorem, so its original surface stalk has
dimension two. The germs therefore form a complete regular parameter
system, and their product satisfies the existing strict-normal-crossings
equation predicate.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

universe u

namespace KltDP.Geometry.PrimeCurveIntersectionOneSNC

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)
  (C D : X.PrimeCurve) [IsSmooth C.toSpec]

/-- Every pair of actual prime Cartier equations at a common point is a
complete regular parameter pair when the original intersection is at most one. -/
theorem isRegularParameterFamily_of_pairing_le_one
    (hCD : C ≠ D)
    (hdegree : X.intersectionPairing hregular (X.primeCurveCartier hregular C)
      (X.primeCurveCartier hregular D) ≤ 1)
    (x : X.toScheme) (hxC : x ∈ (C : Set X.toScheme)) (hxD : x ∈ (D : Set X.toScheme))
    (c : RegularCartierEquationChart X.toScheme (X.primeCurveCartier hregular C))
    (hc : x ∈ c.chart.openSet)
    (d : RegularCartierEquationChart X.toScheme (X.primeCurveCartier hregular D))
    (hd : x ∈ d.chart.openSet) :
    IsRegularParameterFamily (X.toScheme.presheaf.stalk x) 2
      ![X.toScheme.presheaf.germ c.chart.openSet x hc c.coefficient,
        X.toScheme.presheaf.germ d.chart.openSet x hd d.coefficient] := by
  have hxrange : x ∈ Set.range C.inclusion.base := by
    rwa [C.range_inclusion]
  obtain ⟨y, rfl⟩ := hxrange
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, _⟩ :=
    (isBasis_affine_open X.toScheme).exists_subset_of_mem_open
      (Set.mem_univ (C.inclusion.base y)) isOpen_univ
  have hcross :=
    PrimeCurveIntersectionOneCrossing.vanishingIdeal_sup_eq_maximalIdeal_of_pairing_le_one
      X hregular C D hCD hdegree y hxD ⟨U, hU⟩ hyU
  rw [PrimeCurveCrossingCoefficient.vanishingIdeal_map_germ_eq_span_coefficient
      X hregular C ⟨U, hU⟩ (C.inclusion.base y) hyU c hc,
    PrimeCurveCrossingCoefficient.vanishingIdeal_map_germ_eq_span_coefficient
      X hregular D ⟨U, hU⟩ (C.inclusion.base y) hyU d hd] at hcross
  let E := X.primeCurveCartier hregular D
  let hE := X.primeCurveCartier_hasRegularEquations hregular D
  let hC : C.NotInSupport E hE := X.notInSupport_of_ne hregular hCD
  have hz : C.inclusion.base y ∈ Set.range (C.intersectionToSurface E hE hC).base := by
    rw [C.range_intersectionToSurface E hE hC, X.primeCurveCartier_support hregular D]
    exact ⟨hxC, hxD⟩
  have hclosed := (C.range_intersectionToSurface_finite_and_isClosed E hE hC).2
    (C.inclusion.base y) hz
  refine ⟨hregular _, X.closed_stalk_dimension_two _ hclosed, ?_⟩
  simpa only [Matrix.range_cons_cons_empty, Ideal.span_insert] using hcross

/-- The product of the two original prime Cartier germs satisfies the
existing strict-normal-crossings equation predicate. -/
theorem product_isStrictNormalCrossingsEquation_of_pairing_le_one
    (hCD : C ≠ D)
    (hdegree : X.intersectionPairing hregular (X.primeCurveCartier hregular C)
      (X.primeCurveCartier hregular D) ≤ 1)
    (x : X.toScheme) (hxC : x ∈ (C : Set X.toScheme)) (hxD : x ∈ (D : Set X.toScheme))
    (c : RegularCartierEquationChart X.toScheme (X.primeCurveCartier hregular C))
    (hc : x ∈ c.chart.openSet)
    (d : RegularCartierEquationChart X.toScheme (X.primeCurveCartier hregular D))
    (hd : x ∈ d.chart.openSet) :
    IsStrictNormalCrossingsEquation (X.toScheme.presheaf.stalk x)
      (X.toScheme.presheaf.germ c.chart.openSet x hc c.coefficient *
        X.toScheme.presheaf.germ d.chart.openSet x hd d.coefficient) := by
  have hparams := isRegularParameterFamily_of_pairing_le_one
    X hregular C D hCD hdegree x hxC hxD c hc d hd
  apply IsStrictNormalCrossingsEquation.of_parameter_product hparams.1 hparams.2.1
  simpa only [Matrix.range_cons_cons_empty] using hparams.2.2

end KltDP.Geometry.PrimeCurveIntersectionOneSNC

#print axioms KltDP.Geometry.PrimeCurveIntersectionOneSNC.product_isStrictNormalCrossingsEquation_of_pairing_le_one
