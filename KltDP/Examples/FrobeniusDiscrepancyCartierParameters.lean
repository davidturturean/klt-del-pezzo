import KltDP.Examples.FrobeniusDiscrepancySupportCartier
import KltDP.Examples.FrobeniusDiscrepancyAllStalkParameters
import KltDP.Geometry.CartierEquationStalkIdealComparison

/-!
# Original Cartier support equations are regular parameters

At a point of a candidate-support prime, disjointness makes every other
selected curve absent. The multiplicity-one support divisor and that
original prime Cartier divisor thus have the same local curve coefficients.
The derived equation comparison identifies their actual principal stalk
ideals. The original Cartier support equation is consequently a regular
parameter at every point, including the generic point.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u

namespace KltDP.Examples.FrobeniusDiscrepancyBounds

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open FrobeniusMultiCentreSurface FrobeniusMultiCentreCanonicalWeilRepresentatives
open FrobeniusMultiCentreGraphExceptionalPairing

variable {k : Type u} [Field k] [IsAlgClosed k]
    (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
    (a : Fin n → k) (ha : Function.Injective a)
    (hproj : IsProjectiveOverField (multiStructure (q + 1) n a))

/-- The actual support-Cartier coefficient generates the original
prime-inclusion kernel, without a supplied local equation comparison. -/
theorem candidateSupportCartier_germ_span_eq_curve_kernel
    (C : (sourceSurface q n a ha hproj).PrimeCurve)
    (hC : C ∈ (candidate q n a ha hproj).support) (y : C.toScheme)
    (c : RegularCartierEquationChart (sourceSurface q n a ha hproj).toScheme
      (candidateSupportCartier q n a ha hproj))
    (hyc : C.inclusion.base y ∈ c.chart.openSet) :
    Ideal.span ({(sourceSurface q n a ha hproj).toScheme.presheaf.germ
        c.chart.openSet (C.inclusion.base y) hyc c.coefficient} :
      Set ((sourceSurface q n a ha hproj).toScheme.presheaf.stalk (C.inclusion.base y))) =
      RingHom.ker (C.inclusion.stalkMap y).hom := by
  classical
  let X := sourceSurface q n a ha hproj
  let hreg := multiSurfaceSurface_regularPoints (q + 1) n a ha hproj
  letI := X.stalks_uniqueFactorizationMonoid_of_regular hreg
  obtain ⟨d, hyd⟩ := X.primeCurveCartier_hasRegularEquations hreg C (C.inclusion.base y)
  have hcoeff (E : X.PrimeCurve) (hyE : C.inclusion.base y ∈ E) :
      X.cartierToWeilHom (candidateSupportCartier q n a ha hproj) E =
        X.cartierToWeilHom (X.primeCurveCartier hreg C) E := by
    rw [candidateSupportCartier_multiplicity, cartierToWeilHom_primeCurveCartier]
    by_cases hEC : E = C
    · subst E
      rw [if_pos hC, Finsupp.single_eq_same]
    · have hE : E ∉ (candidate q n a ha hproj).support := by
        intro hE
        exact hEC (candidate_support_unique_at_point q n a ha hproj E C hE hC
          (C.inclusion.base y) hyE (C.inclusion_base_mem y))
      rw [if_neg hE, Finsupp.single_eq_of_ne (fun h => hEC h.symm)]
  have hspan := X.regularCartierEquation_span_germ_eq_of_curveCoefficients
    (candidateSupportCartier q n a ha hproj) (X.primeCurveCartier hreg C)
    c d (C.inclusion.base y) hyc hyd hcoeff
  let U : X.toScheme.affineOpens :=
    ⟨(X.toScheme.affineCover.map (C.inclusion.base y)).opensRange,
      isAffineOpen_opensRange (X.toScheme.affineCover.map (C.inclusion.base y))⟩
  have hyU : C.inclusion.base y ∈ U.1 := X.toScheme.affineCover.covers (C.inclusion.base y)
  have hker := (C.vanishingIdeal.stalkMap_gluedTo_ker_eq_map U hyU).trans
    (PrimeCurveCrossingCoefficient.vanishingIdeal_map_germ_eq_span_coefficient
      X hreg C U (C.inclusion.base y) hyU d hyd)
  exact hspan.trans hker.symm

/-- Every original Cartier equation of the reduced candidate support
is an actual ambient regular parameter at every point where a support
component passes, and extends to an actual maximal-ideal generating set. -/
theorem candidateSupportCartier_coefficient_is_parameter
    (C : (sourceSurface q n a ha hproj).PrimeCurve)
    (hC : C ∈ (candidate q n a ha hproj).support) (y : C.toScheme)
    (c : RegularCartierEquationChart (sourceSurface q n a ha hproj).toScheme
      (candidateSupportCartier q n a ha hproj))
    (hyc : C.inclusion.base y ∈ c.chart.openSet) :
    let f := (sourceSurface q n a ha hproj).toScheme.presheaf.germ
      c.chart.openSet (C.inclusion.base y) hyc c.coefficient
    f ∉ (maximalIdeal
        ((sourceSurface q n a ha hproj).toScheme.presheaf.stalk (C.inclusion.base y))) ^ 2 ∧
      (Ideal.span {f} = maximalIdeal
          ((sourceSurface q n a ha hproj).toScheme.presheaf.stalk (C.inclusion.base y)) ∨
        ∃ g, Ideal.span {f, g} = maximalIdeal
          ((sourceSurface q n a ha hproj).toScheme.presheaf.stalk (C.inclusion.base y))) := by
  let f := (sourceSurface q n a ha hproj).toScheme.presheaf.germ
    c.chart.openSet (C.inclusion.base y) hyc c.coefficient
  obtain ⟨_, d, hker, hd, hgen⟩ :=
    candidate_support_all_stalk_parameters q n a ha hproj C hC y
  have hspan : Ideal.span {f} = Ideal.span {d} :=
    (candidateSupportCartier_germ_span_eq_curve_kernel q n a ha hproj C hC y c hyc).trans hker
  refine ⟨fun hf => hd ?_, ?_⟩
  · have hle : Ideal.span {f} ≤ (maximalIdeal
        ((sourceSurface q n a ha hproj).toScheme.presheaf.stalk (C.inclusion.base y))) ^ 2 :=
      Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hf)
    rw [hspan] at hle
    exact hle (Ideal.subset_span (Set.mem_singleton d))
  · rcases hgen with hgen | ⟨g, hg⟩
    · exact Or.inl (hspan.trans hgen)
    · refine Or.inr ⟨g, ?_⟩
      rw [Ideal.span_insert, hspan, ← Ideal.span_insert]
      exact hg

end KltDP.Examples.FrobeniusDiscrepancyBounds
