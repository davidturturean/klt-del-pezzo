import KltDP.Examples.FrobeniusDiscrepancyCartierParameters

/-!
# The original reduced support divisor at every ambient point

Every original regular Cartier coefficient is either a unit, off the actual
candidate support, or an actual regular parameter, on its unique original
smooth component. This is an explicit local-equation conclusion on the
original surface, without a supplied SNC predicate or coordinate hypothesis.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u

namespace KltDP.Examples.FrobeniusDiscrepancyBounds

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open FrobeniusMultiCentreSurface FrobeniusMultiCentreCanonicalWeilRepresentatives

variable {k : Type u} [Field k] [IsAlgClosed k]
    (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
    (a : Fin n → k) (ha : Function.Injective a)
    (hproj : IsProjectiveOverField (multiStructure (q + 1) n a))

/-- Each actual coefficient germ is a unit or one ambient regular parameter. -/
theorem candidateSupportCartier_local_equation
    (c : RegularCartierEquationChart (sourceSurface q n a ha hproj).toScheme
      (candidateSupportCartier q n a ha hproj))
    (x : (sourceSurface q n a ha hproj).toScheme) (hxc : x ∈ c.chart.openSet) :
    let f := (sourceSurface q n a ha hproj).toScheme.presheaf.germ c.chart.openSet x hxc c.coefficient
    IsUnit f ∨ (f ∉ (maximalIdeal ((sourceSurface q n a ha hproj).toScheme.presheaf.stalk x)) ^ 2 ∧
      (Ideal.span {f} = maximalIdeal ((sourceSurface q n a ha hproj).toScheme.presheaf.stalk x) ∨
        ∃ g, Ideal.span {f, g} =
          maximalIdeal ((sourceSurface q n a ha hproj).toScheme.presheaf.stalk x))) := by
  classical
  by_cases hx : x ∈ divisorSupport (candidate q n a ha hproj)
  · obtain ⟨C, hC, hxC⟩ := (mem_divisorSupport _ x).mp hx
    have hrange : x ∈ Set.range C.inclusion.base := by
      rw [C.range_inclusion]
      exact hxC
    obtain ⟨y, rfl⟩ := hrange
    exact Or.inr (candidateSupportCartier_coefficient_is_parameter q n a ha hproj C
      (Finsupp.mem_support_iff.mpr hC) y c hxc)
  · left
    by_contra hf
    apply hx
    rw [← candidateSupportIdeal_support q n a ha hproj]
    exact (PrimeCurve.mem_support_iff_not_isUnit_germ _
      (candidateSupportCartier_hasRegularEquations q n a ha hproj) c x hxc).mpr hf

end KltDP.Examples.FrobeniusDiscrepancyBounds
