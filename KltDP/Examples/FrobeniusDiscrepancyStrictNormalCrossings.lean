import KltDP.Geometry.StrictNormalCrossings
import KltDP.Geometry.FiniteTypeNoetherian
import KltDP.Examples.FrobeniusDiscrepancyCartierLocalEquation

/-!
# Strict normal crossings of the actual candidate-support Cartier divisor

Every original coefficient is a unit off the actual support. At a point of
its unique smooth component, the closed/generic dichotomy supplies a full
parameter system in the actual ambient dimension, respectively two or one.
The original Cartier coefficient is kept through the proved kernel identity.
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

/-- The actual original coefficient is an SNC equation along each support
component, with the complete parameter family in its actual local dimension. -/
theorem candidateSupportCartier_equation_at_curve
    (C : (sourceSurface q n a ha hproj).PrimeCurve)
    (hC : C ∈ (candidate q n a ha hproj).support) (y : C.toScheme)
    (c : RegularCartierEquationChart (sourceSurface q n a ha hproj).toScheme
      (candidateSupportCartier q n a ha hproj))
    (hyc : C.inclusion.base y ∈ c.chart.openSet) :
    IsStrictNormalCrossingsEquation
      ((sourceSurface q n a ha hproj).toScheme.presheaf.stalk (C.inclusion.base y))
      ((sourceSurface q n a ha hproj).toScheme.presheaf.germ
        c.chart.openSet (C.inclusion.base y) hyc c.coefficient) := by
  let X := sourceSurface q n a ha hproj
  rcases C.isClosed_or_eq_genericPoint y with hy | rfl
  · let f := X.toScheme.presheaf.germ c.chart.openSet (C.inclusion.base y) hyc c.coefficient
    obtain ⟨d, g, hdg, hker, _⟩ := candidate_support_stalk_parameters q n a ha hproj C hC y hy
    have hfd : Ideal.span {f} = Ideal.span {d} :=
      (candidateSupportCartier_germ_span_eq_curve_kernel q n a ha hproj C hC y c hyc).trans hker
    have hfg : Ideal.span {f, g} = maximalIdeal (X.toScheme.presheaf.stalk (C.inclusion.base y)) := by
      rw [Ideal.span_insert, hfd, ← Ideal.span_insert]
      exact hdg
    have hx : IsClosed ({C.inclusion.base y} : Set X.toScheme) := by
      simpa only [Set.image_singleton] using C.inclusion.isClosedEmbedding.isClosedMap _ hy
    exact IsStrictNormalCrossingsEquation.of_first_parameter
      (multiSurfaceSurface_regularPoints (q + 1) n a ha hproj (C.inclusion.base y))
      (X.closed_stalk_dimension_two (C.inclusion.base y) hx) f g hfg
  · let y := _root_.genericPoint C.toScheme
    let f := X.toScheme.presheaf.germ c.chart.openSet (C.inclusion.base y) hyc c.coefficient
    obtain ⟨d, hd, hker, _⟩ := C.exists_generic_stalk_parameter
    have hf : Ideal.span {f} = maximalIdeal (X.toScheme.presheaf.stalk (C.inclusion.base y)) :=
      ((candidateSupportCartier_germ_span_eq_curve_kernel q n a ha hproj C hC y c hyc).trans
        hker).trans hd
    have hdim : ringKrullDim (X.toScheme.presheaf.stalk (C.inclusion.base y)) = 1 := by
      change ringKrullDim
        (X.toScheme.presheaf.stalk (C.inclusion.base (_root_.genericPoint C.toScheme))) = 1
      rw [C.inclusion_genericPoint_eq]
      exact C.ringKrullDim_stalk_genericPoint
    exact IsStrictNormalCrossingsEquation.of_single_parameter
      (multiSurfaceSurface_regularPoints (q + 1) n a ha hproj (C.inclusion.base y)) hdim f hf

local instance : IsLocallyNoetherian (sourceSurface q n a ha hproj).toScheme :=
  (sourceSurface q n a ha hproj).isLocallyNoetherian

/-- The reduced Cartier support of the original rational candidate is
strict normal crossings on the original Frobenius surface. -/
theorem candidateSupportCartier_isStrictNormalCrossings :
    IsStrictNormalCrossingsCartier (sourceSurface q n a ha hproj).toScheme
      (candidateSupportCartier q n a ha hproj) := by
  classical
  refine ⟨candidateSupportCartier_hasRegularEquations q n a ha hproj, ?_⟩
  intro c x hxc
  by_cases hx : x ∈ divisorSupport (candidate q n a ha hproj)
  · obtain ⟨C, hC, hxC⟩ := (mem_divisorSupport _ x).mp hx
    have hrange : x ∈ Set.range C.inclusion.base := by
      rw [C.range_inclusion]
      exact hxC
    obtain ⟨y, rfl⟩ := hrange
    exact candidateSupportCartier_equation_at_curve q n a ha hproj C
      (Finsupp.mem_support_iff.mpr hC) y c hxc
  · apply Or.inl
    by_contra hf
    apply hx
    rw [← candidateSupportIdeal_support q n a ha hproj]
    exact (PrimeCurve.mem_support_iff_not_isUnit_germ _
      (candidateSupportCartier_hasRegularEquations q n a ha hproj) c x hxc).mpr hf

end KltDP.Examples.FrobeniusDiscrepancyBounds
