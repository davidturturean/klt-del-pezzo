import KltDP.Geometry.PrincipalQuotientParameters
import KltDP.Geometry.PrimeCurveCrossingCoefficient
import KltDP.Geometry.SmoothSurfaceRegularity
import KltDP.Geometry.ClosedPointDimension

/-!
# Original smooth-prime-curve equations are ambient regular parameters

At a closed point of a smooth prime curve on a smooth surface, its actual
stalk is a DVR. The original Cartier coefficient generates the original
curve-inclusion stalk kernel. Lifting a uniformizer therefore extends this
same coefficient to a regular parameter pair of the actual surface stalk.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

universe u

namespace KltDP.Geometry.NormalProjectiveSurface.PrimeCurve

open KltDP.Geometry

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k) [IsSmooth X.structureMorphism]
  (C : X.PrimeCurve) [IsSmooth C.toSpec]

local instance stalkParameters_curveStalk_domain (y : C.toScheme) :
    IsDomain (C.toScheme.presheaf.stalk y) :=
  integralSchemeStalk_isDomain C.toScheme y

/-- Every original canonical Cartier equation of the smooth prime curve
is a regular parameter at each actual closed point where it is defined. -/
theorem cartierCoefficient_is_parameter (y : C.toScheme)
    (hy : IsClosed ({y} : Set C.toScheme))
    (c : RegularCartierEquationChart X.toScheme
      (X.primeCurveCartier X.regularPoints_of_isSmooth C))
    (hyc : C.inclusion.base y ∈ c.chart.openSet) :
    let f := X.toScheme.presheaf.germ c.chart.openSet (C.inclusion.base y) hyc c.coefficient
    ∃ g : X.toScheme.presheaf.stalk (C.inclusion.base y),
      Ideal.span {f, g} = maximalIdeal (X.toScheme.presheaf.stalk (C.inclusion.base y)) ∧
      RingHom.ker (C.inclusion.stalkMap y).hom = Ideal.span {f} ∧
      f ∉ (maximalIdeal (X.toScheme.presheaf.stalk (C.inclusion.base y))) ^ 2 := by
  let f := X.toScheme.presheaf.germ c.chart.openSet (C.inclusion.base y) hyc c.coefficient
  let U : X.toScheme.affineOpens :=
    ⟨(X.toScheme.affineCover.map (C.inclusion.base y)).opensRange,
      isAffineOpen_opensRange (X.toScheme.affineCover.map (C.inclusion.base y))⟩
  have hyU : C.inclusion.base y ∈ U.1 := X.toScheme.affineCover.covers (C.inclusion.base y)
  have hker : RingHom.ker (C.inclusion.stalkMap y).hom = Ideal.span {f} :=
    (C.vanishingIdeal.stalkMap_gluedTo_ker_eq_map U hyU).trans
      (PrimeCurveCrossingCoefficient.vanishingIdeal_map_germ_eq_span_coefficient
        X X.regularPoints_of_isSmooth C U (C.inclusion.base y) hyU c hyc)
  letI := C.stalk_isDiscreteValuationRing_of_isSmooth y hy
  obtain ⟨g, hspan⟩ := PrincipalQuotientParameters.exists_companion
    (C.inclusion.stalkMap y).hom (C.inclusion.stalkMap_surjective y) f hker
  have hx : IsClosed ({C.inclusion.base y} : Set X.toScheme) := by
    simpa only [Set.image_singleton] using C.inclusion.isClosedEmbedding.isClosedMap _ hy
  exact ⟨g, hspan, hker, PrincipalQuotientParameters.first_not_mem_square
    (X.regularPoints_of_isSmooth (C.inclusion.base y))
    (X.closed_stalk_dimension_two (C.inclusion.base y) hx) f g hspan⟩

/-- Existence of the actual ambient regular parameters and original
curve kernel at every closed point, with no equation or parameter premise. -/
theorem exists_stalk_parameters (y : C.toScheme) (hy : IsClosed ({y} : Set C.toScheme)) :
    ∃ f g : X.toScheme.presheaf.stalk (C.inclusion.base y),
      Ideal.span {f, g} = maximalIdeal (X.toScheme.presheaf.stalk (C.inclusion.base y)) ∧
      RingHom.ker (C.inclusion.stalkMap y).hom = Ideal.span {f} ∧
      f ∉ (maximalIdeal (X.toScheme.presheaf.stalk (C.inclusion.base y))) ^ 2 := by
  obtain ⟨c, hyc⟩ := X.primeCurveCartier_hasRegularEquations X.regularPoints_of_isSmooth C
    (C.inclusion.base y)
  obtain ⟨g, hspan, hker, hf⟩ := cartierCoefficient_is_parameter X C y hy c hyc
  exact ⟨_, g, hspan, hker, hf⟩

end KltDP.Geometry.NormalProjectiveSurface.PrimeCurve
