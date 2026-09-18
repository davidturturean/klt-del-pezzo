import KltDP.Geometry.SchemePointBlowupSequenceIntegral
import KltDP.Geometry.PointBlowupCurveDimension

/-!
The source of an actual point blowup of the original surface is integral
and two-dimensional. Both properties are consequences of its original
glued Rees presentation, transported by the actual isomorphism in `IsAt`.
No source surface package, normality, or dimension hypothesis is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.SchemePointBlowup

variable {k : Type u} [Field k] [IsAlgClosed k]
    (X : NormalProjectiveSurface k)
    {S : Scheme.{u}} {f : S ⟶ X.toScheme} {x : X.toScheme}

/-- The actual closed centre is non-generic on the original surface, so
the original point-blowup source is integral. -/
theorem IsAt.source_isIntegral_of_surface (h : IsAt f x) : IsIntegral S :=
  h.source_isIntegral (X.closedPoint_ne_genericPoint x h.isClosed)

/-- The original source has dimension two by the actual glued-blowup
dimension theorem and its original scheme isomorphism. -/
theorem IsAt.source_dimension_two (h : IsAt f x) : topologicalKrullDim S = 2 := by
  obtain ⟨c, e, he⟩ := h
  letI := c.instCommRing
  letI := c.instOpenImmersion
  letI := c.instMaximal
  exact (IsHomeomorph.topologicalKrullDim_eq
    e.schemeIsoToHomeo e.schemeIsoToHomeo.isHomeomorph).trans
      (PointBlowupGluing.surface_scheme_dimension_two X c.j c.q c.isClosed)

end KltDP.Geometry.SchemePointBlowup
