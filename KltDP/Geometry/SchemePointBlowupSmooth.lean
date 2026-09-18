import KltDP.Geometry.SmoothSurfacePointBlowupSmooth
import KltDP.Geometry.SchemePointBlowupSequence

/-!
Smoothness transports from the actual glued point-blowup construction to
the original map recorded by `SchemePointBlowup.IsAt`. Its source remains
the original scheme and requires no surface packaging or normality premise.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.SchemePointBlowup

/-- An actual point blowup of the original smooth surface has smooth
source over the original field, through the same composite morphism. -/
theorem IsAt.isSmooth_comp_structure
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : NormalProjectiveSurface k) [IsSmooth X.structureMorphism]
    {S : Scheme.{u}} {f : S ⟶ X.toScheme} {x : X.toScheme}
    (h : IsAt f x) : IsSmooth (f ≫ X.structureMorphism) := by
  obtain ⟨c, e, he⟩ := h
  letI := c.instCommRing
  letI := c.instOpenImmersion
  letI := c.instMaximal
  letI : IsSmooth (c.projection ≫ X.structureMorphism) :=
    X.pointBlowup_isSmooth c.j c.q c.isClosed
  rw [← he, Category.assoc]
  infer_instance

end KltDP.Geometry.SchemePointBlowup
