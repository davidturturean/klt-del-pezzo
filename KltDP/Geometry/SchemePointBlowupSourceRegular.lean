import KltDP.Geometry.SchemePointBlowupSurfaceGeometry
import KltDP.Geometry.SchemePointBlowupSmooth
import KltDP.Geometry.SmoothFieldAllPointsRegular

/-!
Every original stalk of an actual point-blowup source is regular.
Integrality, dimension and smoothness of its original field structure
are derived before applying the noncircular all-point regularity theorem.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.SchemePointBlowup

/-- An actual point blowup of the original smooth surface is regular at
every original source point, without a source-normality hypothesis. -/
theorem IsAt.source_regular
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : NormalProjectiveSurface k) [IsSmooth X.structureMorphism]
    {S : Scheme.{u}} {f : S ⟶ X.toScheme} {x : X.toScheme}
    (h : IsAt f x) : ∀ y : S, RegularPoint S y := by
  letI : IsIntegral S := h.source_isIntegral_of_surface X
  letI : IsSmooth (f ≫ X.structureMorphism) := h.isSmooth_comp_structure X
  exact SmoothFieldRegularPoints.regularPoints_of_isSmooth_of_dimension_le_two
    (f ≫ X.structureMorphism) (h.source_dimension_two X).le

end KltDP.Geometry.SchemePointBlowup
