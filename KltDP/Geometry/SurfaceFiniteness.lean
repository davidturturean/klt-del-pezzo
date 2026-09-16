import KltDP.Geometry.SurfaceRegularityFromJ2
import KltDP.Literature.Stacks.FieldJ2

/-!
# Finite singular loci on actual normal projective surfaces

The only external input is the literal field case of Stacks 07PJ(1).
The ring-to-surface specialization, comparison of regularity definitions,
closedness of singular points, and finite-set construction are proved in
separate modules. No bound on the number of singular points is asserted.
-/

noncomputable section

open AlgebraicGeometry

universe u

namespace KltDP.Geometry

/-- The regular locus of an actual normal projective surface is open. -/
theorem normalSurface_regularLocus_isOpen
    {k : Type u} [Field k] (X : NormalProjectiveSurface k) :
    IsOpen (regularLocus X.toScheme) :=
  normalSurface_regularLocus_isOpen_of_J2 X (Literature.Stacks.field_isJ2.{u, u} k)

/-- Finiteness of the actual nonregular scheme points, before taking cardinality. -/
theorem normalSurface_singularLocus_finite
    {k : Type u} [Field k] (X : NormalProjectiveSurface k) :
    (singularLocus X.toScheme).Finite :=
  normalSurface_singularLocus_finite_of_J2 X (Literature.Stacks.field_isJ2.{u, u} k)

namespace NormalProjectiveSurface

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)

/-- The finite set of all actual singular points of the surface. -/
def singularPoints : Finset X.Point :=
  singularPointFinset X.toScheme (normalSurface_singularLocus_finite X)

@[simp]
theorem mem_singularPoints (x : X.Point) :
    x ∈ X.singularPoints ↔ ¬ RegularLocal (X.stalk x) :=
  mem_singularPointFinset X.toScheme (normalSurface_singularLocus_finite X) x

/-- The number of distinct singular points after their finiteness is proved. -/
def singularPointCount : ℕ := X.singularPoints.card

/-- The numerical bound is equivalent to an explicit finite-set statement. -/
theorem singularPointCount_le_iff (bound : ℕ) :
    X.singularPointCount ≤ bound ↔
      ∃ s : Finset X.Point,
        (∀ x : X.Point, x ∈ s ↔ ¬ RegularLocal (X.stalk x)) ∧ s.card ≤ bound :=
  nSing_le_iff_exists_finset X.toScheme (normalSurface_singularLocus_finite X) bound

end NormalProjectiveSurface
end KltDP.Geometry
