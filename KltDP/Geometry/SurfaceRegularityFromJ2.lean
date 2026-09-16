import KltDP.Geometry.SurfaceRegularCharts
import KltDP.Geometry.SurfaceSingularPoints
import KltDP.Literature.Definitions.J2

/-!
# Normal-surface regularity from the literal J-2 condition

This module proves the specialization from the published ring condition to
the actual surface. The base-to-chart algebra is the original structure
map, and the generator/cotangent comparison on chart localizations is proved
in `SurfaceRegularCharts`. J-2 is an explicit source input here; no literature
axiom is declared or used in this module.
-/

noncomputable section

open AlgebraicGeometry

universe u

namespace KltDP.Geometry

/-- Apply J-2 to the actual finite-type coordinate algebra on each member of
the original surface's affine cover, then glue the proved locus identities. -/
theorem normalSurface_regularLocus_isOpen_of_J2
    {k : Type u} [Field k] (X : NormalProjectiveSurface k)
    (hk : Literature.J2Ring.{u, u} k) : IsOpen (regularLocus X.toScheme) := by
  apply X.isOpen_regularLocus_of_generatorRegularLocus_on_affineCover
    X.toScheme.affineOpenCover
  intro i
  letI : Algebra k (X.toScheme.affineOpenCover.obj i) :=
    X.affineChartAlgebra (R := X.toScheme.affineOpenCover.obj i)
      (X.toScheme.affineOpenCover.map i)
  letI : Algebra.FiniteType k (X.toScheme.affineOpenCover.obj i) :=
    X.affineChartAlgebra_finiteType (R := X.toScheme.affineOpenCover.obj i)
      (X.toScheme.affineOpenCover.map i)
  exact hk.isOpen_generatorRegularLocus (X.toScheme.affineOpenCover.obj i)

/-- The actual singular locus is finite over a field satisfying J-2.
Pointwise closedness and Noetherianity are already proved from the surface. -/
theorem normalSurface_singularLocus_finite_of_J2
    {k : Type u} [Field k] (X : NormalProjectiveSurface k)
    (hk : Literature.J2Ring.{u, u} k) : (singularLocus X.toScheme).Finite :=
  normalSurface_singularLocus_finite_of_isOpen_regularLocus X
    (normalSurface_regularLocus_isOpen_of_J2 X hk)

/-- An explicit finite set of exactly the nonregular actual scheme points.
The finite set is constructed after the preceding finiteness proof. -/
theorem normalSurface_exists_singularPointFinset_of_J2
    {k : Type u} [Field k] (X : NormalProjectiveSurface k)
    (hk : Literature.J2Ring.{u, u} k) :
    ∃ s : Finset X.Point, ∀ x : X.Point,
      x ∈ s ↔ ¬ RegularLocal (X.stalk x) :=
  ⟨singularPointFinset X.toScheme (normalSurface_singularLocus_finite_of_J2 X hk),
    mem_singularPointFinset X.toScheme (normalSurface_singularLocus_finite_of_J2 X hk)⟩

end KltDP.Geometry
