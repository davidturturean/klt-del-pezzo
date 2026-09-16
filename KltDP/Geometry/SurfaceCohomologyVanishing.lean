import KltDP.Compatibility.GrothendieckVanishing.GrothendieckVanishing
import KltDP.Geometry.ModuleCohomology
import KltDP.Geometry.Surface

/-!
# Cohomology above the dimension of a normal projective surface

Grothendieck vanishing applies to the underlying abelian sheaf of any actual
scheme module. The cohomology groups here are exactly `ModuleCohomology.H`,
defined through `SheafOfModules.toSheaf` and Mathlib's Ext cohomology.

For a normal projective surface, Noetherian topology follows from its projective
embedding, and its dimension is two. Thus every coefficient module has zero
cohomology in degrees greater than two. This does not assert finite-dimensionality
of the cohomology in the remaining degrees.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace KltDP.Geometry.ModuleCohomology

/-- Actual module cohomology vanishes above the topological dimension of a
Noetherian scheme. -/
theorem scheme_H_subsingleton_of_dimension_lt
    (X : Scheme.{u}) [NoetherianSpace X] (M : X.Modules)
    (n : ℕ) (hn : topologicalKrullDim X < n) :
    Subsingleton (H M n) := by
  change Subsingleton (CategoryTheory.Sheaf.H
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) n)
  exact GrothendieckVanishing X n hn
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)

/-- A normal projective surface has no module cohomology above degree two. -/
theorem normalProjectiveSurface_H_subsingleton
    {k : Type u} [Field k] (X : NormalProjectiveSurface k)
    (M : X.toScheme.Modules) (n : ℕ) (hn : 2 < n) :
    Subsingleton (H M n) := by
  apply scheme_H_subsingleton_of_dimension_lt X.toScheme M n
  rw [X.dimension_two]
  exact_mod_cast hn

/-- Elementwise form of the vanishing above degree two. -/
theorem normalProjectiveSurface_H_eq_zero
    {k : Type u} [Field k] (X : NormalProjectiveSurface k)
    (M : X.toScheme.Modules) (n : ℕ) (hn : 2 < n) (x : H M n) :
    x = 0 := by
  letI := normalProjectiveSurface_H_subsingleton X M n hn
  exact Subsingleton.elim _ _

end KltDP.Geometry.ModuleCohomology
