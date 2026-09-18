import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-! Flatness over the original base through actual affine section modules.
For a quasi-coherent module this is the affine criterion of Stacks 01U4(2).
The base action is restriction through the original scheme section map.
No cohomological consequence is part of this definition. -/

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
universe u
namespace KltDP.Geometry

variable {X Y : Scheme.{u}}

/-- The actual affine-section criterion for relative module flatness. -/
def IsFlatModuleOver (f : X ⟶ Y) (M : X.Modules) : Prop :=
  ∀ (U : Y.affineOpens) (V : X.affineOpens) (e : V.1 ≤ f ⁻¹ᵁ U.1),
    letI : Module Γ(Y, U.1) (M.val.obj (op V.1)) :=
      Module.compHom _ (f.appLE U V e).hom
    Module.Flat Γ(Y, U.1) (M.val.obj (op V.1))

/-- The structure module's relative flatness is exactly flatness of the
original scheme morphism, with the same affine section maps. -/
theorem isFlatModuleOver_unit_iff (f : X ⟶ Y) :
    IsFlatModuleOver f (SheafOfModules.unit X.ringCatSheaf) ↔ Flat f := by
  constructor
  · intro h
    exact ⟨fun U V e => h U V e⟩
  · intro h
    letI : Flat f := h
    exact fun U V e => Flat.flat_of_affine_subset U V e

end KltDP.Geometry

#print axioms KltDP.Geometry.isFlatModuleOver_unit_iff
