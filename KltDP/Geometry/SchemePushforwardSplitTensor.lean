import KltDP.Geometry.ClosedImmersionProjectionFormula
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Tensoring an actual structure-sheaf pushforward splitting

The existing projection formula and preservation of biproducts by tensoring
with an invertible sheaf carry the original splitting of f_*O to the
pushforward of the original pulled line. No affine or cohomology theorem
is used in this ordinary sheaf comparison.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
universe u

namespace KltDP.Geometry.SchemePushforwardSplitTensor

local instance splitTensorModules (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

variable {X Y : Scheme.{u}} (f : Y ⟶ X) (N : X.Modules)
  (e : (schemeModulePushforward f).obj (_root_.SheafOfModules.unit Y.ringCatSheaf) ≅
    _root_.SheafOfModules.unit X.ringCatSheaf ⊞ N)

/-- An original structure-sheaf splitting produces the actual twisted
pushforward splitting for every original invertible sheaf. -/
def iso (L : InvertibleSheaf X) :
    (schemeModulePushforward f).obj ((schemeModulePullback f).obj L.obj) ≅
      L.obj ⊞ (N ⊗ L.obj) := by
  letI := L.tensorRight_preservesZeroMorphisms
  letI := L.tensorRight_preservesFiniteLimits
  letI := preservesBinaryBiproducts_of_preservesBinaryProducts (tensorRight L.obj)
  exact (Classical.choice (InvertibleSheaf.exists_pushforwardUnitTensorIso f L)).symm ≪≫
    (tensorRight L.obj).mapIso e ≪≫
    (tensorRight L.obj).mapBiprod (_root_.SheafOfModules.unit X.ringCatSheaf) N ≪≫
    biprod.mapIso (schemeUnitTensorLeftIso X L.obj) (Iso.refl (N ⊗ L.obj))

end KltDP.Geometry.SchemePushforwardSplitTensor

#print axioms KltDP.Geometry.SchemePushforwardSplitTensor.iso
