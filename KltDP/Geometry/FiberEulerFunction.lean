import KltDP.Geometry.PicardEulerValue
import KltDP.Geometry.SchemeModulePullbackUnit
import Mathlib.AlgebraicGeometry.Fiber

/-! Euler values of the actual residue-field fibers with the actual
pulled-back coefficient module. No local constancy is asserted here. -/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry

variable {X Y : Scheme.{u}}

/-- Original residue-field fiber Euler characteristic. -/
def fiberEuler (f : X ⟶ Y) (M : X.Modules) (y : Y) : ℤ :=
  ModuleCohomology.eulerCharacteristic (f.fiberToSpecResidueField y)
    ((schemeModulePullback (f.fiberι y)).obj M)

/-- For the structure module, the coefficient is canonically the actual
fiber's structure module, over its original residue field. -/
theorem fiberEuler_unit (f : X ⟶ Y) (y : Y) :
    fiberEuler f (SheafOfModules.unit X.ringCatSheaf) y =
      ModuleCohomology.eulerCharacteristic (f.fiberToSpecResidueField y)
        (SheafOfModules.unit (f.fiber y).ringCatSheaf) := by
  exact ModuleCohomology.eulerCharacteristic_eq_of_iso
    (f.fiberToSpecResidueField y) (schemeModulePullbackUnitIso (f.fiberι y))

end KltDP.Geometry

#print axioms KltDP.Geometry.fiberEuler_unit
