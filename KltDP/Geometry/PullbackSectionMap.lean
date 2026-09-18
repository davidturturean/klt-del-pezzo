import KltDP.Geometry.InvertibleSheafSectionPowersPullback

/-! # The original pullback of sections commutes with the original module morphism -/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry

variable {X Y : Scheme.{u}} (h : Y ⟶ X)

/-- Naturality of actual compatible section pullback, proved from the
original unit comparison and original functor composition. -/
theorem pullbackSection_sectionsMap {M N : X.Modules} (g : M ⟶ N) (s : M.sections) :
    _root_.SheafOfModules.sectionsMap ((schemeModulePullback h).map g)
      (InvertibleSheafSectionPowersPullback.pullbackSection h M s) =
    InvertibleSheafSectionPowersPullback.pullbackSection h N
      (_root_.SheafOfModules.sectionsMap g s) := by
  change ((schemeModulePullback h).obj N).unitHomEquiv
    (((schemeModulePullbackUnitIso h).inv ≫
      (schemeModulePullback h).map (M.unitHomEquiv.symm s)) ≫
        (schemeModulePullback h).map g) =
    ((schemeModulePullback h).obj N).unitHomEquiv
      ((schemeModulePullbackUnitIso h).inv ≫ (schemeModulePullback h).map
        (N.unitHomEquiv.symm (_root_.SheafOfModules.sectionsMap g s)))
  apply congrArg ((schemeModulePullback h).obj N).unitHomEquiv
  rw [← _root_.SheafOfModules.unitHomEquiv_symm_comp,
    Functor.map_comp, Category.assoc]

end KltDP.Geometry
