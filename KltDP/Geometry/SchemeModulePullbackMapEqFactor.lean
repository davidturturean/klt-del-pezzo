import KltDP.Geometry.SchemeConormal

/-!
# Transport an actual pullback factor along an equality of original maps

Equality elimination is performed with abstract schemes and module objects.
The later concrete application checks only the original scheme-map equality.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace KltDP.Geometry.SchemeModulePullbackMapEqFactor

universe u

variable {X Y : Scheme.{u}} {l l' : X ⟶ Y} (h : l = l')
variable {M N T : Y.Modules}

def iso (e : (schemeModulePullback l).obj M ≅ (schemeModulePullback l).obj N) :
    (schemeModulePullback l').obj M ≅ (schemeModulePullback l').obj N := h ▸ e

theorem iso_comp
    (e : (schemeModulePullback l).obj M ≅ (schemeModulePullback l).obj N)
    (i : N ⟶ T) (m : M ⟶ T)
    (he : e.hom ≫ (schemeModulePullback l).map i = (schemeModulePullback l).map m) :
    (iso h e).hom ≫ (schemeModulePullback l').map i =
      (schemeModulePullback l').map m := by
  cases h
  exact he

end KltDP.Geometry.SchemeModulePullbackMapEqFactor
