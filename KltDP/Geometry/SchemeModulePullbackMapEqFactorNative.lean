import KltDP.Geometry.SchemeModulePullbackMapEqFactor

/-!
# Infer the original native factor before transporting its map

The isomorphism and its normalization are supplied before the equality of
original scheme maps. This keeps their native module carriers during inference.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace KltDP.Geometry.SchemeModulePullbackMapEqFactor

universe u

variable {X Y : Scheme.{u}} {l l' : X ⟶ Y} {M N T : Y.Modules}

def nativeIso
    (e : (schemeModulePullback l).obj M ≅ (schemeModulePullback l).obj N)
    (h : l = l') :
    (schemeModulePullback l').obj M ≅ (schemeModulePullback l').obj N := iso h e

theorem nativeIso_comp
    (e : (schemeModulePullback l).obj M ≅ (schemeModulePullback l).obj N)
    (i : N ⟶ T) (m : M ⟶ T)
    (he : e.hom ≫ (schemeModulePullback l).map i = (schemeModulePullback l).map m)
    (h : l = l') :
    (nativeIso e h).hom ≫ (schemeModulePullback l').map i =
      (schemeModulePullback l').map m := iso_comp h e i m he

end KltDP.Geometry.SchemeModulePullbackMapEqFactor
