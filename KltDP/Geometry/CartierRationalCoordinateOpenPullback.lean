import KltDP.Geometry.CartierOpenPullbackInclusion
import KltDP.Geometry.CartierRationalCoordinate

/-!
# Exact rational coordinates under the original open module pullback

The actual open Cartier pullback isomorphism specifies the pulled-back
representative. Its fractional inclusion square fixes the rational coordinate
of that representative, without an additional compatibility hypothesis.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.CartierRationalCoordinate

open OpenImmersionRational

/-- Changing only the Cartier-divisor expression by its actual equality
does not change the coordinate morphism into the rational module. -/
theorem coordinate_eqToIso_left (X : Scheme.{u}) [IsIntegral X]
    (D E : CartierDivisor X) (h : D = E) (M : X.Modules)
    (e : cartierDivisorModule X E ≅ M) :
    coordinate X D M (eqToIso (congrArg (cartierDivisorModule X) h) ≪≫ e) =
      coordinate X E M e := by
  subst E
  simp only [eqToIso_refl, Iso.refl_trans]

/-- Composing the actual module identification changes the coordinate by
the inverse of that same module isomorphism. -/
theorem hom_comp_coordinate_trans (X : Scheme.{u}) [IsIntegral X]
    (D : CartierDivisor X) (M N : X.Modules)
    (e : cartierDivisorModule X D ≅ M) (a : M ≅ N) :
    a.hom ≫ coordinate X D N (e ≪≫ a) = coordinate X D M e := by
  simp only [coordinate, Iso.trans_inv, Category.assoc, Iso.hom_inv_id_assoc]

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : Y ⟶ X) [IsOpenImmersion f]

/-- The pulled-back module identification uses the original normalized
open Cartier isomorphism, with no independently chosen rational scalar. -/
def openPullbackIso (D : CartierDivisor X) (M : X.Modules)
    (e : cartierDivisorModule X D ≅ M) :
    cartierDivisorModule Y (cartierRestrictionHom f D) ≅
      (schemeModulePullback f).obj M :=
  (cartierModulePullbackIso f D).symm ≪≫ (schemeModulePullback f).mapIso e

/-- The rational coordinate of this original pulled-back representative
is precisely the original coordinate followed by rational-function pullback. -/
theorem coordinate_openPullbackIso (D : CartierDivisor X) (M : X.Modules)
    (e : cartierDivisorModule X D ≅ M) :
    coordinate Y (cartierRestrictionHom f D) ((schemeModulePullback f).obj M)
        (openPullbackIso f D M e) =
      (schemeModulePullback f).map (coordinate X D M e) ≫
        (rationalModulePullbackIso f).hom := by
  calc
    _ = (schemeModulePullback f).map e.inv ≫
        ((cartierModulePullbackIso f D).hom ≫
          cartierDivisorModuleInclusion Y (cartierRestrictionHom f D)) := by
      simp only [coordinate, openPullbackIso, Iso.trans_inv, Iso.symm_inv,
        Functor.mapIso_inv, Category.assoc]
    _ = (schemeModulePullback f).map e.inv ≫
        ((schemeModulePullback f).map (cartierDivisorModuleInclusion X D) ≫
          (rationalModulePullbackIso f).hom) := by
      rw [cartierModulePullbackIso_inclusion]
    _ = _ := by
      rw [← Category.assoc, ← Functor.map_comp]
      rfl

end KltDP.Geometry.CartierRationalCoordinate

#check @KltDP.Geometry.CartierRationalCoordinate.coordinate_openPullbackIso
#print axioms KltDP.Geometry.CartierRationalCoordinate.coordinate_openPullbackIso
