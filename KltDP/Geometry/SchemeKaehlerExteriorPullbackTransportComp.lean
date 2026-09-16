import KltDP.Geometry.SchemeKaehlerExteriorPullbackTransport
import KltDP.Geometry.SchemeKaehlerExteriorPullbackComp

/-!
# Composition with the original structure-map equalities

Eliminate only the supplied equalities of the actual scheme morphisms.
The remaining identity is exactly the already constructed exterior
pullback-composition identity, with its original association transport.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.SchemeKaehlerExteriorPullbackTransport

open SchemeKaehlerSheaf

variable {k : Type u} [CommRing k] {X Y Z : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (j : Y ⟶ X) (l : Z ⟶ Y)
    (g : Y ⟶ Spec (CommRingCat.of k)) (hg : j ≫ f = g)
    (t : Z ⟶ X) (ht : l ≫ j = t)
    (q : Z ⟶ Spec (CommRingCat.of k)) (hq : l ≫ g = q) (hqt : t ≫ f = q) (n : ℕ)

/-- The original diagram commutes under the original source and structure-map equalities. -/
theorem map_comp :
    (schemeModulePullback l).map (map f j g hg n) ≫ map g l q hq n =
      (schemeModulePullbackCompIso l j).hom.app (SchemeExteriorPower.sheaf (baseRingSheaf f) n) ≫
        (eqToIso (congrArg
          (fun r => (schemeModulePullback r).obj (SchemeExteriorPower.sheaf (baseRingSheaf f) n))
          ht)).hom ≫ map f t q hqt n := by
  cases hg
  cases ht
  cases hq
  simpa only [map, eqToIso_refl, Iso.refl_hom, Category.comp_id, Category.id_comp] using
    (SchemeKaehlerExteriorPullbackMap.map_comp f j l n).symm

end KltDP.Geometry.SchemeKaehlerExteriorPullbackTransport
