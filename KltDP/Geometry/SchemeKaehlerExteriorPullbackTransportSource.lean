import KltDP.Geometry.SchemeKaehlerExteriorPullbackTransportComp

/-!
# The original source isomorphism in the exterior composition diagram

Name the original pullback-composition and scheme-equality comparison before
specializing to a geometric chart. The associativity normalization is proved
once on arbitrary schemes and the original differential maps.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.SchemeKaehlerExteriorPullbackTransport

open SchemeKaehlerSheaf

variable {k : Type u} [CommRing k] {X Y Z : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (j : Y ⟶ X) (l : Z ⟶ Y)

/-- The original composition isomorphism followed by the actual scheme-map equality. -/
def sourceIso (t : Z ⟶ X) (ht : l ≫ j = t) (n : ℕ) :
    (schemeModulePullback l).obj
        ((schemeModulePullback j).obj (SchemeExteriorPower.sheaf (baseRingSheaf f) n)) ≅
      (schemeModulePullback t).obj (SchemeExteriorPower.sheaf (baseRingSheaf f) n) :=
  (schemeModulePullbackCompIso l j).app (SchemeExteriorPower.sheaf (baseRingSheaf f) n) ≪≫
    eqToIso (congrArg
      (fun r => (schemeModulePullback r).obj (SchemeExteriorPower.sheaf (baseRingSheaf f) n)) ht)

/-- The whole original composition diagram, with that same source isomorphism grouped. -/
theorem map_comp_sourceIso
    (g : Y ⟶ Spec (CommRingCat.of k)) (hg : j ≫ f = g)
    (t : Z ⟶ X) (ht : l ≫ j = t)
    (q : Z ⟶ Spec (CommRingCat.of k)) (hq : l ≫ g = q) (hqt : t ≫ f = q) (n : ℕ) :
    (schemeModulePullback l).map (map f j g hg n) ≫ map g l q hq n =
      (sourceIso f j l t ht n).hom ≫ map f t q hqt n := by
  simpa only [sourceIso, Iso.trans_hom, Iso.app_hom, Category.assoc] using
    map_comp f j l g hg t ht q hq hqt n

end KltDP.Geometry.SchemeKaehlerExteriorPullbackTransport
