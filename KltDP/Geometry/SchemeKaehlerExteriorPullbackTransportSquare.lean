import KltDP.Geometry.SchemeKaehlerExteriorPullbackTransportSource

/-!
# The original exterior differential on an actual commuting scheme square

Use the already proved composition identity along the two paths. The source
isomorphism consists only of the original pullback composition and the proved
scheme-map equality. No differential compatibility is an input premise.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.SchemeKaehlerExteriorPullbackTransport

open SchemeKaehlerSheaf

variable {k : Type u} [CommRing k] {X Y Z W : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k))
    (j : Y ⟶ X) (l : Z ⟶ Y) (c : W ⟶ X) (b : Z ⟶ W)
    (hsq : l ≫ j = b ≫ c) (n : ℕ)

/-- The original pullback source comparison around the actual commuting square. -/
def squareSourceIso :
    (schemeModulePullback l).obj
        ((schemeModulePullback j).obj (SchemeExteriorPower.sheaf (baseRingSheaf f) n)) ≅
      (schemeModulePullback b).obj
        ((schemeModulePullback c).obj (SchemeExteriorPower.sheaf (baseRingSheaf f) n)) :=
  sourceIso f j l (b ≫ c) hsq n ≪≫
    (sourceIso f c b (b ≫ c) rfl n).symm

/-- The whole original exterior maps commute through the original source comparison. -/
theorem map_square
    (g : Y ⟶ Spec (CommRingCat.of k)) (hg : j ≫ f = g)
    (p : W ⟶ Spec (CommRingCat.of k)) (hp : c ≫ f = p)
    (q : Z ⟶ Spec (CommRingCat.of k))
    (hl : l ≫ g = q) (hb : b ≫ p = q) :
    (schemeModulePullback l).map (map f j g hg n) ≫ map g l q hl n =
      (squareSourceIso f j l c b hsq n).hom ≫
        (schemeModulePullback b).map (map f c p hp n) ≫ map p b q hb n := by
  have hq : (b ≫ c) ≫ f = q := by
    rw [Category.assoc, hp, hb]
  rw [map_comp_sourceIso f j l g hg (b ≫ c) hsq q hl hq n,
    map_comp_sourceIso f c b p hp (b ≫ c) rfl q hb hq n]
  simp only [squareSourceIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_assoc]

end KltDP.Geometry.SchemeKaehlerExteriorPullbackTransport
