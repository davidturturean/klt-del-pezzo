import KltDP.Geometry.SchemeKaehlerPullbackRestrictionComp

/-!
# The original source-isomorphism projection with independently bound schemes

Infer the three original arrows from their proved base-map equality. This
stage contains neither quotient-ring construction nor a whole adjunction
equation; it caches only the original composite-isomorphism hom projection.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.SchemeKaehlerRefinementHomPresentation

/-- Present the original refinement hom using the arrows of its proved base square. -/
def hom_equation {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    {b : X ⟶ Spec (CommRingCat.of R)} {j : Y ⟶ X}
    {g : Y ⟶ Spec (CommRingCat.of R)}
    (hBase : j ≫ b = g) (hOpen : IsOpenImmersion j) :=
  let _ : IsOpenImmersion j := hOpen
  (Iso.trans_hom (SchemeKaehlerOpenRestriction.pullbackIso b j)
    (eqToIso (congrArg SchemeKaehlerSheaf.baseRingSheaf hBase))).symm

end KltDP.Geometry.SchemeKaehlerRefinementHomPresentation
