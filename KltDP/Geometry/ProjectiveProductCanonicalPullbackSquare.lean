import KltDP.Geometry.SchemeKaehlerPullbackMapComp
import KltDP.Geometry.SchemeModulePullbackSquareCoherence

/-!
# Original differential maps on a commuting chart square

The existing composition law for the original Kähler map gives its square
naturality through the existing module-pullback square isomorphism. These
identities retain the actual scheme maps and all equality transports. They
are used for the original product charts; no invertibility is assumed here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.ProjectiveProductCanonicalPullbackSquare

open SchemeKaehlerSheaf SchemeKaehlerPullbackMap
open SchemeModulePullbackSquareCoherence

variable {R : Type u} [CommRing R]

/-- Equality of the original morphisms transports the original differential map. -/
theorem map_morphism_eq {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    {a b : Y ⟶ X} (h : a = b) :
    (eqToIso (congrArg schemeModulePullback h)).hom.app (baseRingSheaf f) ≫
        map f b =
      map f a ≫ eqToHom (congrArg baseRingSheaf
        (congrArg (fun t => t ≫ f) h)) := by
  subst b
  simp only [eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    eqToHom_refl, Category.id_comp, Category.comp_id]

/-- Equality of the original base maps transports the original differential map. -/
theorem map_base_eq {X Y : Scheme.{u}}
    {f g : X ⟶ Spec (CommRingCat.of R)} (h : f = g) (a : Y ⟶ X) :
    (schemeModulePullback a).map (eqToHom (congrArg baseRingSheaf h)) ≫ map g a =
      map f a ≫ eqToHom (congrArg baseRingSheaf
        (congrArg (fun t => a ≫ t) h)) := by
  subst g
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id]

variable {X Y V S : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (p : Y ⟶ X) (i : V ⟶ X)
    (j : S ⟶ Y) (q : S ⟶ V) (h : j ≫ p = q ≫ i)

include h in
/-- The actual equality of the associated structure maps on a commuting square. -/
theorem square_structure : j ≫ (p ≫ f) = q ≫ (i ≫ f) :=
  (Category.assoc j p f).symm.trans
    ((congrArg (fun t => t ≫ f) h).trans (Category.assoc q i f))

/-- The original Kähler maps commute with the original pullback-square comparison. -/
theorem square_map :
    (squareIso i p q j h (baseRingSheaf f)).hom ≫
        (schemeModulePullback q).map (map f i) ≫ map (i ≫ f) q =
      (schemeModulePullback j).map (map f p) ≫ map (p ≫ f) j ≫
        eqToHom (congrArg baseRingSheaf (square_structure f p i j q h)) := by
  have ht :
      eqToHom (congrArg baseRingSheaf (congrArg (fun t => t ≫ f) h)) ≫
          eqToHom (congrArg baseRingSheaf (Category.assoc q i f)) =
        eqToHom (congrArg baseRingSheaf (Category.assoc j p f)) ≫
          eqToHom (congrArg baseRingSheaf (square_structure f p i j q h)) := by
    simp only [eqToHom_trans]
  rw [← map_comp f i q]
  simp only [squareIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.app_hom, Iso.app_inv, Iso.inv_hom_id_app_assoc]
  rw [← Category.assoc
    ((eqToIso (congrArg schemeModulePullback h)).hom.app (baseRingSheaf f))
    (map f (q ≫ i)), map_morphism_eq f h]
  simp only [Category.assoc, eqToIso.hom]
  rw [ht]
  have hc := congrArg
    (fun a => a ≫ eqToHom
      (congrArg baseRingSheaf (square_structure f p i j q h)))
    (map_comp f p j)
  simpa only [Category.assoc, eqToIso.hom] using hc

end KltDP.Geometry.ProjectiveProductCanonicalPullbackSquare
