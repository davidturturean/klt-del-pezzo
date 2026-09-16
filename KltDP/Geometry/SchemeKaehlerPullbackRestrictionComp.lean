import KltDP.Geometry.SchemeKaehlerOpenRestrictionComp

/-!
# The original differential restriction through actual scheme pullback

The accepted restriction isomorphism and the original restriction/pullback
comparison identify the actual pullback of the Kähler sheaf. Naturality of
that comparison transfers the already proved restriction composition law
to the original scheme-module pullback composition isomorphism.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.SchemeKaehlerOpenRestriction

open SchemeKaehlerSheaf SchemeModuleRestriction

attribute [local instance] Types.instFunLike Types.instConcreteCategory

private theorem comparison_word
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F G : C ⥤ D} (e : F ≅ G) {P Q : D ⥤ E} (a : P ≅ Q)
    (M : C) {N : D} {V W : E} (s : F.obj M ≅ N)
    (t : P.obj N ≅ W) (b : Q.obj (G.obj M) ≅ V) (v : V ≅ W)
    (h : P.mapIso (e.app M) ≪≫ a.app (G.obj M) ≪≫ b ≪≫ v =
      P.mapIso s ≪≫ t) :
    b ≪≫ v = Q.mapIso ((e.app M).symm ≪≫ s) ≪≫ (a.app N).symm ≪≫ t := by
  apply Iso.ext
  apply (cancel_epi ((P.mapIso (e.app M)).hom ≫ (a.app (G.obj M)).hom)).mp
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp,
    Iso.app_hom, Iso.app_inv, Category.assoc]
  have hh : P.map (e.app M).hom ≫ a.hom.app (G.obj M) ≫ b.hom ≫ v.hom =
      P.map s.hom ≫ t.hom := by
    simpa only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Category.assoc]
      using congrArg Iso.hom h
  have hn := congrArg (fun z => P.map (e.app M).hom ≫ z ≫ t.hom)
    (NatIso.naturality_2 a ((e.app M).inv ≫ s.hom))
  have hn' : P.map (e.app M).hom ≫ a.hom.app (G.obj M) ≫
        Q.map (e.app M).inv ≫ Q.map s.hom ≫ a.inv.app N ≫ t.hom =
      P.map s.hom ≫ t.hom := by
    simpa only [Functor.map_comp, Category.assoc, Iso.map_hom_inv_id_assoc] using hn
  exact hh.trans hn'.symm

variable {k : Type u} [CommRing k] {X Y Z : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) (j : Y ⟶ X) [IsOpenImmersion j]

/-- The original Kähler restriction isomorphism through the actual scheme pullback. -/
def pullbackIso :
    (schemeModulePullback j).obj (baseRingSheaf f) ≅ baseRingSheaf (j ≫ f) :=
  ((restrictionIsoPullback j).app (baseRingSheaf f)).symm ≪≫ restrictionIso f j

/-- These actual pullback comparisons compose through the original pullback
composition and the canonical reassociation of the original structure maps. -/
theorem pullbackIso_comp (l : Z ⟶ Y) [IsOpenImmersion l] :
    (schemeModulePullbackCompIso l j).app (baseRingSheaf f) ≪≫
        pullbackIso f (l ≫ j) ≪≫
          eqToIso (congrArg baseRingSheaf (Category.assoc l j f)) =
      (schemeModulePullback l).mapIso (pullbackIso f j) ≪≫
        pullbackIso (j ≫ f) l := by
  have h := comparison_word (restrictionIsoPullback j) (restrictionIsoPullback l)
    (baseRingSheaf f) (restrictionIso f j) (restrictionIso (j ≫ f) l)
    ((schemeModulePullbackCompIso l j).app (baseRingSheaf f) ≪≫
      ((restrictionIsoPullback (l ≫ j)).app (baseRingSheaf f)).symm)
    (restrictionIso f (l ≫ j) ≪≫
      eqToIso (congrArg baseRingSheaf (Category.assoc l j f))) (by
        apply Iso.ext
        simpa only [restrictionCompIso, Iso.app_hom, Iso.app_inv, Iso.trans_hom,
          Iso.symm_hom, NatTrans.comp_app, isoWhiskerRight_hom, whiskerRight_app,
          isoWhiskerLeft_hom, whiskerLeft_app, Functor.mapIso_hom, Category.assoc]
          using congrArg Iso.hom (restrictionIso_comp f j l))
  simpa only [pullbackIso, Iso.trans_assoc] using h

end KltDP.Geometry.SchemeKaehlerOpenRestriction
