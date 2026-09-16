import KltDP.Geometry.SchemeModulePullbackSquareCoherence
import KltDP.Geometry.SchemeKernelOpenPullback

/-!
# Original equation maps through refined pullback squares

The already normalized frame pullback commutes with refinement on either
side of the original scheme square. Equality transport records only
actual equalities of scheme morphisms. These laws combine the ambient
kernel equation refinement with the original global conormal chart.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.SchemeModulePullbackSquareFrames

open SchemeModulePullbackSquareCoherence

variable {X V Y S T : Scheme.{u}}
  (f : X ⟶ Y) (g : V ⟶ Y) (j : S ⟶ X) (k : S ⟶ V)
  (h : k ≫ g = j ≫ f) (M : Y.Modules)
  (s : _root_.SheafOfModules.unit V.ringCatSheaf ⟶ (schemeModulePullback g).obj M)

/-- Further actual pullback preserves a map normalized by the original structure-module unit. -/
theorem frame_refinement (q : T ⟶ S) :
    schemeModulePullbackFrame q
        (schemeModulePullbackFrame k s ≫ (squareIso f g j k h M).hom) ≫
        (schemeModulePullbackCompIso q j).hom.app ((schemeModulePullback f).obj M) =
      schemeModulePullbackFrame (q ≫ k) s ≫
        (squareIso f g (q ≫ j) (q ≫ k)
          ((Category.assoc q k g).trans
            ((congrArg (fun a => q ≫ a) h).trans (Category.assoc q j f).symm)) M).hom := by
  rw [schemeModulePullbackFrame_postcomp, Category.assoc, squareIso_refinement]
  rw [← Category.assoc, schemeModulePullbackFrame_comp]

/-- Actual equality of the two chart maps preserves the same normalized square map. -/
theorem frame_congr {j' : S ⟶ X} {k' : S ⟶ V}
    (ej : j = j') (ek : k = k') (h' : k' ≫ g = j' ≫ f) :
    (schemeModulePullbackFrame k s ≫ (squareIso f g j k h M).hom) ≫
        (eqToIso (congrArg schemeModulePullback ej)).hom.app
          ((schemeModulePullback f).obj M) =
      schemeModulePullbackFrame k' s ≫ (squareIso f g j' k' h' M).hom := by
  subst j'
  subst k'
  simp only [eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.comp_id]

/-- Refining the ambient equation first or refining its actual pullback square gives the same map. -/
theorem frame_ambient_refinement (a : T ⟶ V) (l : T ⟶ Y) (ea : a ≫ g = l)
    (q : S ⟶ T) (hq : q ≫ l = j ≫ f) :
    schemeModulePullbackFrame q
        (schemeModulePullbackFrame a s ≫
          (schemeModulePullbackCompIso a g).hom.app M ≫
          (eqToIso (congrArg schemeModulePullback ea)).hom.app M) ≫
        (squareIso f l j q hq M).hom =
      schemeModulePullbackFrame (q ≫ a) s ≫
        (squareIso f g j (q ≫ a)
          ((Category.assoc q a g).trans ((congrArg (fun z => q ≫ z) ea).trans hq)) M).hom := by
  subst l
  simp only [eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.comp_id]
  have ha := schemeModulePullbackCompIso_assoc q a g M
  have ht :
      (eqToIso (congrArg (fun z => (schemeModulePullback z).obj M)
        (Category.assoc q a g))).hom ≫
      (eqToIso (congrArg schemeModulePullback hq)).hom.app M =
      (eqToIso (congrArg schemeModulePullback ((Category.assoc q a g).trans hq))).hom.app M := by
    simp only [eqToIso.hom, eqToHom_app, eqToHom_trans]
  simp only [squareIso, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
    schemeModulePullbackFrame_postcomp, Category.assoc]
  rw [← Category.assoc
      ((schemeModulePullback q).map ((schemeModulePullbackCompIso a g).hom.app M))
      ((schemeModulePullbackCompIso q (a ≫ g)).hom.app M), ha]
  simp only [Category.assoc]
  rw [← Category.assoc (schemeModulePullbackFrame q (schemeModulePullbackFrame a s))
      ((schemeModulePullbackCompIso q a).hom.app ((schemeModulePullback g).obj M)),
    schemeModulePullbackFrame_comp]
  rw [← Category.assoc
      (eqToIso (congrArg (fun z => (schemeModulePullback z).obj M)
        (Category.assoc q a g))).hom
      ((eqToIso (congrArg schemeModulePullback hq)).hom.app M), ht]

end KltDP.Geometry.SchemeModulePullbackSquareFrames
