import KltDP.Geometry.SchemeModulePullbackSquareCoherence

/-!
# Paste the original ambient quotient-chart pullback squares

This is the actual square-pasting step used by ambient adjunction charts.
It uses only the existing pullback composition, its proved associativity,
and equality transport along the original commuting scheme maps.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.GluedAdjunctionAmbientSquarePasting

open SchemeModulePullbackSquareCoherence

private theorem square_cancel {C : Type*} [Category C] {A B D E F : C}
    (a : A ≅ B) (e : B ≅ D) (b : E ≅ D) (v : D ⟶ F) :
    (a ≪≫ e ≪≫ b.symm).hom ≫ b.hom ≫ v = a.hom ≫ e.hom ≫ v := by
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]

private theorem square_congr {X V Y S : Scheme.{u}}
    (f : X ⟶ Y) (g : V ⟶ Y) (j : S ⟶ X) (k : S ⟶ V)
    (h : k ≫ g = j ≫ f) (M : Y.Modules)
    {j' : S ⟶ X} {k' : S ⟶ V} (ej : j = j') (ek : k = k')
    (h' : k' ≫ g = j' ≫ f) :
    (squareIso f g j k h M).hom ≫
        (eqToIso (congrArg schemeModulePullback ej)).hom.app ((schemeModulePullback f).obj M) =
      (eqToIso (congrArg schemeModulePullback ek)).hom.app ((schemeModulePullback g).obj M) ≫
        (squareIso f g j' k' h' M).hom := by
  subst j'
  subst k'
  simp only [eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.comp_id, Category.id_comp]

/-- The whole ambient pullback map satisfies the existing frame-pasting computation. -/
private theorem ambient_refinement {X V Y S T : Scheme.{u}}
    (f : X ⟶ Y) (g : V ⟶ Y) (j : S ⟶ X) (M : Y.Modules)
    (a : T ⟶ V) (l : T ⟶ Y) (ea : a ≫ g = l)
    (q : S ⟶ T) (hq : q ≫ l = j ≫ f) :
    (schemeModulePullback q).map
        ((schemeModulePullbackCompIso a g).hom.app M ≫
          (eqToIso (congrArg schemeModulePullback ea)).hom.app M) ≫
        (squareIso f l j q hq M).hom =
      (schemeModulePullbackCompIso q a).hom.app ((schemeModulePullback g).obj M) ≫
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
  simp only [squareIso, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Category.assoc]
  rw [← Category.assoc
      ((schemeModulePullback q).map ((schemeModulePullbackCompIso a g).hom.app M))
      ((schemeModulePullbackCompIso q (a ≫ g)).hom.app M), ha]
  simp only [Category.assoc]
  rw [← Category.assoc
      (eqToIso (congrArg (fun z => (schemeModulePullback z).obj M)
        (Category.assoc q a g))).hom
      ((eqToIso (congrArg schemeModulePullback hq)).hom.app M), ht]

/-- Paste the three arrow equalities before any scheme pullback is instantiated. -/
private theorem pasting_word {C : Type*} [Category C] {A B D E F H K L : C}
    (u : A ⟶ B) (c : B ⟶ D) (d : D ⟶ L)
    (a : A ≅ E) (t : E ≅ F) (b : H ≅ F)
    (s : E ⟶ D) (v : F ⟶ L) (w : H ⟶ K) (z : K ⟶ L)
    (hRef : u ≫ c = a.hom ≫ s) (hCong : s ≫ d = t.hom ≫ v)
    (hAmbient : w ≫ z = b.hom ≫ v) :
    u ≫ c ≫ d = (a ≪≫ t ≪≫ b.symm).hom ≫ w ≫ z := by
  rw [hAmbient, square_cancel a t b v]
  calc
    _ = (u ≫ c) ≫ d := (Category.assoc u c d).symm
    _ = (a.hom ≫ s) ≫ d := congrArg (fun q => q ≫ d) hRef
    _ = a.hom ≫ (s ≫ d) := Category.assoc _ _ _
    _ = _ := congrArg (fun q => a.hom ≫ q) hCong

private def square_pasting_proof {X Y U V Q P : Scheme.{u}}
    (f : X ⟶ Y) (g : U ⟶ Y) (g' : V ⟶ Y)
    (j : Q ⟶ X) (j' : P ⟶ X) (k : Q ⟶ U) (k' : P ⟶ V)
    (b : P ⟶ Q) (c : V ⟶ U)
    (hU : k ≫ g = j ≫ f) (hV : k' ≫ g' = j' ≫ f)
    (hb : b ≫ j = j') (hc : c ≫ g = g') (hr : b ≫ k = k' ≫ c) (M : Y.Modules) :=
  let hCombined := (Category.assoc k' c g).trans
    ((congrArg (fun z => k' ≫ z) hc).trans hV)
  let hRefined := (Category.assoc b k g).trans
    ((congrArg (fun z => b ≫ z) hU).trans (Category.assoc b j f).symm)
  pasting_word (C := P.Modules)
    ((schemeModulePullback b).map (squareIso f g j k hU M).hom)
    ((schemeModulePullbackCompIso b j).hom.app ((schemeModulePullback f).obj M))
    ((eqToIso (congrArg schemeModulePullback hb)).hom.app ((schemeModulePullback f).obj M))
    ((schemeModulePullbackCompIso b k).app ((schemeModulePullback g).obj M))
    ((eqToIso (congrArg schemeModulePullback hr)).app ((schemeModulePullback g).obj M))
    ((schemeModulePullbackCompIso k' c).app ((schemeModulePullback g).obj M))
    (squareIso f g (b ≫ j) (b ≫ k) hRefined M).hom
    (squareIso f g j' (k' ≫ c) hCombined M).hom
    ((schemeModulePullback k').map
      ((schemeModulePullbackCompIso c g).hom.app M ≫
        (eqToIso (congrArg schemeModulePullback hc)).hom.app M))
    (squareIso f g' j' k' hV M).hom
    (squareIso_refinement f g j k hU M b)
    (square_congr f g (b ≫ j) (b ≫ k) hRefined M hb hr hCombined)
    (ambient_refinement f g j' M c g' hc k' hV)

/-- Refine the original global quotient square or first refine the ambient affine chart.
The two routes use the same original square comparison and actual equality transports. -/
theorem square_pasting {X Y U V Q P : Scheme.{u}}
    (f : X ⟶ Y) (g : U ⟶ Y) (g' : V ⟶ Y)
    (j : Q ⟶ X) (j' : P ⟶ X) (k : Q ⟶ U) (k' : P ⟶ V)
    (b : P ⟶ Q) (c : V ⟶ U)
    (hU : k ≫ g = j ≫ f) (hV : k' ≫ g' = j' ≫ f)
    (hb : b ≫ j = j') (hc : c ≫ g = g') (hr : b ≫ k = k' ≫ c) (M : Y.Modules) :
    (schemeModulePullback b).map (squareIso f g j k hU M).hom ≫
        (schemeModulePullbackCompIso b j).hom.app ((schemeModulePullback f).obj M) ≫
        (eqToIso (congrArg schemeModulePullback hb)).hom.app ((schemeModulePullback f).obj M) =
      (squareIso c k k' b hr ((schemeModulePullback g).obj M)).hom ≫
        (schemeModulePullback k').map
          ((schemeModulePullbackCompIso c g).hom.app M ≫
            (eqToIso (congrArg schemeModulePullback hc)).hom.app M) ≫
        (squareIso f g' j' k' hV M).hom :=
  square_pasting_proof f g g' j j' k k' b c hU hV hb hc hr M

end KltDP.Geometry.GluedAdjunctionAmbientSquarePasting
