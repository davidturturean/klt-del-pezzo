import KltDP.Geometry.SchemeModulePullbackCoherence

/-!
# Refinement of the original scheme-module pullback square

The comparison uses the already defined pullback-composition isomorphisms
and equality transport along the actual square of scheme morphisms.
Its refinement law is proved from their accepted associativity and
equality compatibility. The morphism-word proof is factored before
instantiating actual sheaf pullbacks.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.SchemeModulePullbackSquareCoherence

attribute [local instance] Types.instFunLike Types.instConcreteCategory

private theorem square_word {D : Type*} [Category D]
    {A B C E F G H L N P : D}
    (a : A ≅ B) (e : B ≅ C) (b : P ≅ C) (cj : P ≅ H) (dj : H ≅ G)
    (bk : B ≅ L) (bj : C ≅ N) (ck : A ≅ E) (dk : E ≅ F)
    (ak : F ≅ L) (aj : G ≅ N) (eh : L ≅ N) (r : F ≅ G)
    (ha : a.hom ≫ bk.hom = ck.hom ≫ dk.hom ≫ ak.hom)
    (hb : b.hom ≫ bj.hom = cj.hom ≫ dj.hom ≫ aj.hom)
    (he : e.hom ≫ bj.hom = bk.hom ≫ eh.hom)
    (hr : r.hom = ak.hom ≫ eh.hom ≫ aj.inv) :
    a.hom ≫ e.hom ≫ b.inv ≫ cj.hom = ck.hom ≫ dk.hom ≫ r.hom ≫ dj.inv := by
  have hbinv : b.inv ≫ cj.hom ≫ dj.hom = bj.hom ≫ aj.inv := by
    apply (cancel_mono aj.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← hb, Iso.inv_hom_id_assoc]
  apply (cancel_mono dj.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  calc
    _ = a.hom ≫ e.hom ≫ bj.hom ≫ aj.inv := by rw [hbinv]
    _ = a.hom ≫ bk.hom ≫ eh.hom ≫ aj.inv := by
      rw [← Category.assoc e.hom bj.hom, he, Category.assoc]
    _ = ck.hom ≫ dk.hom ≫ ak.hom ≫ eh.hom ≫ aj.inv := by
      rw [← Category.assoc a.hom bk.hom, ha]
      simp only [Category.assoc]
    _ = ck.hom ≫ dk.hom ≫ r.hom := by rw [hr]

/-- Normalize functor mapping before any scheme sheaf is substituted. -/
private theorem mapped_square_word {C D : Type*} [Category C] [Category D]
    (Q : C ⥤ D) {A B C' P : C} {E F G H L N : D}
    (a : A ≅ B) (e : B ≅ C') (b : P ≅ C')
    (cj : Q.obj P ≅ H) (dj : H ≅ G)
    (bk : Q.obj B ≅ L) (bj : Q.obj C' ≅ N)
    (ck : Q.obj A ≅ E) (dk : E ≅ F)
    (ak : F ≅ L) (aj : G ≅ N) (eh : L ≅ N) (r : F ≅ G)
    (ha : Q.map a.hom ≫ bk.hom = ck.hom ≫ dk.hom ≫ ak.hom)
    (hb : Q.map b.hom ≫ bj.hom = cj.hom ≫ dj.hom ≫ aj.hom)
    (he : Q.map e.hom ≫ bj.hom = bk.hom ≫ eh.hom)
    (hr : r.hom = ak.hom ≫ eh.hom ≫ aj.inv) :
    Q.map (a ≪≫ e ≪≫ b.symm).hom ≫ cj.hom =
      ck.hom ≫ (dk ≪≫ r ≪≫ dj.symm).hom := by
  have hw := square_word (Q.mapIso a) (Q.mapIso e) (Q.mapIso b)
    cj dj bk bj ck dk ak aj eh r ha hb he hr
  simpa only [CategoryTheory.Functor.mapIso_hom, CategoryTheory.Functor.mapIso_inv,
    CategoryTheory.Functor.map_comp, Iso.trans_hom, Iso.symm_hom, Category.assoc] using hw

/-- Equality transport is functorial before any concrete pullback is substituted. -/
private theorem equality_word {C D : Type*} [Category C] [Category D] {A : Type*}
    (F : A → C ⥤ D) (M : C) {a b c d : A}
    (h₁ : a = b) (h₂ : b = c) (h₃ : d = c) :
    (eqToIso (congrArg F (h₁.trans (h₂.trans h₃.symm)))).hom.app M =
      (eqToIso (congrArg (fun z => (F z).obj M) h₁)).hom ≫
        (eqToIso (congrArg F h₂)).hom.app M ≫
          (eqToIso (congrArg (fun z => (F z).obj M) h₃)).inv := by
  subst b
  subst c
  subst d
  simp only [eqToIso_refl, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, Category.id_comp]

/-- Equality transport for a single composite map, before a scheme square is substituted. -/
private theorem pullback_comparison_eq {S₀ Y₀ T₀ : Scheme.{u}}
    (a b : S₀ ⟶ Y₀) (h : a = b) (q : T₀ ⟶ S₀) (M : Y₀.Modules) :
    (schemeModulePullback q).map
        ((eqToIso (congrArg schemeModulePullback h)).hom.app M) ≫
      (schemeModulePullbackCompIso q b).hom.app M =
    (schemeModulePullbackCompIso q a).hom.app M ≫
      (eqToIso (congrArg schemeModulePullback (congrArg (fun z => q ≫ z) h))).hom.app M := by
  subst b
  simp only [eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

variable {X V Y S T : Scheme.{u}}
  (f : X ⟶ Y) (g : V ⟶ Y) (j : S ⟶ X) (k : S ⟶ V)
  (h : k ≫ g = j ≫ f) (M : Y.Modules)

/-- The actual square comparison, assembled from the original composition isomorphisms. -/
def squareIso :
    (schemeModulePullback k).obj ((schemeModulePullback g).obj M) ≅
      (schemeModulePullback j).obj ((schemeModulePullback f).obj M) :=
  (schemeModulePullbackCompIso k g).app M ≪≫
    (eqToIso (congrArg schemeModulePullback h)).app M ≪≫
      ((schemeModulePullbackCompIso j f).app M).symm

set_option maxHeartbeats 800000 in
/-- Infer this equality specialization directly, avoiding a duplicate elaboration of its
concrete pullback objects. The scoped allowance addresses the measured kernel timeout
in this declaration at the default budget. -/
private def refined_equality_hom {X V Y S T : Scheme.{u}}
    (f : X ⟶ Y) (g : V ⟶ Y) (j : S ⟶ X) (k : S ⟶ V)
    (h : k ≫ g = j ≫ f) (M : Y.Modules) (q : T ⟶ S) :=
  equality_word schemeModulePullback M
    (Category.assoc q k g) (congrArg (fun z => q ≫ z) h) (Category.assoc q j f)

set_option maxHeartbeats 800000 in
/-- Refining an actual scheme square commutes with the original pullback comparisons. -/
theorem squareIso_refinement (q : T ⟶ S) :
    (schemeModulePullback q).map (squareIso f g j k h M).hom ≫
        (schemeModulePullbackCompIso q j).hom.app ((schemeModulePullback f).obj M) =
      (schemeModulePullbackCompIso q k).hom.app ((schemeModulePullback g).obj M) ≫
        (squareIso f g (q ≫ j) (q ≫ k)
          ((Category.assoc q k g).trans
            ((congrArg (fun a => q ≫ a) h).trans (Category.assoc q j f).symm)) M).hom := by
  exact mapped_square_word (schemeModulePullback q)
    ((schemeModulePullbackCompIso k g).app M)
    ((eqToIso (congrArg schemeModulePullback h)).app M)
    ((schemeModulePullbackCompIso j f).app M)
    ((schemeModulePullbackCompIso q j).app ((schemeModulePullback f).obj M))
    ((schemeModulePullbackCompIso (q ≫ j) f).app M)
    ((schemeModulePullbackCompIso q (k ≫ g)).app M)
    ((schemeModulePullbackCompIso q (j ≫ f)).app M)
    ((schemeModulePullbackCompIso q k).app ((schemeModulePullback g).obj M))
    ((schemeModulePullbackCompIso (q ≫ k) g).app M)
    (eqToIso (congrArg (fun z => (schemeModulePullback z).obj M) (Category.assoc q k g)))
    (eqToIso (congrArg (fun z => (schemeModulePullback z).obj M) (Category.assoc q j f)))
    ((eqToIso (congrArg schemeModulePullback (congrArg (fun z => q ≫ z) h))).app M)
    ((eqToIso (congrArg schemeModulePullback
      ((Category.assoc q k g).trans
        ((congrArg (fun z => q ≫ z) h).trans (Category.assoc q j f).symm)))).app M)
    (schemeModulePullbackCompIso_assoc q k g M)
    (schemeModulePullbackCompIso_assoc q j f M)
    (pullback_comparison_eq (k ≫ g) (j ≫ f) h q M)
    (refined_equality_hom f g j k h M q)

end KltDP.Geometry.SchemeModulePullbackSquareCoherence
