import KltDP.Geometry.SchemeKernelOpenPullback

/-!
# Transport of a normalized original kernel frame through an ambient square

The existing pullback composition and equality comparisons move a frame on an
original ambient open to the literal iterated pullback on another ambient scheme.
Their proved unit coherence preserves the original inclusion and the pulled
coefficient. No new pullback, tensor, or gluing construction is introduced.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

/-- The original pullback composition comparison preserves the original kernel inclusion. -/
theorem schemeKernelPullbackCompIso_inclusion {A V Y U : Scheme.{u}}
    (f : A ⟶ Y) (i : V ⟶ Y) (g : U ⟶ V) :
    (schemeModulePullbackCompIso g i).hom.app (schemeKernelIdeal f) ≫
        pulledKernelInclusion f (g ≫ i) =
      (schemeModulePullback g).map (pulledKernelInclusion f i) ≫
        (schemeModulePullbackUnitIso g).hom := by
  simp only [pulledKernelInclusion, Category.assoc]
  rw [← Category.assoc ((schemeModulePullbackCompIso g i).hom.app (schemeKernelIdeal f)),
    ← (schemeModulePullbackCompIso g i).hom.naturality (schemeKernelIdealι f),
    Category.assoc, schemeModulePullbackCompIso_unit]
  simp only [Functor.map_comp, Functor.comp_map, Category.assoc]

/-- The existing frame, pullback composition and equality isomorphisms along the proved square. -/
def schemeKernelFrameOnSquare {A V Y U X : Scheme.{u}}
    (f : A ⟶ Y) (i : V ⟶ Y) (g : U ⟶ V) (j : U ⟶ X) (p : X ⟶ Y)
    (h : g ≫ i = j ≫ p)
    (e : _root_.SheafOfModules.unit V.ringCatSheaf ≅
      (schemeModulePullback i).obj (schemeKernelIdeal f)) :
    _root_.SheafOfModules.unit U.ringCatSheaf ≅
      (schemeModulePullback j).obj ((schemeModulePullback p).obj (schemeKernelIdeal f)) :=
  (schemeModulePullbackUnitIso g).symm ≪≫
    (schemeModulePullback g).mapIso e ≪≫
    (schemeModulePullbackCompIso g i).app (schemeKernelIdeal f) ≪≫
    (eqToIso (congrArg schemeModulePullback h)).app (schemeKernelIdeal f) ≪≫
    ((schemeModulePullbackCompIso j p).app (schemeKernelIdeal f)).symm

/-- The transported frame preserves the literal iterated pullback of the original inclusion. -/
theorem schemeKernelFrameOnSquare_inclusion {A V Y U X : Scheme.{u}}
    (f : A ⟶ Y) (i : V ⟶ Y) (g : U ⟶ V) (j : U ⟶ X) (p : X ⟶ Y)
    (h : g ≫ i = j ≫ p)
    (e : _root_.SheafOfModules.unit V.ringCatSheaf ≅
      (schemeModulePullback i).obj (schemeKernelIdeal f))
    (d : Γ(V, ⊤)) (he : e.hom ≫ pulledKernelInclusion f i = schemeScalarEnd d) :
    (schemeKernelFrameOnSquare f i g j p h e).hom ≫
      (schemeModulePullback j).map (pulledKernelInclusion f p) ≫
      (schemeModulePullbackUnitIso j).hom = schemeScalarEnd (g.appTop d) := by
  simp only [schemeKernelFrameOnSquare, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.app_hom, Category.assoc]
  rw [← schemeKernelPullbackCompIso_inclusion f p j]
  simp only [Iso.app_inv, Iso.inv_hom_id_app_assoc]
  rw [pulledKernelInclusion_congr f h, schemeKernelPullbackCompIso_inclusion f i g,
    ← Functor.map_comp_assoc, he, ← Category.assoc,
    schemeModulePullbackUnitIso_inv_scalar, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

end KltDP.Geometry
