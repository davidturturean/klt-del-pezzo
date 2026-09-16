import KltDP.Geometry.SchemeKaehlerPullbackMap
import KltDP.Geometry.SchemeModulePullbackCoherence

/-!
# Composition of the original arbitrary-morphism Kähler maps

The original section-map composition law determines the composite of the
actual pushed-forward derivations. The original pullback-composition
adjunction transports that identity to the actual pullback maps. No open
immersion or compatibility hypothesis is added to either morphism.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.SchemeKaehlerPullbackMap

open SchemeKaehlerSheaf

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [CommRing k] {X Y Z : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (j : Y ⟶ X) (l : Z ⟶ Y)

/-- The original adjoint differential maps compose through the actual structure-map association. -/
theorem adjointMap_comp :
    adjointMap f (l ≫ j) ≫ (schemeModulePushforward (l ≫ j)).map
        (eqToIso (congrArg baseRingSheaf (Category.assoc l j f))).hom =
      adjointMap f j ≫ (schemeModulePushforward j).map (adjointMap (j ≫ f) l) := by
  apply SchemeKaehlerSheaf.hom_ext (scalarPresheafHom f)
  ext U s
  change (eqToIso (congrArg baseRingSheaf (Category.assoc l j f))).hom.val.app
      (op ((l ≫ j) ⁻¹ᵁ U.unop))
      ((adjointMap f (l ≫ j)).val.app U ((baseRingDerivation f).d s)) =
    (adjointMap (j ≫ f) l).val.app (op (j ⁻¹ᵁ U.unop))
      ((adjointMap f j).val.app U ((baseRingDerivation f).d s))
  rw [adjointMap_d,
    SchemeKaehlerOpenRestriction.baseRingSheaf_eqToIso_hom_d (Category.assoc l j f),
    adjointMap_d, adjointMap_d]
  exact congrArg (fun t => (baseRingDerivation (l ≫ (j ≫ f))).d t)
    (ConcreteCategory.congr_hom (Scheme.comp_app l j U.unop) s)

/-- The original Kähler pullback maps compose through the original pullback comparison. -/
theorem map_comp :
    (schemeModulePullbackCompIso l j).hom.app (baseRingSheaf f) ≫
        map f (l ≫ j) ≫ (eqToIso (congrArg baseRingSheaf (Category.assoc l j f))).hom =
      (schemeModulePullback l).map (map f j) ≫ map (j ≫ f) l := by
  apply ((schemeModulePullbackPushforwardAdjunction l).homEquiv _ _).injective
  apply ((schemeModulePullbackPushforwardAdjunction j).homEquiv _ _).injective
  rw [schemeModulePullbackCompIso_homEquiv, Adjunction.homEquiv_naturality_left,
    Adjunction.homEquiv_naturality_right, map_homEquiv,
    Adjunction.homEquiv_naturality_right, map_homEquiv, map_homEquiv]
  exact adjointMap_comp f j l

end KltDP.Geometry.SchemeKaehlerPullbackMap
