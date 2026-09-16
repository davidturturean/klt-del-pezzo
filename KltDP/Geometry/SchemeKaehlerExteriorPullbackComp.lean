import KltDP.Geometry.SchemeKaehlerExteriorPullbackMap
import KltDP.Geometry.SchemeKaehlerPullbackMapComp

/-!
# Composition of the original intrinsic exterior differential maps

The whole original Kähler composition identity determines the composition
on arbitrary exterior wedges. The original exterior universal property and
the original pullback-composition adjunction give equality of the entire
intrinsic exterior differential maps, with the original structure-map
association retained explicitly.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace KltDP.Geometry.SchemeKaehlerExteriorPullbackMap

open SchemeKaehlerSheaf

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance sectionCommRing (Z : Scheme.{u}) (U : Z.Opensᵒᵖ) :
    CommRing (Z.ringCatSheaf.val.obj U) :=
  inferInstanceAs (CommRing (Z.presheaf.obj U))

local instance presheafSectionCommRing (Z : Scheme.{u}) (U : Z.Opensᵒᵖ) :
    CommRing ((Z.presheaf ⋙ forget₂ CommRingCat RingCat).obj U) :=
  inferInstanceAs (CommRing (Z.presheaf.obj U))

variable {k : Type u} [CommRing k] {X Y Z : Scheme.{u}}

/-- The actual exterior equality transport is the exterior of the actual module equality transport. -/
theorem exterior_eqToIso_hom {f g : X ⟶ Spec (CommRingCat.of k)} (h : f = g) (n : ℕ) :
    (eqToIso (congrArg (fun t => SchemeExteriorPower.sheaf (baseRingSheaf t) n) h)).hom =
      SchemeExteriorPower.map (eqToIso (congrArg baseRingSheaf h)).hom n := by
  subst g
  simp only [eqToIso_refl, Iso.refl_hom, SchemeExteriorPower.map_id]

variable (f : X ⟶ Spec (CommRingCat.of k)) (j : Y ⟶ X) (l : Z ⟶ Y) (n : ℕ)

/-- Composition on an arbitrary wedge follows from the original whole Kähler map identity. -/
theorem adjointMap_comp_wedge (U : X.Opens)
    (v : Fin n → (baseRingSheaf f).val.obj (op U)) :
    (adjointMap f (l ≫ j) n ≫ (schemeModulePushforward (l ≫ j)).map
        (eqToIso (congrArg (fun t => SchemeExteriorPower.sheaf (baseRingSheaf t) n)
          (Category.assoc l j f))).hom).val.app (op U)
            (SchemeExteriorPower.wedge (baseRingSheaf f) n U v) =
      (adjointMap f j n ≫ (schemeModulePushforward j).map
        (adjointMap (j ≫ f) l n)).val.app (op U)
          (SchemeExteriorPower.wedge (baseRingSheaf f) n U v) := by
  change (eqToIso (congrArg (fun t => SchemeExteriorPower.sheaf (baseRingSheaf t) n)
      (Category.assoc l j f))).hom.val.app (op ((l ≫ j) ⁻¹ᵁ U))
      ((adjointMap f (l ≫ j) n).val.app (op U)
        (SchemeExteriorPower.wedge (baseRingSheaf f) n U v)) =
    (adjointMap (j ≫ f) l n).val.app (op (j ⁻¹ᵁ U))
      ((adjointMap f j n).val.app (op U)
        (SchemeExteriorPower.wedge (baseRingSheaf f) n U v))
  rw [adjointMap_wedge, exterior_eqToIso_hom (Category.assoc l j f), SchemeExteriorPower.map_wedge,
    adjointMap_wedge, adjointMap_wedge]
  apply congrArg (SchemeExteriorPower.wedge (baseRingSheaf (l ≫ (j ≫ f))) n (l ⁻¹ᵁ (j ⁻¹ᵁ U)))
  funext i
  exact congrArg (fun a => a.val.app (op U) (v i))
    (SchemeKaehlerPullbackMap.adjointMap_comp f j l)

/-- Equality of the original entire exterior adjuncts, not only coordinate values. -/
theorem adjointMap_comp :
    adjointMap f (l ≫ j) n ≫ (schemeModulePushforward (l ≫ j)).map
        (eqToIso (congrArg (fun t => SchemeExteriorPower.sheaf (baseRingSheaf t) n)
          (Category.assoc l j f))).hom =
      adjointMap f j n ≫ (schemeModulePushforward j).map (adjointMap (j ≫ f) l n) := by
  apply (SchemeExteriorPower.homEquiv (baseRingSheaf f) n _).injective
  apply _root_.PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.exteriorPower.hom_ext
  apply ModuleCat.AlternatingMap.ext
  intro v
  exact adjointMap_comp_wedge f j l n U.unop v

/-- The original intrinsic exterior differential maps compose through the actual pullback comparison. -/
theorem map_comp :
    (schemeModulePullbackCompIso l j).hom.app (SchemeExteriorPower.sheaf (baseRingSheaf f) n) ≫
        map f (l ≫ j) n ≫
          (eqToIso (congrArg (fun t => SchemeExteriorPower.sheaf (baseRingSheaf t) n)
            (Category.assoc l j f))).hom =
      (schemeModulePullback l).map (map f j n) ≫ map (j ≫ f) l n := by
  apply ((schemeModulePullbackPushforwardAdjunction l).homEquiv _ _).injective
  apply ((schemeModulePullbackPushforwardAdjunction j).homEquiv _ _).injective
  rw [schemeModulePullbackCompIso_homEquiv, Adjunction.homEquiv_naturality_left,
    Adjunction.homEquiv_naturality_right, map_homEquiv,
    Adjunction.homEquiv_naturality_right, map_homEquiv, map_homEquiv]
  exact adjointMap_comp f j l n

end KltDP.Geometry.SchemeKaehlerExteriorPullbackMap
