import KltDP.Geometry.SchemeExteriorPowerOpenRestrictionIso
import KltDP.Geometry.SchemeKaehlerExteriorPullbackMap

/-!
# The actual intrinsic exterior differential map on an open immersion

Combine the original exterior restriction comparison with the original
Kähler restriction isomorphism. Its adjunct preserves arbitrary wedges of
original differential-sheaf sections. This identifies its pullback form
with the already constructed actual exterior differential pullback map.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.SchemeKaehlerExteriorOpenRestriction

open SchemeKaehlerSheaf SchemeModuleRestriction

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance sectionCommRing (Z : Scheme.{u}) (U : Z.Opensᵒᵖ) :
    CommRing (Z.ringCatSheaf.val.obj U) :=
  inferInstanceAs (CommRing (Z.presheaf.obj U))

local instance presheafSectionCommRing (Z : Scheme.{u}) (U : Z.Opensᵒᵖ) :
    CommRing ((Z.presheaf ⋙ forget₂ CommRingCat RingCat).obj U) :=
  inferInstanceAs (CommRing (Z.presheaf.obj U))

private theorem homEquiv_leftAdjointUniq_comp
    {C D : Type*} [Category C] [Category D]
    {F F' : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G) (b : F' ⊣ G)
    (M : C) (N : D) (t : F'.obj M ⟶ N) :
    a.homEquiv M N ((Adjunction.leftAdjointUniq a b).hom.app M ≫ t) =
      b.homEquiv M N t := by
  rw [Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_leftAdjointUniq_hom_app, Adjunction.homEquiv_unit]

private theorem restrictionAdjunction_homEquiv_app
    {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (M : X.Modules) (N : Y.Modules) (t : (restriction j).obj M ⟶ N)
    (U : X.Opens) (s : M.val.obj (op U)) :
    ((restrictionAdjunction j).homEquiv M N t).val.app (op U) s =
      t.val.app (op (j ⁻¹ᵁ U))
        (M.val.map (homOfLE (Set.image_preimage_subset j.base (U : Set X))).op s) := by
  rw [Adjunction.homEquiv_unit]
  rfl

variable {k : Type u} [CommRing k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (j : Y ⟶ X) [IsOpenImmersion j] (n : ℕ)

/-- Restriction of the original intrinsic exterior is its original intrinsic exterior on the open. -/
def restrictionIso :
    (restriction j).obj (SchemeExteriorPower.sheaf (baseRingSheaf f) n) ≅
      SchemeExteriorPower.sheaf (baseRingSheaf (j ≫ f)) n :=
  SchemeExteriorPowerOpenRestriction.restrictionIso j (baseRingSheaf f) n ≪≫
    SchemeExteriorPower.mapIso (SchemeKaehlerOpenRestriction.restrictionIso f j) n

/-- The comparison retains the original wedge and the original Kähler comparison on each factor. -/
theorem restrictionIso_hom_wedge (U : Y.Opens)
    (v : Fin n → ((restriction j).obj (baseRingSheaf f)).val.obj (op U)) :
    (restrictionIso f j n).hom.val.app (op U)
        (SchemeExteriorPower.wedge (baseRingSheaf f) n (j ''ᵁ U) v) =
      SchemeExteriorPower.wedge (baseRingSheaf (j ≫ f)) n U
        (fun i => (SchemeKaehlerOpenRestriction.restrictionIso f j).hom.val.app (op U) (v i)) :=
  (congrArg
    ((SchemeExteriorPower.map (SchemeKaehlerOpenRestriction.restrictionIso f j).hom n).val.app
      (op U))
    (SchemeExteriorPowerOpenRestriction.restrictionIso_hom_wedge j (baseRingSheaf f) n U v)).trans
      (SchemeExteriorPower.map_wedge (SchemeKaehlerOpenRestriction.restrictionIso f j).hom n U v)

def adjointComparison : SchemeExteriorPower.sheaf (baseRingSheaf f) n ⟶
    (schemeModulePushforward j).obj (SchemeExteriorPower.sheaf (baseRingSheaf (j ≫ f)) n) :=
  (restrictionAdjunction j).homEquiv _ _ (restrictionIso f j n).hom

/-- The original restriction adjunct preserves arbitrary wedges of actual sheaf sections. -/
theorem adjointComparison_wedge (U : X.Opens)
    (v : Fin n → (baseRingSheaf f).val.obj (op U)) :
    (adjointComparison f j n).val.app (op U)
        (SchemeExteriorPower.wedge (baseRingSheaf f) n U v) =
      SchemeExteriorPower.wedge (baseRingSheaf (j ≫ f)) n (j ⁻¹ᵁ U)
        (fun i => (SchemeKaehlerOpenRestriction.adjointComparison f j).val.app (op U) (v i)) := by
  rw [adjointComparison, restrictionAdjunction_homEquiv_app]
  let i : j ''ᵁ (j ⁻¹ᵁ U) ⟶ U :=
    homOfLE (Set.image_preimage_subset j.base (U : Set X))
  refine (congrArg ((restrictionIso f j n).hom.val.app (op (j ⁻¹ᵁ U)))
    (SchemeExteriorPower.wedge_restrict (baseRingSheaf f) n i.le v)).trans ?_
  refine (restrictionIso_hom_wedge f j n (j ⁻¹ᵁ U)
    (fun r => (baseRingSheaf f).val.map i.op (v r))).trans ?_
  apply congrArg (SchemeExteriorPower.wedge (baseRingSheaf (j ≫ f)) n (j ⁻¹ᵁ U))
  funext r
  exact (restrictionAdjunction_homEquiv_app j (baseRingSheaf f) (baseRingSheaf (j ≫ f))
    (SchemeKaehlerOpenRestriction.restrictionIso f j).hom U (v r)).symm

private theorem kaehler_adjoint_eq :
    SchemeKaehlerPullbackMap.adjointMap f j =
      SchemeKaehlerOpenRestriction.adjointComparison f j := by
  have h := congrArg ((schemeModulePullbackPushforwardAdjunction j).homEquiv _ _)
    (SchemeKaehlerPullbackMap.map_eq_pullbackIso f j)
  exact (SchemeKaehlerPullbackMap.map_homEquiv f j).symm.trans
    (h.trans (SchemeKaehlerOpenRestriction.pullbackIso_homEquiv f j))

/-- Equality with the actual previously constructed exterior adjunct, on all sections. -/
theorem adjointComparison_eq :
    adjointComparison f j n = SchemeKaehlerExteriorPullbackMap.adjointMap f j n := by
  apply (SchemeExteriorPower.homEquiv (baseRingSheaf f) n _).injective
  apply _root_.PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.exteriorPower.hom_ext
  apply ModuleCat.AlternatingMap.ext
  intro v
  change (adjointComparison f j n).val.app U
      (SchemeExteriorPower.wedge (baseRingSheaf f) n U.unop v) =
    (SchemeKaehlerExteriorPullbackMap.adjointMap f j n).val.app U
      (SchemeExteriorPower.wedge (baseRingSheaf f) n U.unop v)
  rw [adjointComparison_wedge, SchemeKaehlerExteriorPullbackMap.adjointMap_wedge,
    kaehler_adjoint_eq]

/-- The comparison on the actual scheme pullback, through the original adjunction isomorphism. -/
def pullbackIso :
    (schemeModulePullback j).obj (SchemeExteriorPower.sheaf (baseRingSheaf f) n) ≅
      SchemeExteriorPower.sheaf (baseRingSheaf (j ≫ f)) n :=
  ((restrictionIsoPullback j).symm.app (SchemeExteriorPower.sheaf (baseRingSheaf f) n)) ≪≫
    restrictionIso f j n

theorem pullbackIso_homEquiv :
    (schemeModulePullbackPushforwardAdjunction j).homEquiv _ _
      (pullbackIso f j n).hom = adjointComparison f j n := by
  change (schemeModulePullbackPushforwardAdjunction j).homEquiv _ _
    ((Adjunction.leftAdjointUniq (schemeModulePullbackPushforwardAdjunction j)
      (restrictionAdjunction j)).hom.app (SchemeExteriorPower.sheaf (baseRingSheaf f) n) ≫
        (restrictionIso f j n).hom) = _
  exact homEquiv_leftAdjointUniq_comp _ _ _ _ _

/-- The forward isomorphism is the original actual exterior differential pullback map. -/
theorem pullbackIso_hom :
    (pullbackIso f j n).hom = SchemeKaehlerExteriorPullbackMap.map f j n := by
  apply ((schemeModulePullbackPushforwardAdjunction j).homEquiv _ _).injective
  rw [pullbackIso_homEquiv, SchemeKaehlerExteriorPullbackMap.map_homEquiv,
    adjointComparison_eq]

theorem map_isIso : IsIso (SchemeKaehlerExteriorPullbackMap.map f j n) := by
  rw [← pullbackIso_hom]
  infer_instance

end KltDP.Geometry.SchemeKaehlerExteriorOpenRestriction
