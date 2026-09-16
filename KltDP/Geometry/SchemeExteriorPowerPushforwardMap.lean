import KltDP.Geometry.SchemeExteriorPowerMap
import KltDP.Geometry.SchemeModuleFunctorial

/-!
# Original exterior powers and original scheme pushforward

The existing scalar-restriction comparison on exterior powers defines a map
from the exterior power of the actual pushforward to the actual pushforward
of the exterior power. Original restrictions make these section maps natural.
The original sheafification universal property supplies the sheaf map, whose
value on every original wedge is retained explicitly.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.SchemeExteriorPowerPushforwardMap

open SchemeExteriorPower KltDP.Compatibility.ExteriorPowerPresheaf

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance sectionCommRing (Z : Scheme.{u}) (U : Z.Opensᵒᵖ) :
    CommRing (Z.ringCatSheaf.val.obj U) :=
  inferInstanceAs (CommRing (Z.presheaf.obj U))

local instance presheafSectionCommRing (Z : Scheme.{u}) (U : Z.Opensᵒᵖ) :
    CommRing ((Z.presheaf ⋙ forget₂ CommRingCat RingCat).obj U) :=
  inferInstanceAs (CommRing (Z.presheaf.obj U))

variable {X Y : Scheme.{u}} (j : Y ⟶ X) (N : Y.Modules) (n : ℕ)

/-- The original scalar-restriction comparison followed by the original
exterior sheafification unit on the actual inverse-image open. -/
def presheafMapApp (U : X.Opens) :
    (SchemeExteriorPower.presheaf ((schemeModulePushforward j).obj N) n).obj (op U) ⟶
      ((schemeModulePushforward j).obj (SchemeExteriorPower.sheaf N n)).val.obj (op U) :=
  fromRestrictScalars (j.app U).hom (N.val.obj (op (j ⁻¹ᵁ U))) n ≫
    (ModuleCat.restrictScalars (j.app U).hom).map
      ((SchemeExteriorPower.toSheaf N n).app (op (j ⁻¹ᵁ U)))

/-- Its action on a pure wedge is the original wedge over the target ring. -/
theorem presheafMapApp_mk (U : X.Opens)
    (v : Fin n → ((schemeModulePushforward j).obj N).val.obj (op U)) :
    presheafMapApp j N n U (ModuleCat.exteriorPower.mk v) =
      SchemeExteriorPower.wedge N n (j ⁻¹ᵁ U) v := by
  change (SchemeExteriorPower.toSheaf N n).app (op (j ⁻¹ᵁ U))
      (fromRestrictScalars (j.app U).hom (N.val.obj (op (j ⁻¹ᵁ U))) n
        (ModuleCat.exteriorPower.mk v)) = _
  rw [fromRestrictScalars_mk]
  rfl

/-- The original section comparisons commute with every original restriction. -/
def presheafMap :
    SchemeExteriorPower.presheaf ((schemeModulePushforward j).obj N) n ⟶
      ((schemeModulePushforward j).obj (SchemeExteriorPower.sheaf N n)).val where
  app U := presheafMapApp j N n U.unop
  naturality {U V} i := by
    apply ModuleCat.exteriorPower.hom_ext
    apply ModuleCat.AlternatingMap.ext
    intro v
    change presheafMapApp j N n V.unop
        ((SchemeExteriorPower.presheaf ((schemeModulePushforward j).obj N) n).map i
          (ModuleCat.exteriorPower.mk v)) =
      ((schemeModulePushforward j).obj (SchemeExteriorPower.sheaf N n)).val.map i
        (presheafMapApp j N n U.unop (ModuleCat.exteriorPower.mk v))
    refine (congrArg (presheafMapApp j N n V.unop)
      (restriction_mk X.presheaf ((schemeModulePushforward j).obj N).val n i v)).trans ?_
    rw [presheafMapApp_mk, presheafMapApp_mk]
    exact (SchemeExteriorPower.wedge_restrict N n
      (leOfHom ((Opens.map j.base).map i.unop)) v).symm

/-- The comparison of the actual exterior sheaves is induced by those
original section maps, without a frame or an isomorphism assumption. -/
def map :
    SchemeExteriorPower.sheaf ((schemeModulePushforward j).obj N) n ⟶
      (schemeModulePushforward j).obj (SchemeExteriorPower.sheaf N n) :=
  (SchemeExteriorPower.homEquiv ((schemeModulePushforward j).obj N) n
    ((schemeModulePushforward j).obj (SchemeExteriorPower.sheaf N n))).symm
      (presheafMap j N n)

theorem map_homEquiv :
    SchemeExteriorPower.homEquiv ((schemeModulePushforward j).obj N) n
        ((schemeModulePushforward j).obj (SchemeExteriorPower.sheaf N n)) (map j N n) =
      presheafMap j N n :=
  (SchemeExteriorPower.homEquiv ((schemeModulePushforward j).obj N) n
    ((schemeModulePushforward j).obj (SchemeExteriorPower.sheaf N n))).apply_symm_apply _

/-- This actual comparison sends every original pushforward wedge to the
original target-ring wedge on the actual inverse-image open. -/
theorem map_wedge (U : X.Opens)
    (v : Fin n → ((schemeModulePushforward j).obj N).val.obj (op U)) :
    (map j N n).val.app (op U)
        (SchemeExteriorPower.wedge ((schemeModulePushforward j).obj N) n U v) =
      SchemeExteriorPower.wedge N n (j ⁻¹ᵁ U) v := by
  have h := congrArg (fun a => a.app (op U) (ModuleCat.exteriorPower.mk v))
    (map_homEquiv j N n)
  exact h.trans (presheafMapApp_mk j N n U v)

end KltDP.Geometry.SchemeExteriorPowerPushforwardMap
