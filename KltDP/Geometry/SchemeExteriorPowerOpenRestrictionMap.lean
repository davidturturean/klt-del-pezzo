import KltDP.Geometry.SchemeExteriorPower
import KltDP.Geometry.ModuleOpenRestrictionTensor

/-!
# The original exterior map for actual open restriction

Use exactly the inverse section-ring isomorphism of the original open
immersion. The existing scalar-restriction exterior map is natural on the
actual image opens, and the original sheafification universal property
therefore gives a sheaf map preserving each original wedge of sections.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.SchemeExteriorPowerOpenRestriction

open SchemeModuleRestriction KltDP.Compatibility.ExteriorPowerPresheaf

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance sectionCommRing (Z : Scheme.{u}) (U : Z.Opensᵒᵖ) :
    CommRing (Z.ringCatSheaf.val.obj U) :=
  inferInstanceAs (CommRing (Z.presheaf.obj U))

local instance presheafSectionCommRing (Z : Scheme.{u}) (U : Z.Opensᵒᵖ) :
    CommRing ((Z.presheaf ⋙ forget₂ CommRingCat RingCat).obj U) :=
  inferInstanceAs (CommRing (Z.presheaf.obj U))

variable {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j] (M : X.Modules) (n : ℕ)

/-- Restrict the actual exterior presheaf by the original inverse section-ring maps. -/
abbrev restrictedPresheaf : Y.PresheafOfModules :=
  (_root_.PresheafOfModules.pushforward (restrictionRingHom j)).obj
    (SchemeExteriorPower.presheaf M n)

/-- The existing canonical exterior comparison on each original image open. -/
def presheafComparisonApp (U : Y.Opens) :
    (SchemeExteriorPower.presheaf ((restriction j).obj M) n).obj (op U) ⟶
      (restrictedPresheaf j M n).obj (op U) :=
  fromRestrictScalars (j.appIso U).inv.hom (M.val.obj (op (j ''ᵁ U))) n

theorem presheafComparisonApp_mk (U : Y.Opens)
    (v : Fin n → ((restriction j).obj M).val.obj (op U)) :
    presheafComparisonApp j M n U (ModuleCat.exteriorPower.mk v) =
      ModuleCat.exteriorPower.mk (M := M.val.obj (op (j ''ᵁ U))) v :=
  fromRestrictScalars_mk (j.appIso U).inv.hom (M.val.obj (op (j ''ᵁ U))) n v

/-- These actual scalar comparisons commute with all original restrictions. -/
def presheafComparison :
    SchemeExteriorPower.presheaf ((restriction j).obj M) n ⟶ restrictedPresheaf j M n where
  app U := presheafComparisonApp j M n U.unop
  naturality {U V} i := by
    apply ModuleCat.exteriorPower.hom_ext
    apply ModuleCat.AlternatingMap.ext
    intro v
    change presheafComparisonApp j M n V.unop
        ((SchemeExteriorPower.presheaf ((restriction j).obj M) n).map i
          (ModuleCat.exteriorPower.mk v)) =
      (restrictedPresheaf j M n).map i
        (presheafComparisonApp j M n U.unop (ModuleCat.exteriorPower.mk v))
    refine (congrArg (presheafComparisonApp j M n V.unop)
      (restriction_mk Y.presheaf ((restriction j).obj M).val n i v)).trans ?_
    rw [presheafComparisonApp_mk, presheafComparisonApp_mk]
    change ModuleCat.exteriorPower.mk (M := M.val.obj (j.opensFunctor.op.obj V))
        (fun r => M.val.map (j.opensFunctor.op.map i) (v r)) =
      (SchemeExteriorPower.presheaf M n).map (j.opensFunctor.op.map i)
        (ModuleCat.exteriorPower.mk v)
    exact (restriction_mk X.presheaf M.val n (j.opensFunctor.op.map i) v).symm

/-- Restrict the original exterior sheafification unit by the same actual functor. -/
def restrictedUnit : restrictedPresheaf j M n ⟶
    ((restriction j).obj (SchemeExteriorPower.sheaf M n)).val :=
  (_root_.PresheafOfModules.pushforward (restrictionRingHom j)).map
    (SchemeExteriorPower.toSheaf M n)

def presheafMap : SchemeExteriorPower.presheaf ((restriction j).obj M) n ⟶
    ((restriction j).obj (SchemeExteriorPower.sheaf M n)).val :=
  presheafComparison j M n ≫ restrictedUnit j M n

theorem presheafMap_mk (U : Y.Opens)
    (v : Fin n → ((restriction j).obj M).val.obj (op U)) :
    (presheafMap j M n).app (op U) (ModuleCat.exteriorPower.mk v) =
      SchemeExteriorPower.wedge M n (j ''ᵁ U) v := by
  change (SchemeExteriorPower.toSheaf M n).app (op (j ''ᵁ U))
    (presheafComparisonApp j M n U (ModuleCat.exteriorPower.mk v)) = _
  rw [presheafComparisonApp_mk]
  rfl

/-- The actual exterior map of open restriction, induced by original wedges. -/
def map : SchemeExteriorPower.sheaf ((restriction j).obj M) n ⟶
    (restriction j).obj (SchemeExteriorPower.sheaf M n) :=
  (SchemeExteriorPower.homEquiv ((restriction j).obj M) n
    ((restriction j).obj (SchemeExteriorPower.sheaf M n))).symm (presheafMap j M n)

theorem toSheaf_comp_map :
    SchemeExteriorPower.toSheaf ((restriction j).obj M) n ≫ (map j M n).val =
      presheafComparison j M n ≫ restrictedUnit j M n :=
  (SchemeExteriorPower.homEquiv ((restriction j).obj M) n
    ((restriction j).obj (SchemeExteriorPower.sheaf M n))).apply_symm_apply _

/-- Every original wedge is preserved through the actual image-open comparison. -/
theorem map_wedge (U : Y.Opens)
    (v : Fin n → ((restriction j).obj M).val.obj (op U)) :
    (map j M n).val.app (op U)
        (SchemeExteriorPower.wedge ((restriction j).obj M) n U v) =
      SchemeExteriorPower.wedge M n (j ''ᵁ U) v :=
  (congrArg (fun a => a.app (op U) (ModuleCat.exteriorPower.mk v))
    (toSheaf_comp_map j M n)).trans (presheafMap_mk j M n U v)

end KltDP.Geometry.SchemeExteriorPowerOpenRestriction
