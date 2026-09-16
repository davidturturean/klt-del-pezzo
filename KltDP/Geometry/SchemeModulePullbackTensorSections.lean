import KltDP.Geometry.SchemeSheafificationTensorSections
import KltDP.Geometry.SchemeModulePullbackSheafificationSections
import KltDP.Geometry.SchemeModulePullbackTensorSectionUnits

/-!
# The original scheme pullback tensor map on local pure tensors

Each of the five original comparison factors has an independently proved
formula on the original adjunction-unit sections. Their composition gives
the exact local formula for the existing scheme pullback tensor isomorphism.
This is the section normalization needed for its composition law.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite
open scoped TensorProduct

universe u

namespace KltDP.Geometry.SchemeModulePullbackTensorSections

open SchemeModuleTensorSections SchemeModulePullbackSheafificationSections
open SchemeModulePullbackTensorSectionUnits SchemeSheafificationTensorSections

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance moduleTensor (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

local instance presheafTensor (X : Scheme.{u}) : MonoidalCategory X.PresheafOfModules :=
  PresheafOfModules.monoidalCategory (R := X.sheaf.val)

local instance sheafificationTensor (X : Scheme.{u}) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).Monoidal :=
  PresheafOfModules.sheafificationMonoidal X.sheaf.val X.ringCatSheaf.cond

local instance sectionCommRing (X : Scheme.{u}) (U : X.Opensᵒᵖ) :
    CommRing (X.ringCatSheaf.val.obj U) :=
  inferInstanceAs (CommRing (X.presheaf.obj U))

private theorem tensorSection_hom {X : Scheme.{u}} (M N : X.Modules) (U : X.Opens)
    (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    (PresheafOfModules.sheafTensorIsoSheafification
      X.sheaf.val X.ringCatSheaf.cond M N).hom.val.app (op U)
        (tensorSection M N U m n) =
      ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.val)).unit.app
        (M.val ⊗ N.val)).app (op U) (m ⊗ₜ[X.ringCatSheaf.val.obj (op U)] n) := by
  let S := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)
  let T : M ⊗ N ≅ S.obj (M.val ⊗ N.val) :=
    PresheafOfModules.sheafTensorIsoSheafification X.sheaf.val X.ringCatSheaf.cond M N
  change (T.inv ≫ T.hom).val.app (op U) _ = _
  rw [Iso.inv_hom_id]
  rfl

private theorem pullbackSheafification_inv_unit {X Y : Scheme.{u}} (f : Y ⟶ X)
    (M : X.Modules) (U : X.Opens) (m : M.val.obj (op U)) :
    (schemeModulePullbackSheafificationIso f M).inv.val.app (op (f ⁻¹ᵁ U))
      (((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.val)).unit.app
        ((PresheafOfModules.pullback (schemeRingSheafHom f).val).obj M.val)).app
          (op (f ⁻¹ᵁ U))
          (((PresheafOfModules.pullbackPushforwardAdjunction
            (schemeRingSheafHom f).val).unit.app M.val).app (op U) m)) =
      ((schemeModulePullbackPushforwardAdjunction f).unit.app M).val.app (op U) m := by
  let T := schemeModulePullbackSheafificationIso f M
  have h := congrArg (T.inv.val.app (op (f ⁻¹ᵁ U)))
    (pullbackSheafification_unit f M U m)
  change (T.hom ≫ T.inv).val.app (op (f ⁻¹ᵁ U))
    (((schemeModulePullbackPushforwardAdjunction f).unit.app M).val.app (op U) m) = _ at h
  rw [Iso.hom_inv_id] at h
  exact h.symm

/-- The actual tensor comparison sends the original unit image of a local pure tensor
to the local pure tensor of the two original pullback-unit images. -/
theorem tensor_unit_section {X Y : Scheme.{u}} (f : Y ⟶ X)
    (M N : X.Modules) (U : X.Opens) (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    (schemeModulePullbackTensorIso f M N).hom.val.app (op (f ⁻¹ᵁ U))
      (((schemeModulePullbackPushforwardAdjunction f).unit.app (M ⊗ N)).val.app (op U)
        (tensorSection M N U m n)) =
      tensorSection ((schemeModulePullback f).obj M) ((schemeModulePullback f).obj N)
        (f ⁻¹ᵁ U)
        (((schemeModulePullbackPushforwardAdjunction f).unit.app M).val.app (op U) m)
        (((schemeModulePullbackPushforwardAdjunction f).unit.app N).val.app (op U) n) := by
  let F := schemeModulePullback f
  let SX := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)
  let SY := PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.val)
  let PB := PresheafOfModules.pullback (schemeRingSheafHom f).val
  let aX := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.val)
  let aY := PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.val)
  let aP := PresheafOfModules.pullbackPushforwardAdjunction (schemeRingSheafHom f).val
  let aF := schemeModulePullbackPushforwardAdjunction f
  let V := f ⁻¹ᵁ U
  let x := m ⊗ₜ[X.ringCatSheaf.val.obj (op U)] n
  let p : (PB.obj M.val).obj (op V) := (aP.unit.app M.val).app (op U) m
  let q : (PB.obj N.val).obj (op V) := (aP.unit.app N.val).app (op U) n
  let TX : M ⊗ N ≅ SX.obj (M.val ⊗ N.val) :=
    PresheafOfModules.sheafTensorIsoSheafification X.sheaf.val X.ringCatSheaf.cond M N
  let C := (_root_.SheafOfModules.sheafificationCompPullback
    (schemeRingSheafHom f)).app (M.val ⊗ N.val)
  let TP := schemeModulePresheafPullbackTensorIso f M.val N.val
  let TS := Functor.Monoidal.μIso SY (PB.obj M.val) (PB.obj N.val)
  let TM := schemeModulePullbackSheafificationIso f M
  let TN := schemeModulePullbackSheafificationIso f N
  have h₁ : (F.map TX.hom).val.app (op V)
      ((aF.unit.app (M ⊗ N)).val.app (op U) (tensorSection M N U m n)) =
      (aF.unit.app (SX.obj (M.val ⊗ N.val))).val.app (op U)
        ((aX.unit.app (M.val ⊗ N.val)).app (op U) x) :=
    (pullback_map_unit f TX.hom U (tensorSection M N U m n)).trans
      (congrArg ((aF.unit.app (SX.obj (M.val ⊗ N.val))).val.app (op U))
        (tensorSection_hom M N U m n))
  have h₂ : C.hom.val.app (op V)
      ((aF.unit.app (SX.obj (M.val ⊗ N.val))).val.app (op U)
        ((aX.unit.app (M.val ⊗ N.val)).app (op U) x)) =
      (aY.unit.app (PB.obj (M.val ⊗ N.val))).app (op V)
        ((aP.unit.app (M.val ⊗ N.val)).app (op U) x) :=
    sheafificationCompPullback_unit f (M.val ⊗ N.val) U x
  have h₃ : (SY.map TP.hom).val.app (op V)
      ((aY.unit.app (PB.obj (M.val ⊗ N.val))).app (op V)
        ((aP.unit.app (M.val ⊗ N.val)).app (op U) x)) =
      (aY.unit.app (PB.obj M.val ⊗ PB.obj N.val)).app (op V)
        (p ⊗ₜ[Y.ringCatSheaf.val.obj (op V)] q) :=
    (sheafification_map_unit TP.hom V
      ((aP.unit.app (M.val ⊗ N.val)).app (op U) x)).trans
      (congrArg ((aY.unit.app (PB.obj M.val ⊗ PB.obj N.val)).app (op V))
        (presheafTensor_unit_tmul f M.val N.val U m n))
  have h₄ : TS.inv.val.app (op V)
      ((aY.unit.app (PB.obj M.val ⊗ PB.obj N.val)).app (op V)
        (p ⊗ₜ[Y.ringCatSheaf.val.obj (op V)] q)) =
      tensorSection (SY.obj (PB.obj M.val)) (SY.obj (PB.obj N.val)) V
        ((aY.unit.app (PB.obj M.val)).app (op V) p)
        ((aY.unit.app (PB.obj N.val)).app (op V) q) :=
    tensor_inv_unit_tmul (PB.obj M.val) (PB.obj N.val) V p q
  have h₅ : (tensorIso TM.symm TN.symm).hom.val.app (op V)
      (tensorSection (SY.obj (PB.obj M.val)) (SY.obj (PB.obj N.val)) V
        ((aY.unit.app (PB.obj M.val)).app (op V) p)
        ((aY.unit.app (PB.obj N.val)).app (op V) q)) =
      tensorSection (F.obj M) (F.obj N) V
        ((aF.unit.app M).val.app (op U) m) ((aF.unit.app N).val.app (op U) n) :=
    (tensorSection_natural TM.inv TN.inv V
      ((aY.unit.app (PB.obj M.val)).app (op V) p)
      ((aY.unit.app (PB.obj N.val)).app (op V) q)).trans
      (congrArg₂ (tensorSection (F.obj M) (F.obj N) V)
        (pullbackSheafification_inv_unit f M U m)
        (pullbackSheafification_inv_unit f N U n))
  change (tensorIso TM.symm TN.symm).hom.val.app (op V)
    (TS.inv.val.app (op V) ((SY.map TP.hom).val.app (op V)
      (C.hom.val.app (op V) ((F.map TX.hom).val.app (op V)
        ((aF.unit.app (M ⊗ N)).val.app (op U) (tensorSection M N U m n)))))) = _
  rw [h₁, h₂, h₃, h₄]
  exact h₅

end KltDP.Geometry.SchemeModulePullbackTensorSections
