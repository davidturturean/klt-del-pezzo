import KltDP.Geometry.SchemeModulePullbackTensorUnit

/-!
# Unit-section formulas for the original pullback tensor map

Naturality of the actual adjunction units gives their section formulas.
The accepted presheaf pullback tensor normalization then gives the exact
pure-tensor formula for the original presheaf comparison. These are the
remaining sectionwise inputs to the sheaf pullback tensor normalization.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite
open scoped TensorProduct

universe u

namespace KltDP.Geometry.SchemeModulePullbackTensorSectionUnits

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance presheafTensor (X : Scheme.{u}) : MonoidalCategory X.PresheafOfModules :=
  PresheafOfModules.monoidalCategory (R := X.sheaf.val)

local instance sectionCommRing (X : Scheme.{u}) (U : X.Opensᵒᵖ) :
    CommRing (X.ringCatSheaf.val.obj U) :=
  inferInstanceAs (CommRing (X.presheaf.obj U))

/-- Naturality of the original sheafification unit, on original local sections. -/
theorem sheafification_map_unit {X : Scheme.{u}} {P Q : X.PresheafOfModules}
    (a : P ⟶ Q) (U : X.Opens) (p : P.obj (op U)) :
    ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).map a).val.app (op U)
        (((PresheafOfModules.sheafificationAdjunction
          (𝟙 X.ringCatSheaf.val)).unit.app P).app (op U) p) =
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.val)).unit.app Q).app (op U) (a.app (op U) p) :=
  (congrArg (fun b => b.app (op U) p)
    ((PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.val)).unit.naturality a)).symm

variable {X Y : Scheme.{u}} (f : Y ⟶ X)

/-- Naturality of the original scheme pullback unit on its actual inverse-image open. -/
theorem pullback_map_unit {M N : X.Modules} (a : M ⟶ N) (U : X.Opens)
    (m : M.val.obj (op U)) :
    ((schemeModulePullback f).map a).val.app (op (f ⁻¹ᵁ U))
        (((schemeModulePullbackPushforwardAdjunction f).unit.app M).val.app (op U) m) =
      ((schemeModulePullbackPushforwardAdjunction f).unit.app N).val.app (op U)
        (a.val.app (op U) m) :=
  (congrArg (fun b => b.val.app (op U) m)
    ((schemeModulePullbackPushforwardAdjunction f).unit.naturality a)).symm

/-- The original presheaf tensor comparison sends an original unit pure tensor
to the pure tensor of its two original unit images. -/
theorem presheafTensor_unit_tmul (P Q : X.PresheafOfModules) (U : X.Opens)
    (p : P.obj (op U)) (q : Q.obj (op U)) :
    (schemeModulePresheafPullbackTensorIso f P Q).hom.app (op (f ⁻¹ᵁ U))
        (((PresheafOfModules.pullbackPushforwardAdjunction
          (schemeRingSheafHom f).val).unit.app (P ⊗ Q)).app (op U)
          (p ⊗ₜ[X.ringCatSheaf.val.obj (op U)] q)) =
      (show ((PresheafOfModules.pullback (schemeRingSheafHom f).val).obj P).obj
          (op (f ⁻¹ᵁ U)) from
        ((PresheafOfModules.pullbackPushforwardAdjunction
          (schemeRingSheafHom f).val).unit.app P).app (op U) p) ⊗ₜ[Y.ringCatSheaf.val.obj (op (f ⁻¹ᵁ U))]
        (show ((PresheafOfModules.pullback (schemeRingSheafHom f).val).obj Q).obj
            (op (f ⁻¹ᵁ U)) from
          ((PresheafOfModules.pullbackPushforwardAdjunction
            (schemeRingSheafHom f).val).unit.app Q).app (op U) q) := by
  exact PresheafOfModules.pushforwardFactored_map_pullback_δ_unit_tmul
    (PresheafOfModules.schemeRingPresheafHom f) P Q (op U) p q

end KltDP.Geometry.SchemeModulePullbackTensorSectionUnits
