import KltDP.Geometry.SchemeModuleTensorSections

/-!
# The original sheafification tensor map on local pure tensors

The existing sheafification adjunction triangle identifies the image of
its unit with the inverse counit. Naturality of its original monoidal
comparison therefore fixes that comparison on original local pure tensors.
No new monoidal structure or compatibility hypothesis is introduced.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite
open scoped TensorProduct

universe u

namespace KltDP.Geometry.SchemeSheafificationTensorSections

open SchemeModuleTensorSections

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

variable {X : Scheme.{u}}

private theorem map_unit (P : X.PresheafOfModules) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).map
        ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.val)).unit.app P) =
      (PresheafOfModules.sheafificationForgetIso X.ringCatSheaf
        ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).obj P)).inv := by
  apply (cancel_mono (PresheafOfModules.sheafificationForgetIso X.ringCatSheaf
    ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).obj P)).hom).mp
  rw [Iso.inv_hom_id]
  exact (PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.val)).left_triangle_components P

set_option maxHeartbeats 800000 in
/-- The original sheafification tensor comparison is normalized by its original unit. -/
theorem tensor_inv_comparison (P Q : X.PresheafOfModules) :
    (Functor.Monoidal.μIso
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)) P Q).inv ≫
      (PresheafOfModules.sheafTensorIsoSheafification X.sheaf.val X.ringCatSheaf.cond
        ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).obj P)
        ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).obj Q)).hom =
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).map
      (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.val)).unit.app P) ⊗
        ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.val)).unit.app Q)) := by
  apply (cancel_epi (Functor.Monoidal.μIso
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)) P Q).hom).mp
  rw [Iso.hom_inv_id_assoc]
  simp only [PresheafOfModules.sheafTensorIsoSheafification, Iso.trans_hom,
    tensorIso_hom, Iso.symm_hom, Functor.Monoidal.μIso_hom]
  change ((PresheafOfModules.sheafificationForgetIso X.ringCatSheaf
        ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).obj P)).inv ⊗
      (PresheafOfModules.sheafificationForgetIso X.ringCatSheaf
        ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).obj Q)).inv) ≫
      Functor.LaxMonoidal.μ (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val))
        ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).obj P).val
        ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).obj Q).val = _
  rw [← map_unit P, ← map_unit Q]
  exact Functor.LaxMonoidal.μ_natural
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)) _ _

/-- The original tensor comparison sends the unit image of a pure tensor
to the original local pure tensor of its two unit images. -/
theorem tensor_inv_unit_tmul (P Q : X.PresheafOfModules) (U : X.Opens)
    (p : P.obj (op U)) (q : Q.obj (op U)) :
    (Functor.Monoidal.μIso
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)) P Q).inv.val.app (op U)
        (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.val)).unit.app
          (P ⊗ Q)).app (op U) (p ⊗ₜ[X.ringCatSheaf.val.obj (op U)] q)) =
      tensorSection
        ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).obj P)
        ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).obj Q) U
        (((PresheafOfModules.sheafificationAdjunction
          (𝟙 X.ringCatSheaf.val)).unit.app P).app (op U) p)
        (((PresheafOfModules.sheafificationAdjunction
          (𝟙 X.ringCatSheaf.val)).unit.app Q).app (op U) q) := by
  let S := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.val)
  let T := PresheafOfModules.sheafTensorIsoSheafification
    X.sheaf.val X.ringCatSheaf.cond (S.obj P) (S.obj Q)
  let z := (adj.unit.app (P ⊗ Q)).app (op U)
    (p ⊗ₜ[X.ringCatSheaf.val.obj (op U)] q)
  have ht := congrArg (fun a => a.val.app (op U) z) (tensor_inv_comparison P Q)
  have hη := congrArg (fun a => a.app (op U)
      (p ⊗ₜ[X.ringCatSheaf.val.obj (op U)] q))
    (adj.unit.naturality ((adj.unit.app P) ⊗ (adj.unit.app Q)))
  change (adj.unit.app ((S.obj P).val ⊗ (S.obj Q).val)).app (op U)
      (((adj.unit.app P) ⊗ (adj.unit.app Q)).app (op U)
        (p ⊗ₜ[X.ringCatSheaf.val.obj (op U)] q)) =
    (S.map ((adj.unit.app P) ⊗ (adj.unit.app Q))).val.app (op U) z at hη
  erw [PresheafOfModules.Monoidal.tensorHom_app,
    ModuleCat.MonoidalCategory.tensorHom_tmul] at hη
  have hh := congrArg (T.inv.val.app (op U)) (ht.trans hη.symm)
  change (T.hom ≫ T.inv).val.app (op U)
      ((Functor.Monoidal.μIso S P Q).inv.val.app (op U) z) = _ at hh
  rw [Iso.hom_inv_id] at hh
  exact hh

end KltDP.Geometry.SchemeSheafificationTensorSections
