import KltDP.Geometry.AffineModuleTildeTensorIso
import KltDP.Geometry.SchemeModuleTensorSections
import KltDP.Geometry.SchemeModulePullbackTensorSectionUnits

/-!
# Original pure tensors under the actual affine tilde tensor comparison

The existing comparison is the inverse of sheafification of the original
fractional-section tensor map. Its original counit and unit therefore give
the exact formula on canonical affine sections. These are the section
normalizations needed to restrict the original normal-twisted chart.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite
open scoped TensorProduct
universe u
namespace KltDP.Geometry.AffineModuleTildeTensor

open SchemeModuleTensorSections SchemeModulePullbackTensorSectionUnits

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance moduleTensor (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

local instance sectionCommRing (X : Scheme.{u}) (U : X.Opensᵒᵖ) :
    CommRing (X.ringCatSheaf.val.obj U) :=
  inferInstanceAs (CommRing (X.presheaf.obj U))

private theorem counit_unit_section {X : Scheme.{u}} (Q : X.Modules)
    (U : X.Opens) (q : Q.val.obj (op U)) :
    (PresheafOfModules.sheafificationForgetIso X.ringCatSheaf Q).hom.val.app (op U)
      (((PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.val)).unit.app Q.val).app (op U) q) = q := by
  have h := (PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.val)).right_triangle_components Q
  exact congrArg (fun a => a.app (op U) q) h

private theorem sheafification_desc_unit {X : Scheme.{u}}
    (P : X.PresheafOfModules) (Q : X.Modules) (a : P ⟶ Q.val)
    (U : X.Opens) (p : P.obj (op U)) :
    ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).map a ≫
      (PresheafOfModules.sheafificationForgetIso X.ringCatSheaf Q).hom).val.app (op U)
        (((PresheafOfModules.sheafificationAdjunction
          (𝟙 X.ringCatSheaf.val)).unit.app P).app (op U) p) = a.app (op U) p :=
  (congrArg ((PresheafOfModules.sheafificationForgetIso X.ringCatSheaf Q).hom.val.app (op U))
    (sheafification_map_unit a U p)).trans (counit_unit_section Q U (a.app (op U) p))

variable {R : Type u} [CommRing R] (M N : ModuleCat.{u} R)

local instance canonicalTensorSectionRingModule (P : ModuleCat.{u} R)
    (U : (Spec (CommRingCat.of R)).Opens) :
    Module ((Spec (CommRingCat.of R)).ringCatSheaf.val.obj (op U))
      (P.tildeInModuleCat.obj (op U)) :=
  (P.tilde.val.obj (op U)).isModule

/-- The inverse original comparison tensors the two actual canonical sections. -/
theorem iso_inv_tensorSection (U : (Spec (CommRingCat.of R)).Opens) (m : M) (n : N) :
    (iso M N).inv.val.app (op U)
        (tensorSection M.tilde N.tilde U
          (ModuleCat.Tilde.toOpen M U m) (ModuleCat.Tilde.toOpen N U n)) =
      ModuleCat.Tilde.toOpen (tensorModule M N) U (m ⊗ₜ[R] n) := by
  let X := Spec (CommRingCat.of R)
  let S := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)
  let T := PresheafOfModules.sheafTensorIsoSheafification
    X.sheaf.val X.ringCatSheaf.cond M.tilde N.tilde
  let η := (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.val)).unit
  let x := ModuleCat.Tilde.toOpen M U m ⊗ₜ[X.ringCatSheaf.val.obj (op U)]
    ModuleCat.Tilde.toOpen N U n
  change (T.inv ≫ (T.hom ≫ S.map (presheafMap M N) ≫
    (PresheafOfModules.sheafificationForgetIso X.ringCatSheaf (tensorModule M N).tilde).hom)).val.app
      (op U) ((η.app (tensorPresheaf M N)).app (op U) x) = _
  rw [Iso.inv_hom_id_assoc]
  exact (sheafification_desc_unit (tensorPresheaf M N) (tensorModule M N).tilde
    (presheafMap M N) U x).trans (sectionsPure_toOpen M N U m n)

/-- The original forward comparison sends a canonical native tensor to its actual sheaf tensor. -/
theorem iso_hom_toOpen_tmul (U : (Spec (CommRingCat.of R)).Opens) (m : M) (n : N) :
    (iso M N).hom.val.app (op U)
        (ModuleCat.Tilde.toOpen (tensorModule M N) U (m ⊗ₜ[R] n)) =
      tensorSection M.tilde N.tilde U
        (ModuleCat.Tilde.toOpen M U m) (ModuleCat.Tilde.toOpen N U n) := by
  let e := iso M N
  let s := tensorSection M.tilde N.tilde U
    (ModuleCat.Tilde.toOpen M U m) (ModuleCat.Tilde.toOpen N U n)
  have h := congrArg (e.hom.val.app (op U)) (iso_inv_tensorSection M N U m n)
  exact h.symm.trans (congrArg (fun a : M.tilde ⊗ N.tilde ⟶ M.tilde ⊗ N.tilde =>
    a.val.app (op U) s) e.inv_hom_id)

end KltDP.Geometry.AffineModuleTildeTensor
