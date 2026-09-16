import KltDP.Geometry.SchemeStructureTensorScalar
import KltDP.Geometry.ModuleCohomology
import KltDP.Compatibility.FreePresheafTensor

/-!
# Literal scalar action through the original structure-module tensor

The original right-unitor comparison for an arbitrary scheme module agrees
with sheafification of its sectionwise presheaf unitor. Consequently tensoring
with multiplication by a global function, and cancelling the structure
module, gives the already constructed `ModuleCohomology.globalSmulHom`.
Its formula on every original module section is literal scalar multiplication.

This extends the accepted `SchemeStructureTensor` normalization from the unit
module to arbitrary coefficient modules. It reuses its proved sheafification
unitality and the existing global scalar morphism; no scalar action, tensor
compatibility, coherence, or section extension is supplied as a hypothesis.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite
open scoped TensorProduct

universe u

namespace KltDP.Geometry.SchemeModuleTensorScalar

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance scalarModuleTensor (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

local instance scalarPresheafTensor (X : Scheme.{u}) : MonoidalCategory X.PresheafOfModules :=
  PresheafOfModules.monoidalCategory (R := X.sheaf.val)

local instance scalarSheafificationTensor (X : Scheme.{u}) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).Monoidal :=
  PresheafOfModules.sheafificationMonoidal X.sheaf.val X.ringCatSheaf.cond

local instance sectionCommRing {X : Scheme.{u}} (V : (X.Opens)ᵒᵖ) :
    CommRing (X.ringCatSheaf.val.obj V) :=
  inferInstanceAs (CommRing (X.presheaf.obj V))

local instance originalSectionModule {X : Scheme.{u}} (M : X.Modules) (V : X.Opens) :
    Module Γ(X, V) (M.val.obj (op V)) := (M.val.obj (op V)).isModule

open ModuleCohomology

variable {X : Scheme.{u}}

/-- The existing original global scalar morphism has the literal section formula. -/
theorem globalSmulHom_app (M : X.Modules) (a : Γ(X, ⊤)) (V : X.Opens)
    (m : M.val.obj (op V)) :
    (globalSmulHom M a).val.app (op V) m =
      X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op a • m := rfl

set_option maxHeartbeats 800000 in
/-- For every actual module, the chosen structure-module unitor is
the sheafification of its original sectionwise presheaf unitor. -/
theorem sheafTensorIso_structure_right (M : X.Modules) :
    (PresheafOfModules.sheafTensorIsoSheafification X.sheaf.val X.ringCatSheaf.cond
      M (_root_.SheafOfModules.unit X.ringCatSheaf)).hom ≫
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).map (ρ_ M.val).hom ≫
      (PresheafOfModules.sheafificationForgetIso X.ringCatSheaf M).hom =
    (schemeStructureTensorRightIso M).hom := by
  let ε := PresheafOfModules.sheafificationForgetIso X.ringCatSheaf M
  let e : 𝟙_ X.Modules ≅ _root_.SheafOfModules.unit X.ringCatSheaf :=
    PresheafOfModules.sheafTensorUnitIso X.sheaf.val X.ringCatSheaf.cond
  simp only [PresheafOfModules.sheafTensorIsoSheafification, Iso.trans_hom,
    tensorIso_hom, Iso.symm_hom, Functor.Monoidal.μIso_hom, Category.assoc]
  change (ε.inv ⊗ e.inv) ≫
      Functor.LaxMonoidal.μ (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val))
        M.val (𝟙_ X.PresheafOfModules) ≫
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).map (ρ_ M.val).hom ≫
      ε.hom = M ◁ e.inv ≫ (ρ_ M).hom
  rw [schemeSheafification_lax_right_unitality_assoc X M.val]
  simp only [tensorHom_def', Category.assoc, rightUnitor_naturality_assoc,
    ε.inv_hom_id, Category.comp_id]

set_option maxHeartbeats 800000 in
private theorem presheaf_right_scalar (M : X.Modules) (a : Γ(X, ⊤)) :
    (𝟙 M.val ⊗ (schemeScalarEnd a).val) ≫ (ρ_ M.val).hom =
      (ρ_ M.val).hom ≫ (globalSmulHom M a).val := by
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m r
  change (ρ_ (M.val.obj V)).hom
      ((𝟙 M.val ⊗ (schemeScalarEnd a).val).app V (m ⊗ₜ r)) =
    (globalSmulHom M a).val.app V ((ρ_ (M.val.obj V)).hom (m ⊗ₜ r))
  erw [PresheafOfModules.tensorHom_app_tmul (T := X.sheaf.val),
    ModuleCat.MonoidalCategory.rightUnitor_hom_apply,
    ModuleCat.MonoidalCategory.rightUnitor_hom_apply]
  let aV : Γ(X, V.unop) :=
    X.presheaf.map (homOfLE (show V.unop ≤ ⊤ from le_top)).op a
  let r' : Γ(X, V.unop) := r
  change (r' * aV) • m = aV • (r' • m)
  rw [smul_smul, mul_comm r' aV]

set_option maxHeartbeats 800000 in
/-- The actual tensor with a scalar endomorphism is the original scalar
action on the arbitrary coefficient module, through its original unitor. -/
theorem structureTensorRight_scalar (M : X.Modules) (a : Γ(X, ⊤)) :
    (𝟙 M ⊗ schemeScalarEnd a) ≫ (schemeStructureTensorRightIso M).hom =
      (schemeStructureTensorRightIso M).hom ≫ globalSmulHom M a := by
  let F := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)
  let ε := PresheafOfModules.sheafificationForgetIso X.ringCatSheaf M
  let τ := PresheafOfModules.sheafTensorIsoSheafification
    X.sheaf.val X.ringCatSheaf.cond M (_root_.SheafOfModules.unit X.ringCatSheaf)
  have hτ : τ.hom ≫ F.map (ρ_ M.val).hom ≫ ε.hom =
      (schemeStructureTensorRightIso M).hom := sheafTensorIso_structure_right M
  have hε : F.map (globalSmulHom M a).val ≫ ε.hom = ε.hom ≫ globalSmulHom M a :=
    schemeSheafificationForgetIso_hom_natural (globalSmulHom M a)
  calc
    _ = (𝟙 M ⊗ schemeScalarEnd a) ≫ τ.hom ≫ F.map (ρ_ M.val).hom ≫ ε.hom := by
      rw [hτ]
    _ = τ.hom ≫ F.map
        ((𝟙 M.val ⊗ (schemeScalarEnd a).val) ≫ (ρ_ M.val).hom) ≫ ε.hom := by
      simpa only [Category.assoc, Functor.map_comp, _root_.SheafOfModules.id_val] using
        congrArg (fun g => g ≫ F.map (ρ_ M.val).hom ≫ ε.hom)
          (schemeSheafTensorIsoSheafification_natural (𝟙 M) (schemeScalarEnd a))
    _ = τ.hom ≫ F.map ((ρ_ M.val).hom ≫ (globalSmulHom M a).val) ≫ ε.hom := by
      rw [presheaf_right_scalar]
    _ = (τ.hom ≫ F.map (ρ_ M.val).hom ≫ ε.hom) ≫ globalSmulHom M a := by
      simp only [Functor.map_comp, Category.assoc]
      rw [hε]
    _ = _ := by rw [hτ]

/-- Cancelling the original structure tensor identifies the actual tensor
endomorphism with the original global scalar endomorphism. -/
theorem structureTensorRight_scalar_conjugate (M : X.Modules) (a : Γ(X, ⊤)) :
    (schemeStructureTensorRightIso M).inv ≫
        (𝟙 M ⊗ schemeScalarEnd a) ≫ (schemeStructureTensorRightIso M).hom =
      globalSmulHom M a := by
  rw [structureTensorRight_scalar, Iso.inv_hom_id_assoc]

/-- This identification acts on every original local section by the
literal restricted coefficient; no global generation is needed. -/
theorem structureTensorRight_scalar_apply (M : X.Modules) (a : Γ(X, ⊤)) (V : X.Opens)
    (m : M.val.obj (op V)) :
    ((schemeStructureTensorRightIso M).inv ≫
        (𝟙 M ⊗ schemeScalarEnd a) ≫ (schemeStructureTensorRightIso M).hom).val.app
        (op V) m =
      X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op a • m := by
  rw [structureTensorRight_scalar_conjugate]
  exact globalSmulHom_app M a V m

end KltDP.Geometry.SchemeModuleTensorScalar
