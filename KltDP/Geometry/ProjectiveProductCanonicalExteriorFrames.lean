import KltDP.Geometry.ProjectiveProductCanonicalExteriorMap
import KltDP.LinearAlgebra.FramedTensorExteriorSquare
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits

/-!
# The original tensor-to-exterior map on framed opens

Evaluation preserves the actual sheaf biproduct. Its canonical comparison
with the product of the two section modules identifies the original
inclusions. The proved framed tensor-to-wedge equivalence therefore proves
the original section map bijective whenever the two section modules are
actually framed. These frames will be obtained from local trivializations.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

universe u

namespace KltDP.Geometry.ProjectiveProductCanonicalExteriorFrames

open ProjectiveProductCanonicalExteriorMap

attribute [local instance] Types.instFunLike Types.instConcreteCategory

private theorem module_inl_prod {A : Type u} [CommRing A] (L M : ModuleCat.{u} A) :
    (biprod.inl : L ⟶ L ⊞ M) ≫ (ModuleCat.biprodIsoProd L M).hom =
      ModuleCat.ofHom (LinearMap.inl A L M) := by
  apply (cancel_mono (ModuleCat.biprodIsoProd L M).inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply biprod.hom_ext <;>
    simp only [Category.assoc, ModuleCat.biprodIsoProd_inv_comp_fst,
      ModuleCat.biprodIsoProd_inv_comp_snd, biprod.inl_fst, biprod.inl_snd] <;> rfl

private theorem module_inr_prod {A : Type u} [CommRing A] (L M : ModuleCat.{u} A) :
    (biprod.inr : M ⟶ L ⊞ M) ≫ (ModuleCat.biprodIsoProd L M).hom =
      ModuleCat.ofHom (LinearMap.inr A L M) := by
  apply (cancel_mono (ModuleCat.biprodIsoProd L M).inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply biprod.hom_ext <;>
    simp only [Category.assoc, ModuleCat.biprodIsoProd_inv_comp_fst,
      ModuleCat.biprodIsoProd_inv_comp_snd, biprod.inr_fst, biprod.inr_snd] <;> rfl

variable {X : Scheme.{u}} (L M : X.Modules)

local instance sectionRingCommRing (U : X.Opens) :
    CommRing (X.ringCatSheaf.val.obj (op U)) :=
  inferInstanceAs (CommRing Γ(X, U))

private abbrev evaluation (U : X.Opens) :=
  _root_.SheafOfModules.evaluation X.ringCatSheaf (op U)

local instance evaluation_preservesZero (U : X.Opens) :
    (evaluation U).PreservesZeroMorphisms := ⟨by intros; rfl⟩

local instance evaluation_preservesBiprod (U : X.Opens) :
    PreservesBinaryBiproduct L M (evaluation U) :=
  preservesBinaryBiproduct_of_preservesBinaryProduct (evaluation U) (X := L) (Y := M)

/-- The actual sections of the sheaf biproduct are the product of the original sections. -/
def sectionIso (U : X.Opens) :
    (L ⊞ M).val.obj (op U) ≅
      ModuleCat.of Γ(X, U) ((L.val.obj (op U)) × (M.val.obj (op U))) :=
  (evaluation U).mapBiprod L M ≪≫
    ModuleCat.biprodIsoProd (L.val.obj (op U)) (M.val.obj (op U))

/-- The section-product comparison preserves the original first inclusion. -/
theorem sectionIso_inl (U : X.Opens) (x : L.val.obj (op U)) :
    (sectionIso L M U).hom ((biprod.inl : L ⟶ L ⊞ M).val.app (op U) x) = (x, 0) := by
  have h : (evaluation U).map (biprod.inl : L ⟶ L ⊞ M) ≫
      ((evaluation U).mapBiprod L M).hom = biprod.inl := by
    apply (cancel_mono ((evaluation U).mapBiprod L M).inv).mp
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id,
      CategoryTheory.Functor.mapBiprod_inv, biprod.inl_desc]
  have h' := (congrArg (fun a => a ≫
    (ModuleCat.biprodIsoProd (L.val.obj (op U)) (M.val.obj (op U))).hom) h).trans
      (module_inl_prod (L.val.obj (op U)) (M.val.obj (op U)))
  exact ConcreteCategory.congr_hom h' x

/-- The section-product comparison preserves the original second inclusion. -/
theorem sectionIso_inr (U : X.Opens) (y : M.val.obj (op U)) :
    (sectionIso L M U).hom ((biprod.inr : M ⟶ L ⊞ M).val.app (op U) y) = (0, y) := by
  have h : (evaluation U).map (biprod.inr : M ⟶ L ⊞ M) ≫
      ((evaluation U).mapBiprod L M).hom = biprod.inr := by
    apply (cancel_mono ((evaluation U).mapBiprod L M).inv).mp
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id,
      CategoryTheory.Functor.mapBiprod_inv, biprod.inr_desc]
  have h' := (congrArg (fun a => a ≫
    (ModuleCat.biprodIsoProd (L.val.obj (op U)) (M.val.obj (op U))).hom) h).trans
      (module_inr_prod (L.val.obj (op U)) (M.val.obj (op U)))
  exact ConcreteCategory.congr_hom h' y

/-- The exterior of the actual section-product comparison. -/
def sectionExteriorIso (U : X.Opens) :
    (SchemeExteriorPower.presheaf (L ⊞ M) 2).obj (op U) ≅
      (ModuleCat.of Γ(X, U) ((L.val.obj (op U)) × (M.val.obj (op U)))).exteriorPower 2 :=
  (ModuleCat.exteriorPower.functor Γ(X, U) 2).mapIso (sectionIso L M U)

/-- The original section map agrees with the proved framed tensor-to-wedge equivalence. -/
theorem sectionsMap_comp_sectionExteriorIso (U : X.Opens)
    (a : (L.val.obj (op U)) ≃ₗ[Γ(X, U)] Γ(X, U))
    (b : (M.val.obj (op U)) ≃ₗ[Γ(X, U)] Γ(X, U)) :
    sectionsMap L M U ≫ (sectionExteriorIso L M U).hom =
      (KltDP.LinearAlgebra.FramedTensorExteriorSquare.equiv a b).toModuleIso.hom := by
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  change ModuleCat.exteriorPower.map (sectionIso L M U).hom 2
      (sectionsMap L M U (x ⊗ₜ[Γ(X, U)] y)) =
    KltDP.LinearAlgebra.FramedTensorExteriorSquare.equiv a b (x ⊗ₜ[Γ(X, U)] y)
  rw [sectionsMap_tmul, KltDP.LinearAlgebra.FramedTensorExteriorSquare.equiv_tmul]
  change ModuleCat.exteriorPower.map (sectionIso L M U).hom 2
      (ModuleCat.exteriorPower.mk
        ![(biprod.inl : L ⟶ L ⊞ M).val.app (op U) x,
          (biprod.inr : M ⟶ L ⊞ M).val.app (op U) y]) = _
  rw [ModuleCat.exteriorPower.map_mk]
  congr 1
  funext i
  fin_cases i
  · exact sectionIso_inl L M U x
  · exact sectionIso_inr L M U y

/-- Actual rank-one section frames make the original tensor-to-exterior section map invertible. -/
theorem sectionsMap_isIso (U : X.Opens)
    (a : (L.val.obj (op U)) ≃ₗ[Γ(X, U)] Γ(X, U))
    (b : (M.val.obj (op U)) ≃ₗ[Γ(X, U)] Γ(X, U)) :
    IsIso (sectionsMap L M U) := by
  letI : IsIso (sectionsMap L M U ≫ (sectionExteriorIso L M U).hom) := by
    rw [sectionsMap_comp_sectionExteriorIso L M U a b]
    infer_instance
  exact IsIso.of_isIso_comp_right (sectionsMap L M U) (sectionExteriorIso L M U).hom

/-- Bijectivity is for the original section map and original tensor/exterior modules. -/
theorem sectionsMap_bijective (U : X.Opens)
    (a : (L.val.obj (op U)) ≃ₗ[Γ(X, U)] Γ(X, U))
    (b : (M.val.obj (op U)) ≃ₗ[Γ(X, U)] Γ(X, U)) :
    Function.Bijective (sectionsMap L M U) := by
  letI := sectionsMap_isIso L M U a b
  exact ConcreteCategory.bijective_of_isIso (sectionsMap L M U)

end KltDP.Geometry.ProjectiveProductCanonicalExteriorFrames
