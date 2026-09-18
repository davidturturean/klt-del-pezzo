import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Actual sections of a module-sheaf biproduct

The pinned evaluation functor is additive. Its existing biproduct
comparison and the actual module product comparison give the section
linear equivalence, with both original projections retained.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace KltDP.Geometry.SchemeModuleBiprodEvaluation

variable {X : Scheme.{u}}

local instance sectionsModulesBinaryBiproducts : HasBinaryBiproducts X.Modules :=
  HasBinaryBiproducts.of_hasBinaryProducts

local instance sectionsEvaluationAdditive (U : X.Opens) :
    (_root_.SheafOfModules.evaluation X.ringCatSheaf (op U)).Additive := by
  dsimp only [_root_.SheafOfModules.evaluation]
  infer_instance

local instance sectionsEvaluationBinaryBiproduct (M N : X.Modules) (U : X.Opens) :
    PreservesBinaryBiproduct M N
      (_root_.SheafOfModules.evaluation X.ringCatSheaf (op U)) :=
  preservesBinaryBiproduct_of_preservesBiproduct
    (_root_.SheafOfModules.evaluation X.ringCatSheaf (op U)) M N

/-- The actual evaluation of a biproduct is the product of the original sections. -/
def sectionPairIso (M N : X.Modules) (U : X.Opens) :
    (M ⊞ N).val.obj (op U) ≅ ModuleCat.of Γ(X, U)
      (M.val.obj (op U) × N.val.obj (op U)) :=
  (_root_.SheafOfModules.evaluation X.ringCatSheaf (op U)).mapBiprod M N ≪≫
    ModuleCat.biprodIsoProd (M.val.obj (op U)) (N.val.obj (op U))

theorem sectionPairIso_fst (M N : X.Modules) (U : X.Opens) :
    (sectionPairIso M N U).hom ≫ ModuleCat.ofHom (LinearMap.fst Γ(X, U)
      (M.val.obj (op U)) (N.val.obj (op U))) =
        (biprod.fst : M ⊞ N ⟶ M).val.app (op U) := by
  rw [← ModuleCat.biprodIsoProd_inv_comp_fst]
  simp only [sectionPairIso, Iso.trans_hom, Category.assoc, Iso.hom_inv_id_assoc,
    Functor.mapBiprod_hom]
  exact biprod.lift_fst _ _

theorem sectionPairIso_snd (M N : X.Modules) (U : X.Opens) :
    (sectionPairIso M N U).hom ≫ ModuleCat.ofHom (LinearMap.snd Γ(X, U)
      (M.val.obj (op U)) (N.val.obj (op U))) =
        (biprod.snd : M ⊞ N ⟶ N).val.app (op U) := by
  rw [← ModuleCat.biprodIsoProd_inv_comp_snd]
  simp only [sectionPairIso, Iso.trans_hom, Category.assoc, Iso.hom_inv_id_assoc,
    Functor.mapBiprod_hom]
  exact biprod.lift_snd _ _

/-- The comparison is linear over the original ring of sections. -/
def sectionPairEquiv (M N : X.Modules) (U : X.Opens) :
    (M ⊞ N).val.obj (op U) ≃ₗ[Γ(X, U)]
      M.val.obj (op U) × N.val.obj (op U) :=
  (sectionPairIso M N U).toLinearEquiv

theorem sectionPairEquiv_apply (M N : X.Modules) (U : X.Opens)
    (s : (M ⊞ N).val.obj (op U)) :
    sectionPairEquiv M N U s =
      ((biprod.fst : M ⊞ N ⟶ M).val.app (op U) s,
        (biprod.snd : M ⊞ N ⟶ N).val.app (op U) s) := by
  apply Prod.ext
  · exact ConcreteCategory.congr_hom (sectionPairIso_fst M N U) s
  · exact ConcreteCategory.congr_hom (sectionPairIso_snd M N U) s

/-- Applying an original biproduct lift gives precisely its two component maps. -/
theorem sectionPairEquiv_lift {P M N : X.Modules} (f : P ⟶ M) (g : P ⟶ N)
    (U : X.Opens) (s : P.val.obj (op U)) :
    sectionPairEquiv M N U ((biprod.lift f g).val.app (op U) s) =
      (f.val.app (op U) s, g.val.app (op U) s) := by
  rw [sectionPairEquiv_apply]
  apply Prod.ext
  · exact ConcreteCategory.congr_hom
      (congrArg (fun h : P ⟶ M => h.val.app (op U)) (biprod.lift_fst f g)) s
  · exact ConcreteCategory.congr_hom
      (congrArg (fun h : P ⟶ N => h.val.app (op U)) (biprod.lift_snd f g)) s

end KltDP.Geometry.SchemeModuleBiprodEvaluation

#check @KltDP.Geometry.SchemeModuleBiprodEvaluation.sectionPairEquiv
#print axioms KltDP.Geometry.SchemeModuleBiprodEvaluation.sectionPairEquiv
