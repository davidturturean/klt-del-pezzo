import KltDP.Geometry.SectionZeroScheme
import KltDP.Geometry.SchemeModulePullbackTensorNaturality

/-!
# Naturality of the original sheaf dual evaluation

The accepted `evalSection_precomp` identifies the original local functionals.
The original sheafification and tensor comparisons lift that equality to
actual global tensor evaluation. In particular `sectionDualIso` preserves
the original evaluation, with no scalar or comparison witness.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite

universe u

namespace KltDP.Geometry.SchemeDualTensorNaturality

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance structureSectionsComm (X : Scheme.{u}) :
    ∀ U, IsMulCommutative (X.ringCatSheaf.val.obj U) :=
  fun U => by
    change IsMulCommutative (X.presheaf.obj U)
    exact ⟨⟨fun a b => mul_comm a b⟩⟩

local instance moduleTensor (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

local instance presheafTensor (X : Scheme.{u}) : MonoidalCategory X.PresheafOfModules :=
  PresheafOfModules.monoidalCategory (R := X.sheaf.val)

variable (X : Scheme.{u}) {M N : X.Modules}

/-- The actual presheaf evaluation commutes with the original precomposition map. -/
theorem presheafEvaluation_natural (f : M ⟶ N) :
    (f.val ⊗ 𝟙 (KltDP.SheafOfModules.dual X.ringCatSheaf N).val) ≫
        KltDP.SheafOfModules.evaluationPre X.sheaf.val X.ringCatSheaf.cond N =
      (𝟙 M.val ⊗ (sectionDualMap X f).val) ≫
        KltDP.SheafOfModules.evaluationPre X.sheaf.val X.ringCatSheaf.cond M := by
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m φ
  change KltDP.SheafOfModules.evalSection X.ringCatSheaf N U.unop φ (f.val.app U m) =
    KltDP.SheafOfModules.evalSection X.ringCatSheaf M U.unop
      ((_root_.SheafOfModules.overFunctor X.ringCatSheaf U.unop).map f ≫ φ) m
  exact (evalSection_precomp X f U.unop φ m).symm

set_option maxHeartbeats 800000 in
/-- The same identity for the existing evaluation on the actual sheaf tensor. -/
theorem tensorEvaluation_natural (f : M ⟶ N) :
    (f ⊗ 𝟙 (KltDP.SheafOfModules.dual X.ringCatSheaf N)) ≫
        KltDP.SheafOfModules.evaluation X.sheaf.val X.ringCatSheaf.cond N =
      (𝟙 M ⊗ sectionDualMap X f) ≫
        KltDP.SheafOfModules.evaluation X.sheaf.val X.ringCatSheaf.cond M := by
  rw [KltDP.SheafOfModules.evaluation, KltDP.SheafOfModules.evaluation]
  change (f ⊗ 𝟙 (KltDP.SheafOfModules.dual X.ringCatSheaf N)) ≫
      (PresheafOfModules.sheafTensorIsoSheafification X.sheaf.val X.ringCatSheaf.cond
        N (KltDP.SheafOfModules.dual X.ringCatSheaf N)).hom ≫
      KltDP.SheafOfModules.evaluationSheafified X.sheaf.val X.ringCatSheaf.cond N =
    (𝟙 M ⊗ sectionDualMap X f) ≫
      (PresheafOfModules.sheafTensorIsoSheafification X.sheaf.val X.ringCatSheaf.cond
        M (KltDP.SheafOfModules.dual X.ringCatSheaf M)).hom ≫
      KltDP.SheafOfModules.evaluationSheafified X.sheaf.val X.ringCatSheaf.cond M
  erw [schemeSheafTensorIsoSheafification_natural_assoc (X := X) f
      (𝟙 (KltDP.SheafOfModules.dual X.ringCatSheaf N)),
    schemeSheafTensorIsoSheafification_natural_assoc (X := X) (𝟙 M)
      (sectionDualMap X f)]
  rw [KltDP.SheafOfModules.evaluationSheafified_eq_sheafification_map,
    KltDP.SheafOfModules.evaluationSheafified_eq_sheafification_map]
  let T := PresheafOfModules.sheafTensorIsoSheafification X.sheaf.val X.ringCatSheaf.cond
    M (KltDP.SheafOfModules.dual X.ringCatSheaf N)
  let S := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)
  let C := PresheafOfModules.sheafificationForgetIso X.ringCatSheaf
    (_root_.SheafOfModules.unit X.ringCatSheaf)
  have h := congrArg (fun k => T.hom ≫ S.map k ≫ C.hom)
    (presheafEvaluation_natural X f)
  simpa only [Functor.map_comp, Category.assoc, _root_.SheafOfModules.id_val] using h

/-- The original contravariant dual isomorphism has the exact evaluation normalization. -/
theorem sectionDualIso_evaluation (e : M ≅ N) :
    (e.hom ⊗ (sectionDualIso X e).inv) ≫
        KltDP.SheafOfModules.evaluation X.sheaf.val X.ringCatSheaf.cond N =
      KltDP.SheafOfModules.evaluation X.sheaf.val X.ringCatSheaf.cond M := by
  have h : (e.hom ⊗ 𝟙 (KltDP.SheafOfModules.dual X.ringCatSheaf N)) ≫
      KltDP.SheafOfModules.evaluation X.sheaf.val X.ringCatSheaf.cond N =
    (𝟙 M ⊗ (sectionDualIso X e).hom) ≫
      KltDP.SheafOfModules.evaluation X.sheaf.val X.ringCatSheaf.cond M :=
    tensorEvaluation_natural X e.hom
  calc
    _ = (𝟙 M ⊗ (sectionDualIso X e).inv) ≫
        (e.hom ⊗ 𝟙 (KltDP.SheafOfModules.dual X.ringCatSheaf N)) ≫
        KltDP.SheafOfModules.evaluation X.sheaf.val X.ringCatSheaf.cond N := by
      simp only [← tensor_comp_assoc, Category.id_comp, Category.comp_id]
    _ = (𝟙 M ⊗ (sectionDualIso X e).inv) ≫ (𝟙 M ⊗ (sectionDualIso X e).hom) ≫
        KltDP.SheafOfModules.evaluation X.sheaf.val X.ringCatSheaf.cond M := by rw [h]
    _ = _ := by
      rw [← tensor_comp_assoc, Category.id_comp, Iso.inv_hom_id, tensor_id, Category.id_comp]

end KltDP.Geometry.SchemeDualTensorNaturality
