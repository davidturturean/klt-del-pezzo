import KltDP.Geometry.SchemeModulePullbackStructureLeft
import KltDP.Geometry.SchemeModuleStructureUnit

/-!
# Pullback of the original ideal-tensor inclusion

The inclusion is the actual module map into the structure sheaf, followed by
the original counit and left unitor. The original tensor pullback comparison
preserves it. An already normalized actual ideal comparison therefore gives
the corresponding normalized tensor comparison; no new tensor is constructed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance tensorInclusionModules (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

/-- Tensor an actual structure-module inclusion using the original chosen unit. -/
def schemeStructureTensorInclusion {X : Scheme.{u}} {I : X.Modules}
    (i : I ⟶ _root_.SheafOfModules.unit X.ringCatSheaf) (M : X.Modules) : I ⊗ M ⟶ M :=
  ((i ≫ (SchemeModuleStructureUnit.iso X).hom) ▷ M) ≫ (λ_ M).hom

theorem schemeStructureTensorInclusion_eq {X : Scheme.{u}} {I : X.Modules}
    (i : I ⟶ _root_.SheafOfModules.unit X.ringCatSheaf) (M : X.Modules) :
    schemeStructureTensorInclusion i M =
      (i ⊗ 𝟙 M) ≫ (schemeStructureTensorLeftIso M).hom := by
  simp only [schemeStructureTensorInclusion, SchemeModuleStructureUnit.iso,
    schemeStructureTensorLeftIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    tensorHom_id, tensorRight_map, comp_whiskerRight, Category.assoc]

/-- The original tensor comparison preserves the same original pulled inclusion. -/
@[reassoc] theorem schemeModulePullbackTensorIso_inclusion {X Y : Scheme.{u}}
    (f : Y ⟶ X) {I : X.Modules}
    (i : I ⟶ _root_.SheafOfModules.unit X.ringCatSheaf) (M : X.Modules) :
    (schemeModulePullbackTensorIso f I M).hom ≫
      schemeStructureTensorInclusion
        ((schemeModulePullback f).map i ≫ (schemeModulePullbackUnitIso f).hom)
        ((schemeModulePullback f).obj M) =
      (schemeModulePullback f).map (schemeStructureTensorInclusion i M) := by
  simp only [schemeStructureTensorInclusion_eq]
  exact schemeModulePullbackTensorIso_structure_inclusion f i M

/-- Tensoring original isomorphisms retains the actual map into the structure module. -/
@[reassoc] theorem tensorIso_structureInclusion {X : Scheme.{u}}
    {I J M N : X.Modules} (e : I ≅ J) (t : M ≅ N)
    (i : J ⟶ _root_.SheafOfModules.unit X.ringCatSheaf) :
    (tensorIso e t).hom ≫ schemeStructureTensorInclusion i N =
      schemeStructureTensorInclusion (e.hom ≫ i) M ≫ t.hom := by
  simp only [schemeStructureTensorInclusion_eq, tensorIso_hom, Category.assoc]
  rw [← tensor_comp_assoc, Category.comp_id, tensorHom_def, Category.assoc,
    schemeStructureTensorLeftIso_natural, tensorHom_id]

/-- An actual normalized ideal comparison induces the normalized original tensor diagram. -/
theorem schemeModulePullbackTensorIso_comparison_inclusion {X Y : Scheme.{u}}
    (f : Y ⟶ X) {I : X.Modules}
    (i : I ⟶ _root_.SheafOfModules.unit X.ringCatSheaf) (M : X.Modules)
    {J N : Y.Modules} (e : J ≅ (schemeModulePullback f).obj I)
    (t : (schemeModulePullback f).obj M ≅ N)
    (j : J ⟶ _root_.SheafOfModules.unit Y.ringCatSheaf)
    (he : e.hom ≫ ((schemeModulePullback f).map i ≫
      (schemeModulePullbackUnitIso f).hom) = j) :
    ((schemeModulePullbackTensorIso f I M) ≪≫ tensorIso e.symm t).hom ≫
        schemeStructureTensorInclusion j N =
      (schemeModulePullback f).map (schemeStructureTensorInclusion i M) ≫ t.hom := by
  have h : e.inv ≫ j =
      (schemeModulePullback f).map i ≫ (schemeModulePullbackUnitIso f).hom := by
    rw [← he, Iso.inv_hom_id_assoc]
  simp only [Iso.trans_hom, Category.assoc]
  rw [tensorIso_structureInclusion, Iso.symm_hom, h, ← Category.assoc,
    schemeModulePullbackTensorIso_inclusion]

end KltDP.Geometry
