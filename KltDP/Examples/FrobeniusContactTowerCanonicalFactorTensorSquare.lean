import KltDP.Geometry.SchemeModulePullbackTensorInclusion

/-!
# A normalized comparison between two original pulled tensor inclusions

Both pullback tensor comparisons and both structure actions are the existing
ones. A comparison of the actual pulled ideal inclusions and the actual top
maps gives the corresponding whole tensor square. This is the direct diagram
calculation used by the original cluster factor.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Examples.FrobeniusContactTowerCanonicalFactorTensorSquare

open KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance factorTensorSquareModules (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

@[reassoc] private theorem pullbackTensorIso_inv_inclusion {X Y : Scheme.{u}}
    (f : Y ⟶ X) {I : X.Modules}
    (i : I ⟶ _root_.SheafOfModules.unit X.ringCatSheaf) (M : X.Modules) :
    (schemeModulePullbackTensorIso f I M).inv ≫
        (schemeModulePullback f).map (schemeStructureTensorInclusion i M) =
      schemeStructureTensorInclusion
        ((schemeModulePullback f).map i ≫ (schemeModulePullbackUnitIso f).hom)
        ((schemeModulePullback f).obj M) := by
  rw [← schemeModulePullbackTensorIso_inclusion f i M, Iso.inv_hom_id_assoc]

/-- Compare the two original pulled tensors through the original tensor pullback isomorphisms. -/
def pullbackTensorSquareIso {X Y Z : Scheme.{u}} (f : Z ⟶ X) (g : Z ⟶ Y)
    {I M : X.Modules} {J N : Y.Modules}
    (e : (schemeModulePullback f).obj I ≅ (schemeModulePullback g).obj J)
    (t : (schemeModulePullback f).obj M ≅ (schemeModulePullback g).obj N) :
    (schemeModulePullback f).obj (I ⊗ M) ≅ (schemeModulePullback g).obj (J ⊗ N) :=
  schemeModulePullbackTensorIso f I M ≪≫ tensorIso e t ≪≫
    (schemeModulePullbackTensorIso g J N).symm

/-- The original tensor comparison retains both original target maps. -/
theorem pullbackTensorSquareIso_comp {X Y Z : Scheme.{u}} (f : Z ⟶ X) (g : Z ⟶ Y)
    {I M : X.Modules} {J N : Y.Modules}
    (e : (schemeModulePullback f).obj I ≅ (schemeModulePullback g).obj J)
    (t : (schemeModulePullback f).obj M ≅ (schemeModulePullback g).obj N)
    (i : I ⟶ _root_.SheafOfModules.unit X.ringCatSheaf)
    (j : J ⟶ _root_.SheafOfModules.unit Y.ringCatSheaf)
    (he : e.hom ≫ (schemeModulePullback g).map j ≫ (schemeModulePullbackUnitIso g).hom =
      (schemeModulePullback f).map i ≫ (schemeModulePullbackUnitIso f).hom)
    {Q : Z.Modules} (v : (schemeModulePullback g).obj N ⟶ Q)
    (w : (schemeModulePullback f).obj M ⟶ Q) (ht : t.hom ≫ v = w) :
    (pullbackTensorSquareIso f g e t).hom ≫
        (schemeModulePullback g).map (schemeStructureTensorInclusion j N) ≫ v =
      (schemeModulePullback f).map (schemeStructureTensorInclusion i M) ≫ w := by
  simp only [pullbackTensorSquareIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [pullbackTensorIso_inv_inclusion_assoc, tensorIso_structureInclusion_assoc,
    he, ht, schemeModulePullbackTensorIso_inclusion_assoc]

end KltDP.Examples.FrobeniusContactTowerCanonicalFactorTensorSquare
