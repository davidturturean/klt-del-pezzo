import KltDP.Geometry.KernelLinePullbackOffRange
import KltDP.Geometry.SchemeModuleUnitCoherence

/-!
# Normalized exceptional-ideal trivializations away from their support

The accepted complement frame has generator one. Its composite with the
original pulled kernel inclusion is therefore the identity. The original
pullback-composition and unit comparisons transport that identity along any
morphism missing the support. Thus the actual inclusion itself is an
isomorphism, which supplies the normalized foreign factors in a tower tensor.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusContactTowerCanonicalFactorOffRange

open KltDP.Geometry KltDP.Geometry.KernelLinePullbackOffRange

attribute [local instance] Types.instFunLike Types.instConcreteCategory

private theorem scalarEnd_one (X : Scheme.{u}) :
    schemeScalarEnd (Y := X) 1 = 𝟙 (_root_.SheafOfModules.unit X.ringCatSheaf) := by
  apply (_root_.SheafOfModules.unit X.ringCatSheaf).unitHomEquiv.injective
  apply (schemeModuleSectionsEquivTop (_root_.SheafOfModules.unit X.ringCatSheaf)).injective
  change (schemeScalarEnd (Y := X) 1).val.app (Opposite.op ⊤) (1 : Γ(X, ⊤)) = (1 : Γ(X, ⊤))
  rw [schemeScalarEnd_appTop, one_mul]

/-- The accepted equation-one frame inverts the original inclusion on the complement. -/
theorem kernelComplementInclusion_isIso {X Y : Scheme.{u}} (g : X ⟶ Y)
    [IsClosedImmersion g] :
    IsIso (pulledKernelInclusion g (rangeComplement g).ι) := by
  have h : (kernelLine_complement_unitIso g).hom ≫
      pulledKernelInclusion g (rangeComplement g).ι = 𝟙 _ := by
    simp only [kernelLine_complement_unitIso, Iso.trans_hom, asIso_hom, Category.assoc]
    rw [localKernelToGlobalPullbackIso_inclusion, schemeKernelGenerator_comp_ι, scalarEnd_one]
  exact IsIso.of_isIso_fac_left h

/-- The actual pulled structure-module inclusion respects the original composition isomorphism. -/
theorem pulledInclusion_comp {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
    {I : X.Modules} (i : I ⟶ _root_.SheafOfModules.unit X.ringCatSheaf) :
    (schemeModulePullbackCompIso g f).hom.app I ≫
        (schemeModulePullback (g ≫ f)).map i ≫
        (schemeModulePullbackUnitIso (g ≫ f)).hom =
      (schemeModulePullback g).map
        ((schemeModulePullback f).map i ≫ (schemeModulePullbackUnitIso f).hom) ≫
        (schemeModulePullbackUnitIso g).hom := by
  rw [← Category.assoc ((schemeModulePullbackCompIso g f).hom.app I),
    ← (schemeModulePullbackCompIso g f).hom.naturality i, Category.assoc,
    schemeModulePullbackCompIso_unit]
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc]

/-- Pulling an invertible original inclusion further retains that same normalized map. -/
theorem pulledInclusion_comp_isIso {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
    {I : X.Modules} (i : I ⟶ _root_.SheafOfModules.unit X.ringCatSheaf)
    [IsIso ((schemeModulePullback f).map i ≫ (schemeModulePullbackUnitIso f).hom)] :
    IsIso ((schemeModulePullback (g ≫ f)).map i ≫
      (schemeModulePullbackUnitIso (g ≫ f)).hom) :=
  IsIso.of_isIso_fac_left (pulledInclusion_comp f g i)

/-- Away from the actual closed support, the original pulled kernel inclusion itself is invertible. -/
theorem pulledKernelInclusion_isIso_of_disjoint {X Y Z : Scheme.{u}}
    (g : X ⟶ Y) [IsClosedImmersion g] (f : Z ⟶ Y)
    (hdisj : Disjoint (Set.range f.base) (Set.range g.base)) :
    IsIso (pulledKernelInclusion g f) := by
  have hsub : Set.range f.base ⊆ Set.range (rangeComplement g).ι.base := by
    rw [Scheme.Opens.range_ι]
    exact Set.disjoint_left.mp hdisj
  let l := IsOpenImmersion.lift (rangeComplement g).ι f hsub
  have hl : l ≫ (rangeComplement g).ι = f :=
    IsOpenImmersion.lift_fac _ _ _
  letI : IsIso ((schemeModulePullback (rangeComplement g).ι).map (schemeKernelIdealι g) ≫
      (schemeModulePullbackUnitIso (rangeComplement g).ι).hom) :=
    kernelComplementInclusion_isIso g
  rw [← hl]
  exact pulledInclusion_comp_isIso (rangeComplement g).ι l (schemeKernelIdealι g)

/-- The normalized trivialization uses exactly the original pulled inclusion as its hom. -/
def pulledKernelInclusionIso {X Y Z : Scheme.{u}}
    (g : X ⟶ Y) [IsClosedImmersion g] (f : Z ⟶ Y)
    (hdisj : Disjoint (Set.range f.base) (Set.range g.base)) :
    (schemeModulePullback f).obj (schemeKernelIdeal g) ≅
      _root_.SheafOfModules.unit Z.ringCatSheaf := by
  letI := pulledKernelInclusion_isIso_of_disjoint g f hdisj
  exact asIso (pulledKernelInclusion g f)

@[simp] theorem pulledKernelInclusionIso_hom {X Y Z : Scheme.{u}}
    (g : X ⟶ Y) [IsClosedImmersion g] (f : Z ⟶ Y)
    (hdisj : Disjoint (Set.range f.base) (Set.range g.base)) :
    (pulledKernelInclusionIso g f hdisj).hom = pulledKernelInclusion g f := rfl

end KltDP.Examples.FrobeniusContactTowerCanonicalFactorOffRange
