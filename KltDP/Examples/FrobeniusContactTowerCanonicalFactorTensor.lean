import KltDP.Geometry.SchemeModulePullbackTensorInclusion
import KltDP.Geometry.SchemeInvertibleSheafPullback

/-!
# Tensor composition for the original tower canonical factors

Use the existing tensor, structure action, and pullback comparison. The product
map below multiplies two actual maps into the structure module. The associator
identity proves that its action is the successive action of those same maps.
This is the tensor calculation used to compose the proved blowup factors.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Examples.FrobeniusContactTowerCanonicalFactorTensor

open KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance factorTensorModules (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

private theorem unitAction_natural {C : Type*} [Category C] [MonoidalCategory C]
    {I M N : C} (i : I ⟶ 𝟙_ C) (g : M ⟶ N) :
    I ◁ g ≫ i ▷ N ≫ (λ_ N).hom = i ▷ M ≫ (λ_ M).hom ≫ g := by
  rw [whisker_exchange_assoc, leftUnitor_naturality]

private theorem unitAction_product {C : Type*} [Category C] [MonoidalCategory C]
    {I J : C} (i : I ⟶ 𝟙_ C) (j : J ⟶ 𝟙_ C) (M : C) :
    (α_ I J M).inv ≫
        ((i ▷ J ≫ (λ_ J).hom ≫ j) ▷ M) ≫ (λ_ M).hom =
      I ◁ (j ▷ M ≫ (λ_ M).hom) ≫ i ▷ M ≫ (λ_ M).hom := by
  simp only [comp_whiskerRight, Category.assoc]
  rw [← associator_inv_naturality_left_assoc, leftUnitor_whiskerRight,
    Category.assoc, Iso.inv_hom_id_assoc]
  exact (unitAction_natural i (j ▷ M ≫ (λ_ M).hom)).symm

/-- The actual tensor of two already invertible module sheaves is again a line. -/
def tensorLine {X : Scheme.{u}} (L M : InvertibleSheaf X) : InvertibleSheaf X := by
  refine ⟨L.obj ⊗ M.obj, SchemeTensorPairing.isInvertible_of_isUnit_toSkeleton _ ?_⟩
  rw [Skeleton.toSkeleton_tensorObj]
  exact L.isUnit_toSkeleton.mul M.isUnit_toSkeleton

/-- Multiplication of the two original structure-module maps by the original action. -/
def productInclusion {X : Scheme.{u}} {I J : X.Modules}
    (i : I ⟶ _root_.SheafOfModules.unit X.ringCatSheaf)
    (j : J ⟶ _root_.SheafOfModules.unit X.ringCatSheaf) :
    I ⊗ J ⟶ _root_.SheafOfModules.unit X.ringCatSheaf :=
  schemeStructureTensorInclusion i J ≫ j

/-- Naturality of the same original ideal action. -/
@[reassoc] theorem inclusion_natural {X : Scheme.{u}} {I M N : X.Modules}
    (i : I ⟶ _root_.SheafOfModules.unit X.ringCatSheaf) (g : M ⟶ N) :
    I ◁ g ≫ schemeStructureTensorInclusion i N =
      schemeStructureTensorInclusion i M ≫ g :=
  unitAction_natural (i ≫ (SchemeModuleStructureUnit.iso X).hom) g

/-- The actual product inclusion acts as its two original factors, through the associator. -/
@[reassoc] theorem productInclusion_action {X : Scheme.{u}} {I J : X.Modules}
    (i : I ⟶ _root_.SheafOfModules.unit X.ringCatSheaf)
    (j : J ⟶ _root_.SheafOfModules.unit X.ringCatSheaf) (M : X.Modules) :
    (α_ I J M).inv ≫ schemeStructureTensorInclusion (productInclusion i j) M =
      I ◁ schemeStructureTensorInclusion j M ≫ schemeStructureTensorInclusion i M := by
  simpa only [productInclusion, schemeStructureTensorInclusion, Category.assoc] using
    unitAction_product (i ≫ (SchemeModuleStructureUnit.iso X).hom)
      (j ≫ (SchemeModuleStructureUnit.iso X).hom) M

/-- The original associator composes two actual tensor factors. -/
def composeFactorIso {X : Scheme.{u}} {P I M J N : X.Modules}
    (e : P ≅ I ⊗ M) (s : M ≅ J ⊗ N) : P ≅ (I ⊗ J) ⊗ N :=
  e ≪≫ tensorIso (Iso.refl I) s ≪≫ (α_ I J N).symm

/-- This composition retains both actual structure-module maps. -/
theorem composeFactorIso_comp {X : Scheme.{u}} {P I M J N : X.Modules}
    (e : P ≅ I ⊗ M) (s : M ≅ J ⊗ N)
    (i : I ⟶ _root_.SheafOfModules.unit X.ringCatSheaf)
    (j : J ⟶ _root_.SheafOfModules.unit X.ringCatSheaf) :
    (composeFactorIso e s).hom ≫
        schemeStructureTensorInclusion (productInclusion i j) N =
      e.hom ≫ schemeStructureTensorInclusion i M ≫
        s.hom ≫ schemeStructureTensorInclusion j N := by
  simp only [composeFactorIso, Iso.trans_hom, Iso.symm_hom, tensorIso_hom,
    Iso.refl_hom, id_tensorHom, Category.assoc]
  rw [productInclusion_action, ← MonoidalCategory.whiskerLeft_comp_assoc,
    inclusion_natural]

end KltDP.Examples.FrobeniusContactTowerCanonicalFactorTensor

