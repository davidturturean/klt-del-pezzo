import KltDP.Examples.FrobeniusStrictTransformInvertible
import KltDP.Geometry.PointBlowupExceptionalIdeal
import KltDP.Geometry.QuasicoherentIdealKernelIso
import KltDP.Geometry.TensorInvertibleSheaf
import KltDP.Geometry.SchemeStructureTensor
import KltDP.Compatibility.InvertibleQuasicoherent
import Mathlib.CategoryTheory.Functor.EpiMono

/-!
# The original exceptional-times-strict product on the entire successor stage

Tensor the original center-fiber and strict-transform kernel inclusions
and use the original monoidal unit comparison. Tensor cancellation for
the proved exceptional line makes this actual product morphism monic.

The existing quasicoherent-image ideal construction retains its original
component maps. The existing affine-kernel argument, here applied to a
monic morphism, identifies the actual product-image kernel with the actual
tensor line and preserves its inclusion. Its Picard class is consequently
the product of the two original ideal-line classes.

This is a whole-stage product bridge. Equality with the image of the
pulled-back previous strict ideal is a separate remaining comparison.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
  Opposite TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusStrictTransformProductKernel

open KltDP.Geometry
open FrobeniusBlowupContact FrobeniusBlowupChartIteration FrobeniusGlobalBlowupStages
open FrobeniusGlobalStrictTransform FrobeniusStrictTransformInvertible
open QuasicoherentImageIdeal

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance productSectionsComm (X : Scheme.{u}) :
    ∀ U, IsMulCommutative (X.ringCatSheaf.val.obj U) :=
  fun U => by
    change IsMulCommutative (X.presheaf.obj U)
    exact ⟨⟨fun a b => mul_comm a b⟩⟩

local instance productModulesMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

local instance productModulesSymmetric (X : Scheme.{u}) : SymmetricCategory X.Modules :=
  Scheme.Modules.symmetricCategory X

/-- The two tensor inverses give an equivalence with the original left-tensor functor. -/
private def lineTensorEquivalenceOfInverse {C : Type*} [Category C] [MonoidalCategory C]
    [SymmetricCategory C] {A D : C} (d : A ⊗ D ≅ 𝟙_ C) : C ≌ C :=
  CategoryTheory.Equivalence.mk (tensorLeft A) (tensorLeft D)
    ((tensorLeftTensor D A).symm ≪≫
      (tensoringLeft C).mapIso ((β_ D A) ≪≫ d) ≪≫ leftUnitorNatIso C).symm
    ((tensorLeftTensor A D).symm ≪≫
      (tensoringLeft C).mapIso d ≪≫ leftUnitorNatIso C)

/-- Tensoring on the left with an invertible object preserves monomorphisms. -/
private theorem tensorLeft_preservesMonomorphisms_of_inverse {C : Type*} [Category C]
    [MonoidalCategory C] [SymmetricCategory C] {A D : C} (d : A ⊗ D ≅ 𝟙_ C) :
    (tensorLeft A).PreservesMonomorphisms :=
  have adj : tensorLeft D ⊣ tensorLeft A := (lineTensorEquivalenceOfInverse d).symm.toAdjunction
  Functor.preservesMonomorphisms_of_adjunction adj

/-- The already proved tensor inverse of an actual line makes left tensoring preserve monos. -/
private theorem lineTensor_preservesMonomorphisms {X : Scheme.{u}}
    (L : InvertibleSheaf X) : (tensorLeft L.obj).PreservesMonomorphisms :=
  tensorLeft_preservesMonomorphisms_of_inverse
    (KltDP.SheafOfModules.tensorDualIsoUnit X.sheaf.val X.ringCatSheaf.cond L.obj :
      L.obj ⊗ KltDP.SheafOfModules.dual X.ringCatSheaf L.obj ≅ 𝟙_ X.Modules)

/-- Naturality of the right-unit multiplication transported through a unit isomorphism. -/
private theorem unitIso_rightUnitor_naturality {C : Type*} [Category C] [MonoidalCategory C]
    {O : C} (e : 𝟙_ C ≅ O) {M N : C} (f : M ⟶ N) :
    f ▷ O ≫ (N ◁ e.inv ≫ (ρ_ N).hom) = (M ◁ e.inv ≫ (ρ_ M).hom) ≫ f := by
  rw [← whisker_exchange_assoc, rightUnitor_naturality, Category.assoc]

/-- The existing structure-module multiplication is natural in the module. -/
private theorem structureTensorRightIso_naturality {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) :
    f ▷ _root_.SheafOfModules.unit X.ringCatSheaf ≫ (schemeStructureTensorRightIso N).hom =
      (schemeStructureTensorRightIso M).hom ≫ f := by
  let e : 𝟙_ X.Modules ≅ _root_.SheafOfModules.unit X.ringCatSheaf :=
    PresheafOfModules.sheafTensorUnitIso X.sheaf.val X.ringCatSheaf.cond
  simp only [schemeStructureTensorRightIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  exact unitIso_rightUnitor_naturality (C := X.Modules) e f

section OriginalImageKernel

variable {X : Scheme.{u}} {M : X.Modules} [M.IsQuasicoherent]
  (g : M ⟶ _root_.SheafOfModules.unit X.ringCatSheaf)

/-- The existing glued image ideal is killed by the original component image map. -/
private theorem image_comp_structure_zero :
    g ≫ structureToPushforwardUnit (ofMorphism g).gluedTo = 0 := by
  have hB : Opens.IsBasis (Set.range (fun U : X.affineOpens => U.1)) := by
    simpa only [Subtype.range_val] using isBasis_affine_open X
  apply (_root_.SheafOfModules.toSheaf X.ringCatSheaf).map_injective
  apply CategoryTheory.Sheaf.hom_ext _ _
  apply TopCat.Sheaf.hom_ext _ _ hB
  intro U
  apply ConcreteCategory.hom_ext
  intro s
  change g.val.app (op U.1) s ∈ RingHom.ker ((ofMorphism g).gluedTo.app U.1).hom
  rw [(ofMorphism g).ker_gluedTo_app U, ofMorphism_ideal]
  exact ⟨s, rfl⟩

/-- This is the factor of the original map through the original glued image kernel. -/
private def imageToKernel : M ⟶ schemeKernelIdeal (ofMorphism g).gluedTo :=
  kernel.lift (structureToPushforwardUnit (ofMorphism g).gluedTo) g
    (image_comp_structure_zero g)

private theorem imageToKernel_inclusion :
    imageToKernel g ≫ schemeKernelIdealι (ofMorphism g).gluedTo = g :=
  kernel.lift_ι _ _ _

private theorem imageToKernel_app_inclusion (U : X.Opens) (s : M.val.obj (op U)) :
    (schemeKernelIdealι (ofMorphism g).gluedTo).val.app (op U)
        ((imageToKernel g).val.app (op U) s) = g.val.app (op U) s :=
  congrArg (fun α : M ⟶ _root_.SheafOfModules.unit X.ringCatSheaf =>
    α.val.app (op U) s) (imageToKernel_inclusion g)

/-- Monicity and the exact original affine image ideals prove bijectivity. -/
private theorem imageToKernel_app_bijective [Mono g] (U : X.affineOpens) :
    Function.Bijective ((imageToKernel g).val.app (op U.1)) := by
  have hg : Function.Injective (g.val.app (op U.1)) := by
    apply (ModuleCat.mono_iff_injective _).mp
    change Mono ((_root_.SheafOfModules.evaluation X.ringCatSheaf (op U.1)).map g)
    infer_instance
  have hι : Function.Injective
      ((schemeKernelIdealι (ofMorphism g).gluedTo).val.app (op U.1)) := by
    apply (ModuleCat.mono_iff_injective _).mp
    change Mono ((_root_.SheafOfModules.evaluation X.ringCatSheaf (op U.1)).map
      (kernel.ι (structureToPushforwardUnit (ofMorphism g).gluedTo)))
    infer_instance
  constructor
  · intro s t hst
    apply hg
    simpa only [imageToKernel_app_inclusion] using
      congrArg ((schemeKernelIdealι (ofMorphism g).gluedTo).val.app (op U.1)) hst
  · intro y
    have hy : (schemeKernelIdealι (ofMorphism g).gluedTo).val.app (op U.1) y ∈
        RingHom.ker ((ofMorphism g).gluedTo.app U.1).hom := by
      change ((schemeKernelIdealι (ofMorphism g).gluedTo ≫
        structureToPushforwardUnit (ofMorphism g).gluedTo).val.app (op U.1)) y = 0
      rw [schemeKernelIdealι_comp]
      rfl
    rw [(ofMorphism g).ker_gluedTo_app U, ofMorphism_ideal] at hy
    obtain ⟨s, hs⟩ := hy
    refine ⟨s, hι ?_⟩
    exact (imageToKernel_app_inclusion g U.1 s).trans hs

/-- This is the existing affine-basis kernel comparison for an actual monic image map. -/
private def monicImageKernelIso [Mono g] : M ≅ schemeKernelIdeal (ofMorphism g).gluedTo := by
  have hB : Opens.IsBasis (Set.range (fun U : X.affineOpens => U.1)) := by
    simpa only [Subtype.range_val] using isBasis_affine_open X
  letI := KltDP.SheafOfModules.isIso_of_bijective_on_basis (imageToKernel g) hB
    (imageToKernel_app_bijective g)
  exact asIso (imageToKernel g)

private theorem monicImageKernelIso_inclusion [Mono g] :
    (monicImageKernelIso g).hom ≫ schemeKernelIdealι (ofMorphism g).gluedTo = g :=
  imageToKernel_inclusion g

end OriginalImageKernel

variable {k : Type u} [Field k]

local instance productKernelOriginIdealMaximal : (originPoint (k := k)).asIdeal.IsMaximal :=
  centerIdeal_isMaximal

/-- The literal center-fiber inclusion on the original whole successor stage. -/
abbrev stepExceptionalInclusion (n : ℕ) :=
  PointBlowupGluing.globalCenterFiberι
    ((projectiveProductInitial (k := k)).stage n).chart (originPoint (k := k))
    ((projectiveProductInitial (k := k)).stage n).center_closed

/-- Its original ambient ideal kernel, with invertibility proved from the actual Rees charts. -/
def stepExceptionalIdealLine (n : ℕ) :
    InvertibleSheaf (projectiveContactStage (k := k) (n + 1)) :=
  PointBlowupGluing.globalCenterFiberIdealLine
    ((projectiveProductInitial (k := k)).stage n).chart (originPoint (k := k))
    ((projectiveProductInitial (k := k)).stage n).center_closed

@[simp] theorem stepExceptionalIdealLine_obj (n : ℕ) :
    (stepExceptionalIdealLine (k := k) n).obj =
      schemeKernelIdeal (stepExceptionalInclusion n) := rfl

/-- The actual tensor of the two original whole-stage ideal kernels is an actual line. -/
def strictExceptionalTensorLine (n m : ℕ) :
    InvertibleSheaf (projectiveContactStage (k := k) (n + 1)) := by
  refine ⟨(stepExceptionalIdealLine n).obj ⊗ (strictKernelLine (n + 1) m).obj,
    SchemeTensorPairing.isInvertible_of_isUnit_toSkeleton _ ?_⟩
  rw [Skeleton.toSkeleton_tensorObj]
  exact (stepExceptionalIdealLine n).isUnit_toSkeleton.mul
    (strictKernelLine (n + 1) m).isUnit_toSkeleton

/-- Multiply the two original ideal inclusions using the original structure-sheaf unit. -/
def strictExceptionalProduct (n m : ℕ) :
    (strictExceptionalTensorLine (k := k) n m).obj ⟶
      _root_.SheafOfModules.unit (projectiveContactStage (k := k) (n + 1)).ringCatSheaf :=
  (schemeKernelIdealι (stepExceptionalInclusion n) ⊗
    schemeKernelIdealι (strictTransformι (n + 1) (m + (n + 1)))) ≫
    (schemeStructureTensorRightIso
      (_root_.SheafOfModules.unit (projectiveContactStage (k := k) (n + 1)).ringCatSheaf)).hom

/-- Tensor cancellation for the proved exceptional line makes the actual product injective. -/
theorem strictExceptionalProduct_mono (n m : ℕ) :
    Mono (strictExceptionalProduct (k := k) n m) := by
  letI := lineTensor_preservesMonomorphisms (stepExceptionalIdealLine (k := k) n)
  rw [strictExceptionalProduct, tensorHom_def', Category.assoc,
    structureTensorRightIso_naturality]
  haveI : Mono (schemeKernelIdealι (strictTransformι (k := k) (n + 1) (m + (n + 1)))) := by
    unfold schemeKernelIdealι
    infer_instance
  haveI : Mono (schemeKernelIdealι (stepExceptionalInclusion (k := k) n)) := by
    unfold schemeKernelIdealι
    infer_instance
  haveI : Mono ((stepExceptionalIdealLine (k := k) n).obj ◁
      schemeKernelIdealι (strictTransformι (n + 1) (m + (n + 1)))) :=
    inferInstanceAs (Mono ((tensorLeft (stepExceptionalIdealLine (k := k) n).obj).map
      (schemeKernelIdealι (strictTransformι (n + 1) (m + (n + 1))))))
  infer_instance

/-- The actual tensor line is invertible, hence locally free and quasicoherent. -/
instance strictExceptionalTensorLine_isInvertible (n m : ℕ) :
    KltDP.SheafOfModules.IsInvertible
      (R := (projectiveContactStage (k := k) (n + 1)).ringCatSheaf)
      (strictExceptionalTensorLine n m).obj :=
  (strictExceptionalTensorLine n m).property

instance strictExceptionalTensorLine_isLocallyFree (n m : ℕ) :
    (strictExceptionalTensorLine (k := k) n m).obj.IsLocallyFree :=
  KltDP.SheafOfModules.IsInvertible.isLocallyFree (strictExceptionalTensorLine (k := k) n m).obj

instance strictExceptionalTensorLine_isQuasicoherent (n m : ℕ) :
    (strictExceptionalTensorLine (k := k) n m).obj.IsQuasicoherent :=
  KltDP.SheafOfModules.locallyFree_isQuasicoherent (strictExceptionalTensorLine (k := k) n m).obj

/-- The actual global image ideal of that original product morphism. -/
def strictExceptionalProductIdeal (n m : ℕ) :
    (projectiveContactStage (k := k) (n + 1)).IdealSheafData :=
  ofMorphism (strictExceptionalProduct n m)

/-- Its affine ideals are literally the component images of the original multiplication. -/
theorem strictExceptionalProductIdeal_ideal (n m : ℕ)
    (U : (projectiveContactStage (k := k) (n + 1)).affineOpens) :
    (strictExceptionalProductIdeal n m).ideal U =
      LinearMap.range ((strictExceptionalProduct n m).val.app (op U.1)).hom :=
  ofMorphism_ideal _ U

/-- The tensor line is the actual structural kernel of the actual product-image closed subscheme. -/
def strictExceptionalProductKernelIso (n m : ℕ) :
    (strictExceptionalTensorLine (k := k) n m).obj ≅
      schemeKernelIdeal (strictExceptionalProductIdeal n m).gluedTo := by
  letI := strictExceptionalProduct_mono (k := k) n m
  exact monicImageKernelIso (strictExceptionalProduct n m)

/-- This isomorphism retains the original multiplication as its actual ambient inclusion. -/
theorem strictExceptionalProductKernelIso_inclusion (n m : ℕ) :
    (strictExceptionalProductKernelIso (k := k) n m).hom ≫
        schemeKernelIdealι (strictExceptionalProductIdeal n m).gluedTo =
      strictExceptionalProduct n m := by
  letI := strictExceptionalProduct_mono (k := k) n m
  exact monicImageKernelIso_inclusion (strictExceptionalProduct n m)

/-- The line has literally the actual product-image kernel as its object. -/
def strictExceptionalProductIdealLine (n m : ℕ) :
    InvertibleSheaf (projectiveContactStage (k := k) (n + 1)) :=
  InvertibleSheaf.ofIso (strictExceptionalTensorLine n m)
    (strictExceptionalProductKernelIso n m)

/-- The actual whole-stage product-image ideal has the product of the two original Picard classes. -/
theorem strictExceptionalProductIdeal_picard (n m : ℕ) :
    (strictExceptionalProductIdealLine (k := k) n m).toPic =
      (stepExceptionalIdealLine n).toPic * (strictKernelLine (n + 1) m).toPic := by
  letI := Scheme.Modules.monoidalCategory (projectiveContactStage (k := k) (n + 1))
  apply Units.ext
  change ((strictExceptionalProductIdealLine (k := k) n m).toPic :
      Skeleton (projectiveContactStage (k := k) (n + 1)).Modules) =
    ((stepExceptionalIdealLine (k := k) n).toPic :
      Skeleton (projectiveContactStage (k := k) (n + 1)).Modules) *
      ((strictKernelLine (k := k) (n + 1) m).toPic :
        Skeleton (projectiveContactStage (k := k) (n + 1)).Modules)
  rw [InvertibleSheaf.toPic_val, InvertibleSheaf.toPic_val,
    InvertibleSheaf.toPic_val, ← Skeleton.toSkeleton_tensorObj]
  exact Quotient.sound ⟨(strictExceptionalProductKernelIso n m).symm⟩

end KltDP.Examples.FrobeniusStrictTransformProductKernel
