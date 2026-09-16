import KltDP.Geometry.TransitionUnitMultiplication
import KltDP.Geometry.TransitionUnitPicard
import KltDP.Compatibility.SheafificationOnCover

/-!
# Tensor products of actual transition-unit module sheaves

The original componentwise section product has local tensor coordinates
a ⊗ b ↦ ab. The existing covering criterion therefore makes its
sheafification an isomorphism. The established comparison between the
actual sheaf tensor and the sheafified presheaf tensor gives the desired
module-sheaf isomorphism, and hence multiplication of actual Picard classes.

This reuses the project CartierTensorProduct construction pattern, with
the existing transition-chart equivalences on every chart subopen. It
does not identify global sections of a sheaf tensor with the tensor of
global sections.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite TopologicalSpace
open scoped TensorProduct

universe u

namespace KltDP.Geometry.TransitionUnitGluing

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (X : Scheme.{u}) {ι : Type u} (U : ι → X.Opens)
  (g h : ∀ i j : ι, Γ(X, U i ⊓ U j)ˣ)

local instance structureSectionCommRing (W : (X.Opens)ᵒᵖ) :
    CommRing (X.ringCatSheaf.val.obj W) :=
  inferInstanceAs (CommRing (X.presheaf.obj W))

local instance structurePresheafMonoidal :
    MonoidalCategory (_root_.PresheafOfModules.{u} X.ringCatSheaf.val) :=
  _root_.PresheafOfModules.monoidalCategory (R := X.presheaf)

/-- In the original chart coordinates, the section product is ordinary multiplication. -/
theorem sectionMul_trivialization (hg : IsCocycle X U g) (hh : IsCocycle X U h)
    (i : ι) {W : X.Opens} (hWi : W ≤ U i)
    (s : sections X U g W) (t : sections X U h W) :
    trivialization X U (productUnits X U g h) (productUnits_isCocycle X U g h hg hh)
        i hWi (sectionMul X U g h W s t) =
      trivialization X U g hg i hWi s * trivialization X U h hh i hWi t := by
  rw [trivialization_apply, sectionMul_val, map_mul, trivialization_apply,
    trivialization_apply]

/-- The actual tensor multiplication component is bijective on each chart subopen. -/
theorem multiplicationApp_bijective_on_chart
    (hg : IsCocycle X U g) (hh : IsCocycle X U h)
    (i : ι) {W : X.Opens} (hWi : W ≤ U i) :
    Function.Bijective (multiplicationApp X U g h W) := by
  let eG := trivialization X U g hg i hWi
  let eH := trivialization X U h hh i hWi
  let eP := trivialization X U (productUnits X U g h)
    (productUnits_isCocycle X U g h hg hh) i hWi
  let e := TensorProduct.congr eG eH ≪≫ₗ
    TensorProduct.lid Γ(X, W) Γ(X, W) ≪≫ₗ eP.symm
  have he : (multiplicationApp X U g h W).hom = e.toLinearMap := by
    apply TensorProduct.ext'
    intro s t
    change sectionMul X U g h W s t = e (s ⊗ₜ t)
    apply eP.injective
    simp only [e, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
      TensorProduct.lid_tmul, smul_eq_mul, LinearEquiv.apply_symm_apply]
    exact sectionMul_trivialization X U g h hg hh i hWi s t
  change Function.Bijective (multiplicationApp X U g h W).hom
  rw [he]
  exact e.bijective

/-- Sheafification inverts the actual product map on a covering cocycle atlas. -/
theorem multiplication_mem_sheafificationW
    (hg : IsCocycle X U g) (hh : IsCocycle X U h) (hU : (⨆ i, U i) = ⊤) :
    PresheafOfModules.sheafificationW (𝟙 X.ringCatSheaf.val)
      (multiplication X U g h) := by
  apply PresheafOfModules.sheafificationW_of_bijective_on_coversTop
    (multiplication X U g h) U (opens_coversTop X U hU)
  intro i W f
  exact multiplicationApp_bijective_on_chart X U g h hg hh i f.le

/-- The sheafified actual section product, followed by the original counit comparison. -/
def multiplicationSheafified :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).obj
        ((moduleSheaf X U g).val ⊗ (moduleSheaf X U h).val) ⟶
      moduleSheaf X U (productUnits X U g h) :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).map
      (multiplication X U g h) ≫
    (PresheafOfModules.sheafificationForgetIso X.ringCatSheaf
      (moduleSheaf X U (productUnits X U g h))).hom

/-- The actual sheafified section product is an isomorphism. -/
theorem multiplicationSheafified_isIso
    (hg : IsCocycle X U g) (hh : IsCocycle X U h) (hU : (⨆ i, U i) = ⊤) :
    IsIso (multiplicationSheafified X U g h) := by
  haveI : IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).map
      (multiplication X U g h)) :=
    (PresheafOfModules.sheafificationW_iff (𝟙 X.ringCatSheaf.val)
      (multiplication X U g h)).mp (multiplication_mem_sheafificationW X U g h hg hh hU)
  unfold multiplicationSheafified
  infer_instance

/-- Multiplication on the actual tensor of the two module sheaves. -/
def tensorMultiplication :
    letI := Scheme.Modules.monoidalCategory X
    moduleSheaf X U g ⊗ moduleSheaf X U h ⟶ moduleSheaf X U (productUnits X U g h) := by
  letI := Scheme.Modules.monoidalCategory X
  exact (PresheafOfModules.sheafTensorIsoSheafification X.sheaf.val
    X.ringCatSheaf.cond (moduleSheaf X U g) (moduleSheaf X U h)).hom ≫
      multiplicationSheafified X U g h

/-- The actual sheaf tensor has the product transition cocycle. -/
def tensorIso (hg : IsCocycle X U g) (hh : IsCocycle X U h) (hU : (⨆ i, U i) = ⊤) :
    letI := Scheme.Modules.monoidalCategory X
    moduleSheaf X U g ⊗ moduleSheaf X U h ≅ moduleSheaf X U (productUnits X U g h) := by
  letI := Scheme.Modules.monoidalCategory X
  letI := multiplicationSheafified_isIso X U g h hg hh hU
  exact PresheafOfModules.sheafTensorIsoSheafification X.sheaf.val
    X.ringCatSheaf.cond (moduleSheaf X U g) (moduleSheaf X U h) ≪≫
      asIso (multiplicationSheafified X U g h)

/-- The tensor isomorphism retains the original multiplication morphism. -/
@[simp]
theorem tensorIso_hom (hg : IsCocycle X U g) (hh : IsCocycle X U h)
    (hU : (⨆ i, U i) = ⊤) :
    letI := Scheme.Modules.monoidalCategory X
    (tensorIso X U g h hg hh hU).hom = tensorMultiplication X U g h := rfl

/-- Product transition units give the product in the actual scheme Picard group. -/
theorem picardClass_productUnits
    (hg : IsCocycle X U g) (hh : IsCocycle X U h) (hU : (⨆ i, U i) = ⊤) :
    picardClass X U (productUnits X U g h) (productUnits_isCocycle X U g h hg hh) hU =
      picardClass X U g hg hU * picardClass X U h hh hU := by
  letI := Scheme.Modules.monoidalCategory X
  apply Units.ext
  change (picardClass X U (productUnits X U g h)
      (productUnits_isCocycle X U g h hg hh) hU : Skeleton X.Modules) =
    (picardClass X U g hg hU : Skeleton X.Modules) *
      (picardClass X U h hh hU : Skeleton X.Modules)
  rw [picardClass_val, picardClass_val, picardClass_val, ← Skeleton.toSkeleton_tensorObj]
  exact Quotient.sound ⟨(tensorIso X U g h hg hh hU).symm⟩

end KltDP.Geometry.TransitionUnitGluing
