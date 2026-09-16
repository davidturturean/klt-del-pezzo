import KltDP.Examples.FrobeniusStrictTransformProductKernel
import KltDP.Examples.FrobeniusStrictTransformStepPuncture
import KltDP.Geometry.SchemeModulePullbackTensorMultiplication
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

/-!
# The original total and exceptional-times-strict maps on the center complement

On the actual complement of the current blowup center, the original exceptional
kernel has its already proved frame with inclusion one. The chosen pullback
tensor comparison preserves the actual multiplication, so tensoring this frame
compares the original product line with the original successor strict kernel.

Composing with the original strict-step comparison gives an isomorphism between
the literal pullback of the previous strict ideal and the literal exceptional
times successor strict tensor line, preserving their original ambient maps.
All fields and all stage/contact indices, including zero, remain unrestricted.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite

universe u

namespace KltDP.Examples.FrobeniusStrictTransformProductPuncture

open KltDP.Geometry
open FrobeniusBlowupContact FrobeniusBlowupChartIteration FrobeniusGlobalBlowupStages
open FrobeniusGlobalStrictTransform FrobeniusStrictTransformInvertible
open FrobeniusStrictTransformProductKernel FrobeniusStrictTransformStepPuncture

attribute [local instance] Types.instFunLike Types.instConcreteCategory

local instance punctureModuleTensor (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

/-- Multiplication by the actual unit function is the identity of the structure module. -/
private theorem scalar_one (X : Scheme.{u}) :
    schemeScalarEnd (Y := X) (1 : Γ(X, ⊤)) =
      𝟙 (_root_.SheafOfModules.unit X.ringCatSheaf) := by
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  let s' : Γ(X, V.unop) := s
  change s' * X.presheaf.map (homOfLE (show V.unop ≤ ⊤ from le_top)).op 1 = s'
  rw [(X.presheaf.map (homOfLE (show V.unop ≤ ⊤ from le_top)).op).hom.map_one, mul_one]

/-- The left-unit multiplication transported through an abstract unit isomorphism. -/
private def unitTensorLeftIso {C : Type*} [Category C] [MonoidalCategory C] {O : C}
    (e : 𝟙_ C ≅ O) (M : C) : O ⊗ M ≅ M :=
  (tensorRight M).mapIso e.symm ≪≫ λ_ M

private theorem unitTensorLeftIso_naturality {C : Type*} [Category C] [MonoidalCategory C]
    {O : C} (e : 𝟙_ C ≅ O) {M N : C} (g : M ⟶ N) :
    O ◁ g ≫ (unitTensorLeftIso e N).hom = (unitTensorLeftIso e M).hom ≫ g := by
  simp only [unitTensorLeftIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    tensorRight_map]
  rw [whisker_exchange_assoc, leftUnitor_naturality, Category.assoc]

/-- Both unitors give the same multiplication of the abstract unit object. -/
private theorem unitTensorLeftIso_eq_right {C : Type*} [Category C] [MonoidalCategory C]
    {O : C} (e : 𝟙_ C ≅ O) :
    O ◁ e.inv ≫ (ρ_ O).hom = (unitTensorLeftIso e O).hom := by
  simp only [unitTensorLeftIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    tensorRight_map]
  apply (cancel_mono e.inv).mp
  rw [Category.assoc, Category.assoc, ← rightUnitor_naturality, ← leftUnitor_naturality,
    whisker_exchange_assoc, unitors_equal]

/-- The existing structure-module comparison followed by the original left unitor. -/
private def structureTensorLeftIso {X : Scheme.{u}} (M : X.Modules) :
    _root_.SheafOfModules.unit X.ringCatSheaf ⊗ M ≅ M :=
  let e : 𝟙_ X.Modules ≅ _root_.SheafOfModules.unit X.ringCatSheaf :=
    PresheafOfModules.sheafTensorUnitIso X.sheaf.val X.ringCatSheaf.cond
  unitTensorLeftIso e M

private theorem structureTensorLeftIso_naturality {X : Scheme.{u}} {M N : X.Modules}
    (g : M ⟶ N) :
    _root_.SheafOfModules.unit X.ringCatSheaf ◁ g ≫
        (structureTensorLeftIso N).hom = (structureTensorLeftIso M).hom ≫ g :=
  unitTensorLeftIso_naturality _ g

/-- Both original unitors give the same multiplication of the actual structure module. -/
private theorem structure_mul_eq_left (X : Scheme.{u}) :
    (schemeStructureTensorRightIso (_root_.SheafOfModules.unit X.ringCatSheaf)).hom =
      (structureTensorLeftIso (_root_.SheafOfModules.unit X.ringCatSheaf)).hom := by
  let e : 𝟙_ X.Modules ≅ _root_.SheafOfModules.unit X.ringCatSheaf :=
    PresheafOfModules.sheafTensorUnitIso X.sheaf.val X.ringCatSheaf.cond
  simp only [schemeStructureTensorRightIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  exact unitTensorLeftIso_eq_right (C := X.Modules) e

variable {k : Type u} [Field k]

local instance punctureOriginIdealMaximal : (originPoint (k := k)).asIdeal.IsMaximal :=
  centerIdeal_isMaximal

/-- The proved exceptional frame on the actual one-step center complement. -/
def stepExceptionalPunctureFrame (n : ℕ) :
    _root_.SheafOfModules.unit (nextPuncture (k := k) n).toScheme.ringCatSheaf ≅
      (schemeModulePullback (nextPuncture n).ι).obj
        (schemeKernelIdeal (stepExceptionalInclusion n)) :=
  PointBlowupGluing.globalCenterFiberComplementFrame
    ((projectiveProductInitial (k := k)).stage n).chart (originPoint (k := k))
    ((projectiveProductInitial (k := k)).stage n).center_closed

/-- This is the original fiber frame, normalized by the actual ambient inclusion. -/
theorem stepExceptionalPunctureFrame_inclusion (n : ℕ) :
    (stepExceptionalPunctureFrame (k := k) n).hom ≫
      pulledKernelInclusion (stepExceptionalInclusion n) (nextPuncture n).ι = 𝟙 _ := by
  simpa only [scalar_one] using
    PointBlowupGluing.globalCenterFiberComplementFrame_inclusion
      ((projectiveProductInitial (k := k)).stage n).chart (originPoint (k := k))
      ((projectiveProductInitial (k := k)).stage n).center_closed

/-- Its inverse is literally the original pulled exceptional inclusion. -/
theorem stepExceptionalPunctureFrame_inv (n : ℕ) :
    (stepExceptionalPunctureFrame (k := k) n).inv =
      pulledKernelInclusion (stepExceptionalInclusion n) (nextPuncture n).ι := by
  apply (cancel_epi (stepExceptionalPunctureFrame (k := k) n).hom).mp
  rw [Iso.hom_inv_id, stepExceptionalPunctureFrame_inclusion]

/-- The actual exceptional-times-strict tensor line restricts to the actual strict kernel. -/
def strictExceptionalPunctureIso (n m : ℕ) :
    (schemeModulePullback (nextPuncture (k := k) n).ι).obj
        (strictExceptionalTensorLine n m).obj ≅
      (schemeModulePullback (nextPuncture n).ι).obj
        (schemeKernelIdeal (strictTransformι (n + 1) (m + (n + 1)))) :=
  schemeModulePullbackTensorIso (nextPuncture n).ι
      (schemeKernelIdeal (stepExceptionalInclusion n))
      (schemeKernelIdeal (strictTransformι (n + 1) (m + (n + 1)))) ≪≫
    tensorIso (stepExceptionalPunctureFrame n).symm (Iso.refl _) ≪≫
    structureTensorLeftIso
      ((schemeModulePullback (nextPuncture n).ι).obj
        (schemeKernelIdeal (strictTransformι (n + 1) (m + (n + 1)))))

/-- The comparison preserves the actual original product and strict inclusions. -/
theorem strictExceptionalPunctureIso_inclusion (n m : ℕ) :
    (strictExceptionalPunctureIso (k := k) n m).hom ≫
      pulledKernelInclusion (strictTransformι (n + 1) (m + (n + 1))) (nextPuncture n).ι =
    (schemeModulePullback (nextPuncture n).ι).map (strictExceptionalProduct n m) ≫
      (schemeModulePullbackUnitIso (nextPuncture n).ι).hom := by
  rw [strictExceptionalPunctureIso, Iso.trans_hom, Iso.trans_hom, tensorIso_hom, Iso.symm_hom,
    Iso.refl_hom, pulledKernelInclusion, Category.assoc, Category.assoc,
    ← structureTensorLeftIso_naturality, tensorHom_id, ← tensorHom_def_assoc,
    ← structure_mul_eq_left, stepExceptionalPunctureFrame_inv]
  exact schemeModulePullbackTensorIso_product (nextPuncture n).ι
    (schemeKernelIdealι (stepExceptionalInclusion n))
    (schemeKernelIdealι (strictTransformι (n + 1) (m + (n + 1))))

/-- On the original current-center complement, the literal pulled previous ideal
is the literal tensor of the original exceptional and successor strict ideals. -/
def strictTotalProductPunctureIso (n m : ℕ) :
    (schemeModulePullback (nextPuncture (k := k) n).ι).obj
      ((schemeModulePullback ((projectiveProductInitial (k := k)).stepProjection n)).obj
        (schemeKernelIdeal (strictTransformι n ((m + 1) + n)))) ≅
      (schemeModulePullback (nextPuncture n).ι).obj
        (strictExceptionalTensorLine n m).obj :=
  strictPulledPreviousPunctureIso n m ≪≫ (strictExceptionalPunctureIso n m).symm

/-- The original total-transform and product maps agree through this actual isomorphism. -/
theorem strictTotalProductPunctureIso_inclusion (n m : ℕ) :
    (strictTotalProductPunctureIso (k := k) n m).hom ≫
      (schemeModulePullback (nextPuncture n).ι).map (strictExceptionalProduct n m) ≫
      (schemeModulePullbackUnitIso (nextPuncture n).ι).hom =
    (schemeModulePullback (nextPuncture n).ι).map
      (pulledKernelInclusion (strictTransformι n ((m + 1) + n))
        ((projectiveProductInitial (k := k)).stepProjection n)) ≫
      (schemeModulePullbackUnitIso (nextPuncture n).ι).hom := by
  rw [strictTotalProductPunctureIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    ← strictExceptionalPunctureIso_inclusion, Iso.inv_hom_id_assoc,
    strictPulledPreviousPunctureIso_inclusion]

end KltDP.Examples.FrobeniusStrictTransformProductPuncture
