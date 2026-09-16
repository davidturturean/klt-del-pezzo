import KltDP.Examples.FrobeniusStrictTransformTotalProduct
import KltDP.Geometry.SchemeInvertibleSheafPullback

/-!
# The original one-step strict-transform relation in the actual Picard group

The whole-stage comparison identifies the literal pulled previous ideal with
the actual product-image kernel and preserves its ambient inclusion. The
existing Picard pullback and product-kernel class formula then give the
one-step class relation. Inverting the original ideal classes gives the
strict-curve class as the pulled previous curve class minus the exceptional
class. All classes belong to the original schemes' Picard groups.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u

namespace KltDP.Examples.FrobeniusStrictTransformPicardStep

open KltDP.Geometry
open FrobeniusGlobalBlowupStages FrobeniusGlobalStrictTransform
open FrobeniusStrictTransformInvertible FrobeniusStrictTransformProductKernel
open FrobeniusStrictTransformTotalProduct

local instance strictPicardStepModuleTensor (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

variable {k : Type u} [Field k]

/-- The previous original strict ideal pulled back by the original one-step blowdown. -/
def strictPulledPreviousIdealLine (n m : ℕ) :
    InvertibleSheaf (projectiveContactStage (k := k) (n + 1)) :=
  pullbackInvertibleSheaf ((projectiveProductInitial (k := k)).stepProjection n)
    (strictKernelLine n (m + 1))

/-- The original pulled ideal is the structural kernel of the original product-image subscheme. -/
def strictPulledPreviousProductKernelIso (n m : ℕ) :
    (strictPulledPreviousIdealLine (k := k) n m).obj ≅
      schemeKernelIdeal (strictExceptionalProductIdeal n m).gluedTo :=
  strictTotalProductIso n m ≪≫ strictExceptionalProductKernelIso n m

/-- The comparison preserves the original structural kernel inclusion and pulled ideal map. -/
@[reassoc] theorem strictPulledPreviousProductKernelIso_inclusion (n m : ℕ) :
    (strictPulledPreviousProductKernelIso (k := k) n m).hom ≫
        schemeKernelIdealι (strictExceptionalProductIdeal n m).gluedTo =
      pulledKernelInclusion (strictTransformι n ((m + 1) + n))
        ((projectiveProductInitial (k := k)).stepProjection n) := by
  rw [strictPulledPreviousProductKernelIso, Iso.trans_hom, Category.assoc,
    strictExceptionalProductKernelIso_inclusion, strictTotalProductIso_inclusion]

/-- The actual pulled line has the class of the actual product-image ideal line. -/
theorem strictPulledPreviousIdealLine_picard_eq_productIdeal (n m : ℕ) :
    (strictPulledPreviousIdealLine (k := k) n m).toPic =
      (strictExceptionalProductIdealLine n m).toPic := by
  letI := Scheme.Modules.monoidalCategory (projectiveContactStage (k := k) (n + 1))
  apply Units.ext
  change ((strictPulledPreviousIdealLine (k := k) n m).toPic :
      Skeleton (projectiveContactStage (k := k) (n + 1)).Modules) =
    ((strictExceptionalProductIdealLine (k := k) n m).toPic :
      Skeleton (projectiveContactStage (k := k) (n + 1)).Modules)
  rw [InvertibleSheaf.toPic_val, InvertibleSheaf.toPic_val]
  exact Quotient.sound ⟨strictPulledPreviousProductKernelIso n m⟩

/-- Pullback of the previous original strict-ideal class is exceptional times successor strict. -/
theorem strictKernelLine_picard_step (n m : ℕ) :
    schemePicardPullbackHom ((projectiveProductInitial (k := k)).stepProjection n)
        (strictKernelLine n (m + 1)).toPic =
      (stepExceptionalIdealLine n).toPic * (strictKernelLine (n + 1) m).toPic := by
  rw [schemePicardPullbackHom_toPic]
  change (strictPulledPreviousIdealLine (k := k) n m).toPic = _
  exact (strictPulledPreviousIdealLine_picard_eq_productIdeal n m).trans
    (strictExceptionalProductIdeal_picard n m)

/-- The successor original ideal class is the pulled previous class divided by the exceptional. -/
theorem strictKernelLine_picard_succ (n m : ℕ) :
    (strictKernelLine (k := k) (n + 1) m).toPic =
      schemePicardPullbackHom ((projectiveProductInitial (k := k)).stepProjection n)
        (strictKernelLine n (m + 1)).toPic / (stepExceptionalIdealLine n).toPic :=
  eq_div_iff_mul_eq''.mpr (strictKernelLine_picard_step n m).symm

/-- The strict-curve Picard class, with the original ideal sign convention. -/
def strictCurvePicardClass (n m : ℕ) : Additive (projectiveContactStage (k := k) n).Pic :=
  -Additive.ofMul (strictKernelLine (k := k) n m).toPic

/-- The exceptional Picard class is the inverse class of the original center-fiber ideal. -/
def stepExceptionalPicardClass (n : ℕ) :
    Additive (projectiveContactStage (k := k) (n + 1)).Pic :=
  -Additive.ofMul (stepExceptionalIdealLine (k := k) n).toPic

/-- The original Picard pullback of the previous curve is exceptional plus successor strict. -/
theorem strictCurvePicardClass_pullback (n m : ℕ) :
    (schemePicardPullbackHom ((projectiveProductInitial (k := k)).stepProjection n)).toAdditive
        (strictCurvePicardClass n (m + 1)) =
      stepExceptionalPicardClass n + strictCurvePicardClass (n + 1) m := by
  change (schemePicardPullbackHom
      ((projectiveProductInitial (k := k)).stepProjection n)).toAdditive
        (-Additive.ofMul (strictKernelLine n (m + 1)).toPic) = _
  rw [map_neg]
  change -Additive.ofMul
      (schemePicardPullbackHom ((projectiveProductInitial (k := k)).stepProjection n)
        (strictKernelLine n (m + 1)).toPic) =
    -Additive.ofMul (stepExceptionalIdealLine n).toPic +
      -Additive.ofMul (strictKernelLine (n + 1) m).toPic
  rw [strictKernelLine_picard_step, ofMul_mul, neg_add]

/-- The actual one-step strict-transform formula in the original Picard group. -/
theorem strictCurvePicardClass_succ (n m : ℕ) :
    strictCurvePicardClass (k := k) (n + 1) m =
      (schemePicardPullbackHom ((projectiveProductInitial (k := k)).stepProjection n)).toAdditive
        (strictCurvePicardClass (k := k) n (m + 1)) - stepExceptionalPicardClass (k := k) n :=
  eq_sub_iff_add_eq'.mpr (strictCurvePicardClass_pullback n m).symm

end KltDP.Examples.FrobeniusStrictTransformPicardStep
