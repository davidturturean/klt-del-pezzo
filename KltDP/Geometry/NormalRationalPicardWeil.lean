import KltDP.Geometry.NormalPicardWeilClassInjective
import KltDP.Geometry.NumericalEquivalence
import Mathlib.RingTheory.Flat.Localization

/-!
The original rational Picard group embeds in rational Weil classes on a
normal projective surface. Tensoring the proved integral injection with
the flat localization Q supplies the comparison without target regularity.
-/

noncomputable section

open scoped TensorProduct

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)

/-- The original integral Picard-to-Weil map extended to rational scalars. -/
def rationalPicardToWeilClass : X.RationalPicard →ₗ[ℚ] X.RationalWeilClassGroup :=
  X.weilClassTensorRationalEquiv.toLinearMap.comp
    (X.picardToWeilClassHom.toIntLinearMap.baseChange ℚ)

theorem rationalPicardToWeilClass_inclusion (p : Additive X.toScheme.Pic) :
    X.rationalPicardToWeilClass (X.picardTensorInclusion p) =
      X.weilClassRationalization (X.picardToWeilClassHom p) := by
  change X.weilClassTensorRationalEquiv
    (1 ⊗ₜ[ℤ] X.picardToWeilClassHom p) = _
  exact X.weilClassTensorRationalEquiv_one_tmul _

/-- Normality suffices for injectivity; no regularity or local factoriality
of the target is assumed. -/
theorem rationalPicardToWeilClass_injective [IsAlgClosed k] :
    Function.Injective X.rationalPicardToWeilClass := by
  letI : Module.Flat ℤ ℚ := IsLocalization.flat ℚ (nonZeroDivisors ℤ)
  exact X.weilClassTensorRationalEquiv.injective.comp
    (Module.Flat.lTensor_preserves_injective_linearMap (M := ℚ)
      X.picardToWeilClassHom.toIntLinearMap X.picardToWeilClassHom_injective)

/-- A proved Weil-class spanning statement pulls back to the actual
rational Picard group through the normal-target injection. -/
theorem rationalPicard_span_of_weilClass_span [IsAlgClosed k]
    (p : Additive X.toScheme.Pic)
    (hspan : ∀ w : X.RationalWeilClassGroup, ∃ q : ℚ,
      w = q • X.weilClassRationalization (X.picardToWeilClassHom p))
    (v : X.RationalPicard) :
    ∃ q : ℚ, v = q • X.picardTensorInclusion p := by
  obtain ⟨q, hq⟩ := hspan (X.rationalPicardToWeilClass v)
  refine ⟨q, X.rationalPicardToWeilClass_injective ?_⟩
  rw [map_smul, X.rationalPicardToWeilClass_inclusion]
  exact hq

end KltDP.Geometry.NormalProjectiveSurface
