import KltDP.Geometry.SmoothPrincipalAdjunctionChart
import Mathlib.LinearAlgebra.TensorProduct.Associator

/-!
# Equation-independent adjunction with the actual normal module

Tensor the produced local determinant map with the dual of the original
ideal conormal module. The equation scaling of the determinant map cancels
the scaling of the actual dual conormal vector. Consequently the resulting
linear equivalence is equal for any two regular generators of the same
ideal, without an assumed transition or adjunction certificate.

This is an affine module theorem. Naturality under localization and changes
of ambient chart, comparison with the actual sheaf tensor, and gluing to
the accepted smooth surface canonical sheaf remain separate obligations.
-/

noncomputable section

open scoped TensorProduct

universe u

namespace KltDP.RingTheory.NormalTwistedAdjunction

section NormalFrame

variable {A : Type u} [CommRing A] (J : Ideal A) (d : J)
  (hJ : Ideal.span {(d : A)} = J) (hregular : (d : A) ∈ nonZeroDivisors A)

/-- The actual dual conormal vector evaluating to one on the defining equation. -/
def normalFrame : Module.Dual (A ⧸ J) J.Cotangent :=
  (principalNormalEquiv J d hJ hregular).symm 1

theorem normalFrame_evaluation :
    normalFrame J d hJ hregular (J.toCotangent d) = 1 := by
  have h := (principalNormalEquiv J d hJ hregular).apply_symm_apply (1 : A ⧸ J)
  simpa only [principalNormalEquiv_apply, normalFrame] using h

/-- Equation scaling is inverted by the actual normal vector. -/
theorem normalFrame_change (e : J) (hE : Ideal.span {(e : A)} = J)
    (heregular : (e : A) ∈ nonZeroDivisors A) (r : A)
    (he : (e : A) = r * (d : A)) :
    Ideal.Quotient.mk J r • normalFrame J e hE heregular =
      normalFrame J d hJ hregular := by
  apply (principalNormalEquiv J d hJ hregular).injective
  simp only [principalNormalEquiv_apply, LinearMap.smul_apply, normalFrame_evaluation]
  rw [← map_smul, ← toCotangent_eq_quotient_smul_of_eq_mul J d e r he]
  exact normalFrame_evaluation J e hE heregular

end NormalFrame

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] (J : Ideal A)
  [Algebra.IsStandardSmoothOfRelativeDimension 2 R A]
  [Algebra.IsStandardSmoothOfRelativeDimension 1 R (A ⧸ J)]

local instance ambientStandardSmooth : Algebra.IsStandardSmooth R A :=
  Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth (R := R) (S := A) 2

variable (d : J) (hJ : Ideal.span {(d : A)} = J)
  (hregular : (d : A) ∈ nonZeroDivisors A)

/-- The original ambient top-form target retains the actual equation scaling. -/
theorem moduleEquiv_changeEquation (e : J) (hE : Ideal.span {(e : A)} = J)
    (heregular : (e : A) ∈ nonZeroDivisors A) (r : A)
    (he : (e : A) = r * (d : A)) (n : KaehlerDifferential R (A ⧸ J)) :
    KltDP.Geometry.SmoothPrincipalAdjunctionChart.moduleEquiv R A J e hE heregular n =
      Ideal.Quotient.mk J r •
        KltDP.Geometry.SmoothPrincipalAdjunctionChart.moduleEquiv R A J d hJ hregular n := by
  change (KltDP.Geometry.TopExteriorBaseChange.equiv (A ⧸ J)
      (KltDP.Geometry.AffineTopDifferentialFrame.standardSmoothDifferentialBasis R A)).symm
      (SmoothPrincipalConormalDeterminant.determinantEquiv R A J e hE heregular n) =
    Ideal.Quotient.mk J r •
      (KltDP.Geometry.TopExteriorBaseChange.equiv (A ⧸ J)
        (KltDP.Geometry.AffineTopDifferentialFrame.standardSmoothDifferentialBasis R A)).symm
        (SmoothPrincipalConormalDeterminant.determinantEquiv R A J d hJ hregular n)
  rw [SmoothPrincipalConormalDeterminant.determinantEquiv_changeEquation
    R A J d hJ hregular e hE heregular r he n, map_smul]

/-- Local adjunction with the actual dual conormal factor retained. -/
def equiv :
    KaehlerDifferential R (A ⧸ J) ≃ₗ[A ⧸ J]
      ((A ⧸ J) ⊗[A] (⋀[A]^2 (KaehlerDifferential R A))) ⊗[A ⧸ J]
        Module.Dual (A ⧸ J) J.Cotangent :=
  (KltDP.Geometry.SmoothPrincipalAdjunctionChart.moduleEquiv R A J d hJ hregular).trans
    ((TensorProduct.rid (A ⧸ J)
      ((A ⧸ J) ⊗[A] (⋀[A]^2 (KaehlerDifferential R A)))).symm.trans
      (TensorProduct.congr
        (LinearEquiv.refl (A ⧸ J) ((A ⧸ J) ⊗[A] (⋀[A]^2 (KaehlerDifferential R A))))
        (principalNormalEquiv J d hJ hregular).symm))

/-- The normal factor is the functional dual to the original equation class. -/
theorem equiv_apply (n : KaehlerDifferential R (A ⧸ J)) :
    equiv R A J d hJ hregular n =
      KltDP.Geometry.SmoothPrincipalAdjunctionChart.moduleEquiv R A J d hJ hregular n
        ⊗ₜ[A ⧸ J] normalFrame J d hJ hregular := by
  simp only [equiv, LinearEquiv.trans_apply, TensorProduct.rid_symm_apply,
    TensorProduct.congr_tmul, LinearEquiv.refl_apply, normalFrame]

/-- Tensor balancing cancels the two actual equation transition factors. -/
theorem equiv_changeEquation (e : J) (hE : Ideal.span {(e : A)} = J)
    (heregular : (e : A) ∈ nonZeroDivisors A) (r : A)
    (he : (e : A) = r * (d : A)) (n : KaehlerDifferential R (A ⧸ J)) :
    equiv R A J e hE heregular n = equiv R A J d hJ hregular n := by
  rw [equiv_apply, equiv_apply,
    moduleEquiv_changeEquation R A J d hJ hregular e hE heregular r he n,
    TensorProduct.smul_tmul, normalFrame_change J d hJ hregular e hE heregular r he]

/-- The produced actual tensor equivalence is independent of the regular generator. -/
theorem equiv_eq (e : J) (hE : Ideal.span {(e : A)} = J)
    (heregular : (e : A) ∈ nonZeroDivisors A) :
    equiv R A J e hE heregular = equiv R A J d hJ hregular := by
  have he : (e : A) ∈ Ideal.span {(d : A)} := by
    rw [hJ]
    exact e.property
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp he
  apply LinearEquiv.ext
  intro n
  exact equiv_changeEquation R A J d hJ hregular e hE heregular r hr.symm n

end KltDP.RingTheory.NormalTwistedAdjunction
