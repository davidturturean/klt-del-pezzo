import KltDP.RingTheory.SmoothPrincipalTopFormRestriction
import KltDP.RingTheory.NormalTwistedAdjunction
import KltDP.RingTheory.ConormalRestriction
import KltDP.LinearAlgebra.TensorProductSemilinearMap

/-!
# Original normal-twisted adjunction commutes with ring restriction

The original regular principal coordinates give a semilinear map between
the actual module duals of the original ideal cotangents. Its evaluation
is the original quotient-ring map applied to the original evaluation;
this also proves that it is independent of the equation.

The induced tensor map therefore carries the actual normal-twisted local
adjunction map to the actual target local adjunction map. All component
maps and scalar actions are explicit. This is the module restriction law;
comparison with the original sheaf pullback maps and global descent remain
separate obligations.
-/

noncomputable section

open scoped TensorProduct

universe u

namespace KltDP.RingTheory.NormalTwistedAdjunctionRestriction

open SmoothPrincipalDeterminantRestriction

section Normal

variable (A A' : Type u) [CommRing A] [CommRing A'] [Algebra A A']
  (J : Ideal A) (J' : Ideal A') (hφ : J ≤ J'.comap (algebraMap A A'))
  (d : J) (hJ : Ideal.span {(d : A)} = J) (hd : (d : A) ∈ nonZeroDivisors A)
  (hJ' : Ideal.span {(mappedEquation A A' J J' hφ d : A')} = J')
  (hd' : (mappedEquation A A' J J' hφ d : A') ∈ nonZeroDivisors A')

/-- The actual normal-module restriction keeps the original quotient map explicit. -/
def normalRestriction :
    Module.Dual (A ⧸ J) J.Cotangent →ₛₗ[quotientMap A A' J J' hφ]
      Module.Dual (A' ⧸ J') J'.Cotangent :=
  (principalNormalEquiv J' (mappedEquation A A' J J' hφ d) hJ' hd').symm.toLinearMap.comp
    ((quotientMap A A' J J' hφ).toSemilinearMap.comp
      (principalNormalEquiv J d hJ hd).toLinearMap)

/-- The produced normal restriction preserves evaluation on the original equation. -/
theorem normalRestriction_generator (ℓ : Module.Dual (A ⧸ J) J.Cotangent) :
    normalRestriction A A' J J' hφ d hJ hd hJ' hd' ℓ
        (J'.toCotangent (mappedEquation A A' J J' hφ d)) =
      quotientMap A A' J J' hφ (ℓ (J.toCotangent d)) := by
  have he := (principalNormalEquiv J' (mappedEquation A A' J J' hφ d) hJ' hd').apply_symm_apply
    (quotientMap A A' J J' hφ (principalNormalEquiv J d hJ hd ℓ))
  change (principalNormalEquiv J' (mappedEquation A A' J J' hφ d) hJ' hd').symm
      (quotientMap A A' J J' hφ (principalNormalEquiv J d hJ hd ℓ))
      (J'.toCotangent (mappedEquation A A' J J' hφ d)) = _
  simpa only [principalNormalEquiv_apply] using he

/-- Every original cotangent evaluation is retained by the produced normal restriction. -/
theorem normalRestriction_evaluation (ℓ : Module.Dual (A ⧸ J) J.Cotangent)
    (m : J.Cotangent) :
    normalRestriction A A' J J' hφ d hJ hd hJ' hd' ℓ
        (conormalMap J J' (algebraMap A A') hφ m) =
      quotientMap A A' J J' hφ (ℓ m) := by
  let e := principalConormalEquiv J d hJ hd
  obtain ⟨q, rfl⟩ := e.surjective m
  have he1 : e 1 = J.toCotangent d := principalConormalEquiv_one J d hJ hd
  have heq : e q = q • J.toCotangent d := by
    simpa only [smul_eq_mul, mul_one, he1] using e.map_smul q (1 : A ⧸ J)
  rw [heq, (conormalMap J J' (algebraMap A A') hφ).map_smulₛₗ,
    conormalMap_toCotangent]
  simp only [map_smul, smul_eq_mul, map_mul]
  exact congrArg (fun z : A' ⧸ J' => quotientMap A A' J J' hφ q * z)
    (normalRestriction_generator A A' J J' hφ d hJ hd hJ' hd' ℓ)

/-- Original evaluation determines the same normal map for every regular equation. -/
theorem normalRestriction_eq (e : J) (hE : Ideal.span {(e : A)} = J)
    (he : (e : A) ∈ nonZeroDivisors A)
    (hE' : Ideal.span {(mappedEquation A A' J J' hφ e : A')} = J')
    (he' : (mappedEquation A A' J J' hφ e : A') ∈ nonZeroDivisors A') :
    normalRestriction A A' J J' hφ d hJ hd hJ' hd' =
      normalRestriction A A' J J' hφ e hE he hE' he' := by
  apply LinearMap.ext
  intro ℓ
  apply (principalNormalEquiv J' (mappedEquation A A' J J' hφ d) hJ' hd').injective
  simp only [principalNormalEquiv_apply]
  change normalRestriction A A' J J' hφ d hJ hd hJ' hd' ℓ
      (conormalMap J J' (algebraMap A A') hφ (J.toCotangent d)) =
    normalRestriction A A' J J' hφ e hE he hE' he' ℓ
      (conormalMap J J' (algebraMap A A') hφ (J.toCotangent d))
  rw [normalRestriction_evaluation, normalRestriction_evaluation]

/-- The actual dual-equation frame restricts to the actual dual image-equation frame. -/
theorem normalRestriction_normalFrame :
    normalRestriction A A' J J' hφ d hJ hd hJ' hd'
        (NormalTwistedAdjunction.normalFrame J d hJ hd) =
      NormalTwistedAdjunction.normalFrame J' (mappedEquation A A' J J' hφ d) hJ' hd' := by
  apply (principalNormalEquiv J' (mappedEquation A A' J J' hφ d) hJ' hd').injective
  simp only [principalNormalEquiv_apply]
  rw [normalRestriction_generator, NormalTwistedAdjunction.normalFrame_evaluation,
    NormalTwistedAdjunction.normalFrame_evaluation, map_one]

end Normal

variable (R A A' : Type u) [CommRing R] [CommRing A] [CommRing A']
  [Algebra R A] [Algebra R A'] [Algebra A A'] [IsScalarTower R A A']
  (J : Ideal A) (J' : Ideal A') (hφ : J ≤ J'.comap (algebraMap A A'))
  (d : J) (hJ : Ideal.span {(d : A)} = J) (hd : (d : A) ∈ nonZeroDivisors A)
  (hJ' : Ideal.span {(mappedEquation A A' J J' hφ d : A')} = J')
  (hd' : (mappedEquation A A' J J' hφ d : A') ∈ nonZeroDivisors A')

/-- The original top-form and normal maps induce the actual normal-twisted tensor restriction. -/
def twistedRestriction :
    ((A ⧸ J) ⊗[A] (⋀[A]^2 (KaehlerDifferential R A))) ⊗[A ⧸ J]
        Module.Dual (A ⧸ J) J.Cotangent →ₛₗ[quotientMap A A' J J' hφ]
      ((A' ⧸ J') ⊗[A'] (⋀[A']^2 (KaehlerDifferential R A'))) ⊗[A' ⧸ J']
        Module.Dual (A' ⧸ J') J'.Cotangent :=
  KltDP.LinearAlgebra.TensorProductSemilinearMap.map (quotientMap A A' J J' hφ)
    (SmoothPrincipalTopFormRestriction.ambientTopTensorMap R A A' J J' hφ)
    (normalRestriction A A' J J' hφ d hJ hd hJ' hd')

variable [Algebra.IsStandardSmoothOfRelativeDimension 2 R A]
  [Algebra.IsStandardSmoothOfRelativeDimension 2 R A']
  [Algebra.IsStandardSmoothOfRelativeDimension 1 R (A ⧸ J)]
  [Algebra.IsStandardSmoothOfRelativeDimension 1 R (A' ⧸ J')]

/-- The original normal-twisted adjunction maps commute with the original restriction. -/
theorem equiv_restriction (n : KaehlerDifferential R (A ⧸ J)) :
    twistedRestriction R A A' J J' hφ d hJ hd hJ' hd'
        (NormalTwistedAdjunction.equiv R A J d hJ hd n) =
      NormalTwistedAdjunction.equiv R A' J' (mappedEquation A A' J J' hφ d) hJ' hd'
        (quotientDifferentialMap R A A' J J' hφ n) := by
  rw [NormalTwistedAdjunction.equiv_apply]
  change KltDP.LinearAlgebra.TensorProductSemilinearMap.map (quotientMap A A' J J' hφ)
      (SmoothPrincipalTopFormRestriction.ambientTopTensorMap R A A' J J' hφ)
      (normalRestriction A A' J J' hφ d hJ hd hJ' hd')
      (_ ⊗ₜ[A ⧸ J] _) = _
  rw [KltDP.LinearAlgebra.TensorProductSemilinearMap.map_tmul,
    SmoothPrincipalTopFormRestriction.moduleEquiv_restriction,
    normalRestriction_normalFrame, NormalTwistedAdjunction.equiv_apply]

end KltDP.RingTheory.NormalTwistedAdjunctionRestriction
