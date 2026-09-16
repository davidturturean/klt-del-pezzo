/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Jujian Zhang

The simultaneous localization instance is a bounded port of Mathlib
RingTheory/Localization/BaseChange.lean, revision
141f6b6455959bfeb0b2a6b04118031191d62683, lines 106–115.

Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin

The normalized localized tensor equivalence follows
MazurTorsion/Upstream/DivisorLineBundle.lean, revision
9327963d4ec14fba49c7b14b004fd00707ffc2e9, lines 185–290.
Only pinned module-localization and tensor APIs are imported here.
-/
import Mathlib.RingTheory.Localization.BaseChange

/-!
# The canonical tensor product of actual module localizations

The tensor of two original localization maps is again a localization.
The resulting canonical equivalence preserves the original numerator
maps and multiplies denominators. No localization comparison is assumed.
-/

noncomputable section

open scoped TensorProduct

universe u

namespace KltDP.RingTheory.LocalizedTensorProduct

variable {R : Type u} [CommRing R] (S : Submonoid R)

/-- Simultaneously localizing two actual module maps localizes their tensor map. -/
instance tensor_map_isLocalizedModule
    {M M' N N' : Type u} [AddCommGroup M] [AddCommGroup M']
    [AddCommGroup N] [AddCommGroup N']
    [Module R M] [Module R M'] [Module R N] [Module R N']
    (f : M →ₗ[R] M') (g : N →ₗ[R] N')
    [IsLocalizedModule S f] [IsLocalizedModule S g] :
    IsLocalizedModule S (TensorProduct.map f g) := by
  let eM := IsLocalizedModule.linearEquiv S f (TensorProduct.mk R (Localization S) M 1)
  let eN := IsLocalizedModule.linearEquiv S g (TensorProduct.mk R (Localization S) N 1)
  letI := IsLocalization.tensorProduct_compatibleSMul S (Localization S)
    (Localization S ⊗[R] M) (Localization S ⊗[R] N)
  convert IsLocalizedModule.of_linearEquiv S
    (TensorProduct.mk R (Localization S) (M ⊗[R] N) 1)
    ((TensorProduct.AlgebraTensorModule.distribBaseChange R (Localization S) M N).restrictScalars R ≪≫ₗ
      (TensorProduct.congr eM eN ≪≫ₗ
        TensorProduct.equivOfCompatibleSMul (Localization S) R
          (Localization S ⊗[R] M) (Localization S ⊗[R] N)).symm) using 1
  ext m n
  change f m ⊗ₜ[R] g n = eM.symm (1 ⊗ₜ[R] m) ⊗ₜ[R] eN.symm (1 ⊗ₜ[R] n)
  congr 1 <;> simp only [LinearEquiv.eq_symm_apply, eM, eN, IsLocalizedModule.linearEquiv_apply] <;> rfl

variable (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (A : Type u) [CommRing A] [Algebra R A] [IsLocalization S A]

/-- Tensor localization over the original chosen localization ring. -/
def equiv :
    LocalizedModule S M ⊗[A] LocalizedModule S N ≃ₗ[A]
      LocalizedModule S (M ⊗[R] N) :=
  (IsLocalization.moduleTensorEquiv S A
    (LocalizedModule S M) (LocalizedModule S N)).trans
    ((IsLocalizedModule.linearEquiv S
      (TensorProduct.map (LocalizedModule.mkLinearMap S M) (LocalizedModule.mkLinearMap S N))
      (LocalizedModule.mkLinearMap S (M ⊗[R] N))).extendScalarsOfIsLocalization S A)

/-- The original numerator tensor is sent to the original tensor numerator. -/
theorem equiv_mk_one (m : M) (n : N) :
    equiv S M N A (LocalizedModule.mk m 1 ⊗ₜ[A] LocalizedModule.mk n 1) =
      LocalizedModule.mk (m ⊗ₜ[R] n) 1 := by
  change (IsLocalizedModule.linearEquiv S
      (TensorProduct.map (LocalizedModule.mkLinearMap S M) (LocalizedModule.mkLinearMap S N))
      (LocalizedModule.mkLinearMap S (M ⊗[R] N)))
      ((TensorProduct.map (LocalizedModule.mkLinearMap S M) (LocalizedModule.mkLinearMap S N))
        (m ⊗ₜ[R] n)) = _
  exact IsLocalizedModule.linearEquiv_apply S _ _ _

/-- Original base-ring scalar multiplication is preserved too. -/
theorem equiv_smul (r : R) (z : LocalizedModule S M ⊗[A] LocalizedModule S N) :
    equiv S M N A (r • z) = r • equiv S M N A z :=
  ((equiv S M N A).restrictScalars R).map_smul r z

/-- The canonical localization tensor equivalence multiplies original denominators. -/
theorem equiv_mk (m : M) (n : N) (s t : S) :
    equiv S M N A (LocalizedModule.mk m s ⊗ₜ[A] LocalizedModule.mk n t) =
      LocalizedModule.mk (m ⊗ₜ[R] n) (s * t) := by
  have hm : LocalizedModule.mk m s =
      IsLocalization.mk' A 1 s • LocalizedModule.mk m 1 := by
    simpa using (LocalizedModule.mk'_smul_mk (T := A) 1 m s 1).symm
  have hn : LocalizedModule.mk n t =
      IsLocalization.mk' A 1 t • LocalizedModule.mk n 1 := by
    simpa using (LocalizedModule.mk'_smul_mk (T := A) 1 n t 1).symm
  rw [hm, hn]
  simp only [TensorProduct.smul_tmul_smul, map_smul]
  rw [equiv_mk_one]
  have hmn : LocalizedModule.mk (m ⊗ₜ[R] n) (s * t) =
      IsLocalization.mk' A 1 (s * t) • LocalizedModule.mk (m ⊗ₜ[R] n) 1 := by
    simpa using (LocalizedModule.mk'_smul_mk (T := A) 1 (m ⊗ₜ[R] n) (s * t) 1).symm
  rw [hmn]
  congr 1
  rw [← IsLocalization.mk'_mul]
  simp

end KltDP.RingTheory.LocalizedTensorProduct
