/-
Copyright (c) 2025 Matthew Jasper. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Jasper, Kevin Buzzard

The regular-scalar proof is the bounded port of Mathlib
RingTheory/Flat/TorsionFree.lean:45-59 at
633b366493a76df88a2bff099ed0cbf711a59ec9. The final domain specialization
uses the pinned NoZeroSMulDivisors interface instead of the newer
IsTorsionFree class. No Dedekind-domain equivalence is imported or claimed.
-/
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Algebra.Regular.SMul
import Mathlib.Algebra.NoZeroSMulDivisors.Defs

/-!
# Regular scalars on flat modules at the project pin

Tensoring multiplication by a regular scalar with a flat module preserves
injectivity. The tensor unit isomorphism identifies this map with scalar
multiplication on the original module. Over a domain this gives the
original torsion-free interface used by the pinned PID freeness theorem.
-/

noncomputable section

open LinearMap TensorProduct

namespace KltDP.Compatibility.FlatModuleTorsionFree

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- A regular scalar acts injectively on the original flat module. -/
theorem isSMulRegular_of_isRegular {r : R} (hr : IsRegular r) [Module.Flat R M] :
    IsSMulRegular M r := by
  have h := Module.Flat.rTensor_preserves_injective_linearMap (M := M)
    (toSpanSingleton R R r) hr.right
  have hmap : (fun x : M => r • x) =
      ((TensorProduct.lid R M).toLinearMap ∘ₗ
        (toSpanSingleton R R r).rTensor M ∘ₗ
        (TensorProduct.lid R M).symm.toLinearMap) := by
    ext x
    simp
  rw [IsSMulRegular, hmap]
  exact (TensorProduct.lid R M).injective.comp
    (h.comp (TensorProduct.lid R M).symm.injective)

/-- A flat module over a domain satisfies the pinned no-zero-scalar-divisors interface. -/
theorem noZeroSMulDivisors_of_flat (R M : Type*) [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] [Module.Flat R M] : NoZeroSMulDivisors R M where
  eq_zero_or_eq_zero_of_smul_eq_zero {r m} h := by
    by_cases hr : r = 0
    · exact Or.inl hr
    · right
      apply isSMulRegular_of_isRegular (M := M) (isRegular_of_ne_zero hr)
      simpa only [smul_zero] using h

end KltDP.Compatibility.FlatModuleTorsionFree
