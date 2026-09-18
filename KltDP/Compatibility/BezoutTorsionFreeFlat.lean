/-
Copyright (c) 2025 Matthew Jasper. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Jasper, Kevin Buzzard

Bounded adaptation of the reverse direction of
Module.Flat.flat_iff_torsion_eq_bot_of_isBezout in Mathlib
RingTheory/Flat/TorsionFree.lean at
fd634dd29761b5d32af50e2b8f6d8ad043024303.
The project retains Lean 4.19.0 / Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b.
The pinned NoZeroSMulDivisors interface replaces newer IsTorsionFree, and
toSpanNonzeroSingleton replaces the newer ideal-basis equivalence.
-/
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.Algebra.NoZeroSMulDivisors.Basic
import Mathlib.LinearAlgebra.Span.Basic

/-! Torsion-free modules over a Bezout domain are flat, using only the
pinned finitely generated ideal criterion and an explicit principal-ideal
linear equivalence. No finite-generation assumption on the module is used. -/

noncomputable section

open LinearMap TensorProduct

namespace KltDP.Compatibility.BezoutTorsionFreeFlat

/-- Every torsion-free module over an actual Bezout domain is flat. -/
theorem flat_of_noZeroSMulDivisors (R M : Type*)
    [CommRing R] [IsDomain R] [IsBezout R]
    [AddCommGroup M] [Module R M] [NoZeroSMulDivisors R M] :
    Module.Flat R M := by
  rw [Module.Flat.iff_lift_lsmul_comp_subtype_injective]
  intro I hFG
  obtain rfl | hI := eq_or_ne I ⊥
  · intro x y _
    exact Subsingleton.elim x y
  · letI : I.IsPrincipal := IsBezout.isPrincipal_of_FG I hFG
    let r : R := Submodule.IsPrincipal.generator I
    have hr : r ≠ 0 :=
      mt (Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero I).mpr hI
    let e : R ≃ₗ[R] I :=
      (LinearEquiv.toSpanNonzeroSingleton R R r hr).trans
        (LinearEquiv.ofEq (R ∙ r) I (Submodule.IsPrincipal.span_singleton_generator I))
    have he (a : R) : (e a : R) = a * r := by
      rfl
    let t : R ⊗[R] M ≃ₗ[R] I ⊗[R] M := e.rTensor M
    let φ : I ⊗[R] M →ₗ[R] M := TensorProduct.lift ((lsmul R M).comp I.subtype)
    have hcomp : φ.comp t.toLinearMap =
        (lsmul R M r).comp (TensorProduct.lid R M).toLinearMap := by
      ext a m
      simp [φ, t, he, smul_smul, mul_comm]
    have hinj : Function.Injective (φ ∘ t) := by
      change Function.Injective (φ.comp t.toLinearMap)
      rw [hcomp]
      exact (smul_right_injective M hr).comp (TensorProduct.lid R M).injective
    exact hinj.of_comp_right t.surjective

/-- An injective homomorphism from a Bezout domain to a domain is flat
for its original algebra structure. -/
theorem ringHom_flat_of_injective {R A : Type*}
    [CommRing R] [IsDomain R] [IsBezout R] [CommRing A] [IsDomain A]
    (f : R →+* A) (hf : Function.Injective f) : f.Flat := by
  letI : Algebra R A := f.toAlgebra
  letI : NoZeroSMulDivisors R A := NoZeroSMulDivisors.iff_algebraMap_injective.mpr hf
  exact flat_of_noZeroSMulDivisors R A

end KltDP.Compatibility.BezoutTorsionFreeFlat

#print axioms KltDP.Compatibility.BezoutTorsionFreeFlat.flat_of_noZeroSMulDivisors
#print axioms KltDP.Compatibility.BezoutTorsionFreeFlat.ringHom_flat_of_injective
