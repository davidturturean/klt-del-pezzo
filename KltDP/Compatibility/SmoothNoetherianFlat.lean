/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Flatness of formally smooth finite-type algebras over a Noetherian ring

This bounded port follows the completion-and-retraction proof in official
Mathlib revision a2ba36bc2c8a42c81dec34f290070689583d7477,
`RingTheory/Smooth/AdicCompletion.lean` and `RingTheory/Smooth/Flat.lean`.
The original author attribution and Apache-2.0 license are retained.

The pin already proves flatness of Noetherian adic completions and flatness
of retracts. The helpers below build the missing compatible algebra lift
using the pinned nilpotent-surjection lifting theorem. They use the actual
adic completion, quotient transition maps, and scalar actions. Only the
Noetherian-base case is ported; no Noetherian descent is needed downstream.
-/

noncomputable section

universe u

namespace KltDP.Compatibility.SmoothNoetherianFlat

private def quotientFactor (R : Type u) [CommRing R]
    {S : Type u} [CommRing S] [Algebra R S]
    {I J : Ideal S} (h : I ≤ J) : (S ⧸ I) →ₐ[R] S ⧸ J where
  __ := Ideal.Quotient.factor h
  commutes' _ := rfl

private theorem quotientFactor_comp (R : Type u) [CommRing R]
    {S : Type u} [CommRing S] [Algebra R S]
    {I J K : Ideal S} (hIJ : I ≤ J) (hJK : J ≤ K) :
    (quotientFactor R hJK).comp (quotientFactor R hIJ) =
      quotientFactor R (hIJ.trans hJK) := by
  ext x
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

private theorem pow_smul_top_eq {S : Type u} [CommRing S] (I : Ideal S) (n : ℕ) :
    (I ^ n • ⊤ : Ideal S) = I ^ n := by
  ext x
  simp

variable {R A S : Type u} [CommRing R] [CommRing A] [CommRing S]
variable [Algebra R A] [Algebra R S]

private theorem quotientPowerStep_ker_nilpotent (I : Ideal S) (n : ℕ) :
    IsNilpotent (RingHom.ker (quotientFactor R
      (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)) : I ^ (n + 2) ≤ I ^ (n + 1))).toRingHom) := by
  change IsNilpotent (RingHom.ker (Ideal.Quotient.factor
    (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)) : I ^ (n + 2) ≤ I ^ (n + 1))))
  rw [Ideal.Quotient.factor_ker]
  refine ⟨2, ?_⟩
  rw [← Ideal.map_pow, Submodule.zero_eq_bot, ← pow_mul]
  exact eq_bot_mono
    (Ideal.map_mono (Ideal.pow_le_pow_right (by omega : n + 2 ≤ (n + 1) * 2)))
    (Ideal.map_quotient_self _)

variable [Algebra.FormallySmooth R A]

private def liftFamily (I : Ideal S) (f : A →ₐ[R] S ⧸ I) :
    (n : ℕ) → A →ₐ[R] S ⧸ I ^ n
  | 0 => (quotientFactor R (show I ≤ I ^ 0 by simp)).comp f
  | 1 => (quotientFactor R (show I ≤ I ^ 1 by simp)).comp f
  | n + 2 =>
    Algebra.FormallySmooth.liftOfSurjective (liftFamily I f (n + 1))
      (quotientFactor R (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))))
      (Ideal.Quotient.factor_surjective
        (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)) : I ^ (n + 2) ≤ I ^ (n + 1)))
      (quotientPowerStep_ker_nilpotent (R := R) I n)

private theorem factor_comp_liftFamily_succ (I : Ideal S) (f : A →ₐ[R] S ⧸ I)
    (n : ℕ) :
    (quotientFactor R (Ideal.pow_le_pow_right n.le_succ)).comp
      (liftFamily I f (n + 1)) = liftFamily I f n := by
  cases n with
  | zero =>
    letI : Subsingleton (S ⧸ I ^ 0) := by
      rw [pow_zero, Ideal.one_eq_top]
      infer_instance
    ext x
    exact Subsingleton.elim _ _
  | succ n =>
    rw [liftFamily]
    exact Algebra.FormallySmooth.comp_liftOfSurjective
      (liftFamily I f (n + 1))
      (quotientFactor R (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))))
      (Ideal.Quotient.factor_surjective
        (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)) : I ^ (n + 2) ≤ I ^ (n + 1)))
      (quotientPowerStep_ker_nilpotent (R := R) I n)

private theorem factor_comp_liftFamily (I : Ideal S) (f : A →ₐ[R] S ⧸ I)
    {m n : ℕ} (hmn : m ≤ n) :
    (quotientFactor R (Ideal.pow_le_pow_right hmn)).comp (liftFamily I f n) =
      liftFamily I f m := by
  induction n, hmn using Nat.le_induction with
  | base =>
    ext x
    obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (liftFamily I f m x)
    change Ideal.Quotient.factor (le_refl (I ^ m)) (liftFamily I f m x) =
      liftFamily I f m x
    rw [← hs]
    rfl
  | succ n hmn ih =>
    rw [← quotientFactor_comp R (Ideal.pow_le_pow_right n.le_succ)
      (Ideal.pow_le_pow_right hmn), AlgHom.comp_assoc,
      factor_comp_liftFamily_succ, ih]

private def completionLift (I : Ideal S) (f : A →ₐ[R] S ⧸ I) :
    A →ₐ[R] AdicCompletion I S where
  toFun x := ⟨fun n => quotientFactor R (pow_smul_top_eq I n).symm.le
      (liftFamily I f n x), fun {m n} hmn => by
    have hcompat := AlgHom.congr_fun (factor_comp_liftFamily I f hmn) x
    change AdicCompletion.transitionMap I S hmn
      (Ideal.Quotient.factor (pow_smul_top_eq I n).symm.le (liftFamily I f n x)) =
        Ideal.Quotient.factor (pow_smul_top_eq I m).symm.le (liftFamily I f m x)
    have hmap : AdicCompletion.transitionMap I S hmn
        (Ideal.Quotient.factor (pow_smul_top_eq I n).symm.le (liftFamily I f n x)) =
      Ideal.Quotient.factor (pow_smul_top_eq I m).symm.le
        (quotientFactor R (Ideal.pow_le_pow_right hmn) (liftFamily I f n x)) := by
      obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (liftFamily I f n x)
      rw [← hs]
      rfl
    rw [hmap]
    exact congrArg (Ideal.Quotient.factor (pow_smul_top_eq I m).symm.le) hcompat⟩
  map_zero' := by
    apply AdicCompletion.ext
    intro n
    change quotientFactor R (pow_smul_top_eq I n).symm.le (liftFamily I f n 0) = 0
    simp only [map_zero]
  map_add' x y := by
    apply AdicCompletion.ext
    intro n
    change quotientFactor R (pow_smul_top_eq I n).symm.le (liftFamily I f n (x + y)) =
      quotientFactor R (pow_smul_top_eq I n).symm.le (liftFamily I f n x) +
        quotientFactor R (pow_smul_top_eq I n).symm.le (liftFamily I f n y)
    simp only [map_add]
  map_one' := by
    apply AdicCompletion.ext
    intro n
    change quotientFactor R (pow_smul_top_eq I n).symm.le (liftFamily I f n 1) = 1
    simp only [map_one]
  map_mul' x y := by
    apply AdicCompletion.ext
    intro n
    change quotientFactor R (pow_smul_top_eq I n).symm.le (liftFamily I f n (x * y)) =
      quotientFactor R (pow_smul_top_eq I n).symm.le (liftFamily I f n x) *
        quotientFactor R (pow_smul_top_eq I n).symm.le (liftFamily I f n y)
    simp only [map_mul]
  commutes' r := by
    apply AdicCompletion.ext
    intro n
    change quotientFactor R (pow_smul_top_eq I n).symm.le
        (liftFamily I f n (algebraMap R A r)) =
      algebraMap R (S ⧸ (I ^ n • ⊤ : Ideal S)) r
    rw [(liftFamily I f n).commutes]
    exact (quotientFactor R (pow_smul_top_eq I n).symm.le).commutes r

private def completionEvalOne (I : Ideal S) : AdicCompletion I S →ₐ[R] S ⧸ I :=
  (quotientFactor R (show (I ^ 1 • ⊤ : Ideal S) ≤ I by
    rw [pow_smul_top_eq, pow_one])).comp
    ((AlgHom.ofLinearMap (AdicCompletion.eval I S 1) rfl (fun _ _ => rfl)).restrictScalars R)

private theorem completionEvalOne_completionLift (I : Ideal S)
    (f : A →ₐ[R] S ⧸ I) (x : A) :
    completionEvalOne (R := R) I (completionLift I f x) = f x := by
  change quotientFactor R (show (I ^ 1 • ⊤ : Ideal S) ≤ I by
      rw [pow_smul_top_eq, pow_one])
    (quotientFactor R (pow_smul_top_eq I 1).symm.le
      (liftFamily I f 1 x)) = f x
  simp only [liftFamily, AlgHom.comp_apply]
  obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (f x)
  rw [← hs]
  rfl

/-- Formal smoothness makes the original algebra a retract of the actual
completion of any flat Noetherian algebra surjecting onto it. -/
theorem formallySmooth_flat_of_surjective
    (f : S →ₐ[R] A) (hf : Function.Surjective f)
    [Module.Flat R S] [IsNoetherianRing S] : Module.Flat R A := by
  let I : Ideal S := RingHom.ker f.toRingHom
  let e : (S ⧸ I) ≃ₐ[R] A := Ideal.quotientKerAlgEquivOfSurjective hf
  let i : A →ₐ[R] AdicCompletion I S := completionLift I e.symm.toAlgHom
  let r : AdicCompletion I S →ₐ[R] A := e.toAlgHom.comp (completionEvalOne (R := R) I)
  letI : Module.Flat R (AdicCompletion I S) :=
    Module.Flat.trans R S (AdicCompletion I S)
  apply Module.Flat.of_retract i.toLinearMap r.toLinearMap
  apply LinearMap.ext
  intro x
  change e (completionEvalOne (R := R) I (completionLift I e.symm.toAlgHom x)) = x
  rw [completionEvalOne_completionLift]
  exact e.apply_symm_apply x

/-- A formally smooth finite-type algebra over the original Noetherian
base ring is flat for that same scalar action. -/
theorem formallySmooth_flat_of_finiteType [IsNoetherianRing R]
    [Algebra.FiniteType R A] : Module.Flat R A := by
  obtain ⟨n, f, hf⟩ :=
    (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := R) (S := A)).mp inferInstance
  exact formallySmooth_flat_of_surjective f hf

end KltDP.Compatibility.SmoothNoetherianFlat
