/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.Tactic.Ring

/-!
The target-ring-linear form of relative Kähler base change, used by the
absolute tensor-product splitting in the companion module.

Bounded port of the final equivalence and generator formula from official
Mathlib/RingTheory/Kaehler/TensorProduct.lean, commit
d0fb6fa74fb79fc5b44a1b0a1de55d5c1dda2372 (2026-09-13), source SHA256
405cfb790690597c7a850256bb4ac4007104c66795eec24c429763d0fdf9ab11.
The original Apache 2.0 header is retained. The pinned Mathlib already has the
base-ring-linear equivalence under the older name `tensorKaehlerEquiv`.
Only that name and the pinned tensor induction's explicit zero cases differ.
No project-specific geometric assumption is used.
-/

noncomputable section

open TensorProduct

namespace KltDP.KaehlerTensorProductSplit

variable (R S A B : Type*) [CommRing R] [CommRing S] [Algebra R S]
variable [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
variable [Algebra A B] [Algebra S B] [IsScalarTower R A B] [IsScalarTower R S B]

attribute [local instance] SMulCommClass.of_commMonoid

/-- Relative base change, with its actual target-ring scalar structure. -/
def relativeEquiv [h : Algebra.IsPushout R S A B] :
    B ⊗[A] Ω[A⁄R] ≃ₗ[B] Ω[B⁄S] := by
  have : Algebra.IsPushout R A S B := .symm inferInstance
  let e₁ : B ⊗[A] Ω[A⁄R] ≃ₗ[A] Ω[A⁄R] ⊗[R] S :=
    AlgebraTensorModule.congr (Algebra.IsPushout.equiv R A S B).symm.toLinearEquiv
        (.refl _ _) ≪≫ₗ TensorProduct.comm _ _ _ ≪≫ₗ
      AlgebraTensorModule.cancelBaseChange ..
  let e₂ : B ⊗[A] Ω[A⁄R] ≃ₗ[R] Ω[B⁄S] :=
    e₁.restrictScalars R ≪≫ₗ TensorProduct.comm _ _ _ ≪≫ₗ
      (KaehlerDifferential.tensorKaehlerEquiv R S A B).restrictScalars R
  refine { __ := e₂, map_smul' := ?_ }
  intro m x
  obtain ⟨m, rfl⟩ := (Algebra.IsPushout.equiv R A S B).surjective m
  dsimp
  induction m with
  | zero => simp only [map_zero, zero_smul]
  | add x y _ _ => simp only [add_smul, map_add, *]
  | tmul a b =>
    induction x with
    | zero => simp only [map_zero, smul_zero]
    | add x y _ _ => simp only [smul_add, map_add, *]
    | tmul x y =>
      obtain ⟨x, rfl⟩ := (Algebra.IsPushout.equiv R A S B).surjective x
      induction x with
      | zero => simp only [map_zero, zero_tmul, smul_zero]
      | add x y _ _ => simp only [smul_add, map_add, *, add_tmul]
      | tmul x z =>
        suffices b • z • a • x • KaehlerDifferential.map R S A B y =
            (algebraMap A B a * algebraMap S B b) •
              z • x • KaehlerDifferential.map R S A B y by
          simpa [e₂, e₁, smul_tmul', Algebra.IsPushout.equiv_tmul, ← mul_smul,
            Algebra.IsPushout.equiv_symm_algebraMap_left,
            Algebra.IsPushout.equiv_symm_algebraMap_right]
        simp only [← mul_smul, ← @algebraMap_smul S _ B,
          ← @algebraMap_smul A _ B]
        ring_nf

@[simp]
theorem relativeEquiv_tmul_D [Algebra.IsPushout R S A B] (b : B) (a : A) :
    relativeEquiv R S A B (b ⊗ₜ KaehlerDifferential.D R A a) =
      b • KaehlerDifferential.D S B (algebraMap A B a) := by
  have : Algebra.IsPushout R A S B := .symm inferInstance
  obtain ⟨b, rfl⟩ := (Algebra.IsPushout.equiv R A S B).surjective b
  induction b with
  | zero => simp
  | add x y _ _ => simp only [map_add, *, add_tmul, add_smul]
  | tmul a' s =>
    trans s • a' • KaehlerDifferential.D S B (algebraMap A B a)
    · change KaehlerDifferential.tensorKaehlerEquiv R S A B
        (TensorProduct.comm R (Ω[A⁄R]) S
          (AlgebraTensorModule.cancelBaseChange R A A (Ω[A⁄R]) S
            (TensorProduct.comm A (A ⊗[R] S) (Ω[A⁄R])
              (AlgebraTensorModule.congr
                (Algebra.IsPushout.equiv R A S B).symm.toLinearEquiv
                (LinearEquiv.refl A (Ω[A⁄R]))
                ((Algebra.IsPushout.equiv R A S B) (a' ⊗ₜ[R] s) ⊗ₜ[A]
                  KaehlerDifferential.D R A a))))) = _
      simp
    · simp [Algebra.IsPushout.equiv_tmul, mul_smul, smul_comm]

@[simp]
theorem relativeEquiv_symm_D_algebraMap [Algebra.IsPushout R S A B] (a : A) :
    (relativeEquiv R S A B).symm
        (KaehlerDifferential.D S B (algebraMap A B a)) =
      1 ⊗ₜ KaehlerDifferential.D R A a := by
  apply (relativeEquiv R S A B).injective
  simp

end KltDP.KaehlerTensorProductSplit
