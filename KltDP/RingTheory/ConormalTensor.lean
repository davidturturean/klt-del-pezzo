import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-!
# The actual tensor presentation of the conormal module

The pinned `TensorProduct.quotTensorEquivQuotSMul` already identifies
`(A/J) ⊗[A] J` with `J/J²` as an `A`-module. This module retains that
equivalence and proves its linearity for the actual quotient-ring action.
There are no principal, regularity, or geometric assumptions.
-/

noncomputable section

open scoped TensorProduct

namespace KltDP.RingTheory

universe u

variable {A : Type u} [CommRing A] (J : Ideal A)

/-- The tensor presentation of the actual cotangent module, linear over
the actual quotient ring. Its underlying map is the pinned quotient-tensor
equivalence. -/
def conormalTensorEquiv : ((A ⧸ J) ⊗[A] J) ≃ₗ[A ⧸ J] J.Cotangent := by
  let e : ((A ⧸ J) ⊗[A] J) ≃ₗ[A] J.Cotangent :=
    TensorProduct.quotTensorEquivQuotSMul J J
  refine { e.toAddEquiv with map_smul' := ?_ }
  intro q z
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul s y =>
      obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective s
      change e ((Ideal.Quotient.mk J r • Ideal.Quotient.mk J t) ⊗ₜ[A] y) =
        Ideal.Quotient.mk J r • e (Ideal.Quotient.mk J t ⊗ₜ[A] y)
      rw [smul_eq_mul, ← map_mul]
      change TensorProduct.quotTensorEquivQuotSMul J J
          (Ideal.Quotient.mk J (r * t) ⊗ₜ[A] y) =
        Ideal.Quotient.mk J r •
          TensorProduct.quotTensorEquivQuotSMul J J
            (Ideal.Quotient.mk J t ⊗ₜ[A] y)
      rw [TensorProduct.quotTensorEquivQuotSMul_mk_tmul,
        TensorProduct.quotTensorEquivQuotSMul_mk_tmul]
      change J.toCotangent ((r * t) • y) = J.toCotangent (r • (t • y))
      rw [mul_smul]
  | add x y hx hy =>
      change e (Ideal.Quotient.mk J r • x) = Ideal.Quotient.mk J r • e x at hx
      change e (Ideal.Quotient.mk J r • y) = Ideal.Quotient.mk J r • e y at hy
      change e (Ideal.Quotient.mk J r • (x + y)) =
        Ideal.Quotient.mk J r • e (x + y)
      rw [smul_add, map_add, map_add, hx, hy, smul_add]

/-- On actual pure tensors the quotient-linear equivalence is the
ordinary conormal class of the scalar multiple. -/
@[simp]
theorem conormalTensorEquiv_mk_tmul (r : A) (x : J) :
    conormalTensorEquiv J (Ideal.Quotient.mk J r ⊗ₜ[A] x) =
      J.toCotangent (r • x) :=
  TensorProduct.quotTensorEquivQuotSMul_mk_tmul J r x

/-- The inverse sends the class of an actual ideal element to its
canonical pure tensor. -/
@[simp]
theorem conormalTensorEquiv_symm_toCotangent (x : J) :
    (conormalTensorEquiv J).symm (J.toCotangent x) = 1 ⊗ₜ[A] x :=
  TensorProduct.quotTensorEquivQuotSMul_symm_mk J x

end KltDP.RingTheory
