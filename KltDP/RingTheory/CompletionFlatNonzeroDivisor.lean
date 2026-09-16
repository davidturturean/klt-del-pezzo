import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.Flat.Basic

/-!
# Nonzerodivisors modulo a prime survive flat base change

BRIEF27, item (G3). Let `S` be a flat `R`-algebra, `p` a prime ideal of `R` and `t ∉ p`. Then `t`
is a nonzerodivisor on `R ⧸ p`, hence on `S ⊗[R] (R ⧸ p) ≅ S ⧸ p S` (Mathlib's
`TensorProduct.tensorQuotEquivQuotSMul`, `Module.Flat.lTensor_preserves_injective_linearMap`):

* **`mem_map_of_smul_mem_map`**: `algebraMap t · z ∈ p S → z ∈ p S`.
* `AdicCompletion.mem_map_of_smul_mem_map`: the case of the `I`-adic completion of a Noetherian ring
  (flat by Mathlib's `AdicCompletion.flat_of_isNoetherian`).
-/

noncomputable section

open TensorProduct

universe u

namespace KltDP.RingTheory.FlatNonzeroDivisor

variable {R : Type u} [CommRing R]

/-- Multiplication by `t ∉ p` is injective on `R ⧸ p` for a prime `p`. -/
theorem lsmul_injective (p : Ideal R) [p.IsPrime] {t : R} (ht : t ∉ p) :
    Function.Injective (LinearMap.lsmul R (R ⧸ p) t) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  have h : Ideal.Quotient.mk p (t * a) = 0 := hx
  rw [Ideal.Quotient.eq_zero_iff_mem] at h ⊢
  exact (Ideal.IsPrime.mem_or_mem inferInstance h).resolve_left ht

variable {S : Type u} [CommRing S] [Algebra R S] [Module.Flat R S]

/-- **Nonzerodivisors modulo a prime survive flat base change**: for `p` prime, `t ∉ p` and a flat
`R`-algebra `S`, `t · z ∈ p S` implies `z ∈ p S`. -/
theorem mem_map_of_smul_mem_map (p : Ideal R) [p.IsPrime] {t : R} (ht : t ∉ p) {z : S}
    (hz : algebraMap R S t * z ∈ Ideal.map (algebraMap R S) p) :
    z ∈ Ideal.map (algebraMap R S) p := by
  have hmem : ∀ y : S, y ∈ Ideal.map (algebraMap R S) p ↔ y ∈ (p • ⊤ : Submodule R S) := fun y => by
    rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem]
  rw [hmem] at hz ⊢
  rw [← Algebra.smul_def] at hz
  set E := TensorProduct.tensorQuotEquivQuotSMul S p with hEdef
  set f := LinearMap.lsmul R (R ⧸ p) t with hfdef
  have hE : ∀ y : S ⊗[R] (R ⧸ p), E (f.lTensor S y) = t • E y := fun y => by
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero, smul_zero]
    | tmul x q =>
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
      rw [LinearMap.lTensor_tmul]
      have h1 : f (Ideal.Quotient.mk p r) = Ideal.Quotient.mk p (t * r) := rfl
      rw [h1, hEdef, TensorProduct.tensorQuotEquivQuotSMul_tmul_mk,
        TensorProduct.tensorQuotEquivQuotSMul_tmul_mk, ← Submodule.Quotient.mk_smul, mul_smul]
    | add y₁ y₂ h₁ h₂ => simp only [map_add, h₁, h₂, smul_add]
  have hinj : Function.Injective (f.lTensor S) :=
    Module.Flat.lTensor_preserves_injective_linearMap f (lsmul_injective p ht)
  have h0 : t • (Submodule.Quotient.mk z : S ⧸ (p • ⊤ : Submodule R S)) = 0 := by
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact hz
  have h1 : f.lTensor S (E.symm (Submodule.Quotient.mk z)) = 0 := by
    apply E.injective
    rw [hE, LinearEquiv.apply_symm_apply, map_zero]
    exact h0
  have h2 : E.symm (Submodule.Quotient.mk z) = 0 := hinj (by rw [h1, map_zero])
  have h3 : (Submodule.Quotient.mk z : S ⧸ (p • ⊤ : Submodule R S)) = 0 := by
    have h4 := congrArg E h2
    rwa [LinearEquiv.apply_symm_apply, map_zero] at h4
  exact (Submodule.Quotient.mk_eq_zero _).mp h3

/-- The completion of a Noetherian ring is flat, so nonzerodivisors modulo a prime `p` remain
nonzerodivisors modulo `p R̂`. -/
theorem _root_.KltDP.RingTheory.AdicCompletion.mem_map_of_smul_mem_map [IsNoetherianRing R]
    (I p : Ideal R) [p.IsPrime] {t : R} (ht : t ∉ p) {z : AdicCompletion I R}
    (hz : algebraMap R (AdicCompletion I R) t * z ∈ Ideal.map (algebraMap R (AdicCompletion I R)) p) :
    z ∈ Ideal.map (algebraMap R (AdicCompletion I R)) p :=
  KltDP.RingTheory.FlatNonzeroDivisor.mem_map_of_smul_mem_map p ht hz

end KltDP.RingTheory.FlatNonzeroDivisor
