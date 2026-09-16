/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
/-
Adapted from pinned Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b,
Mathlib/LinearAlgebra/TensorAlgebra/Grading.lean (Eric Wieser).
The same direct-sum argument uses the actual commutative symmetric-algebra
universal property instead of the tensor-algebra universal property.
The resulting grading is intrinsic: powers of the range of the actual inclusion.
No projective-scheme comparison, finite-dimensionality, or projectivity is assumed.
-/

import KltDP.Compatibility.SymmetricAlgebra.Basic
import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# Results about the grading structure of the symmetric algebra

The main result is `SymmetricAlgebra.gradedAlgebra`, which says that the symmetric algebra is a
ℕ-graded algebra.
-/

namespace KltDP.SymmetricAlgebra

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

open scoped DirectSum

variable (R M)

/-- The intrinsic symmetric degree: powers of the range of the original module inclusion.
No basis or projective model is chosen in this definition. -/
abbrev grading (n : ℕ) : Submodule R (SymmetricAlgebra R M) :=
  LinearMap.range (ι R M) ^ n

/-- Every original module element is homogeneous of symmetric degree one. -/
theorem ι_mem_grading_one (m : M) : ι R M m ∈ grading R M 1 := by
  simpa only [grading, pow_one] using LinearMap.mem_range_self (ι R M) m

/-- A version of `SymmetricAlgebra.ι` that maps directly into the graded structure. This is
primarily an auxiliary construction used to provide `SymmetricAlgebra.gradedAlgebra`. -/
nonrec def GradedAlgebra.ι : M →ₗ[R] ⨁ i : ℕ, ↥(LinearMap.range (ι R M : M →ₗ[_] _) ^ i) :=
  DirectSum.lof R ℕ (fun i => ↥(LinearMap.range (ι R M : M →ₗ[_] _) ^ i)) 1 ∘ₗ
    (ι R M).codRestrict _ fun m => by simpa only [pow_one] using LinearMap.mem_range_self _ m

theorem GradedAlgebra.ι_apply (m : M) :
    GradedAlgebra.ι R M m =
      DirectSum.of (fun (i : ℕ) => ↥(LinearMap.range (SymmetricAlgebra.ι R M : M →ₗ[_] _) ^ i)) 1
        ⟨SymmetricAlgebra.ι R M m, by simpa only [pow_one] using LinearMap.mem_range_self _ m⟩ :=
  rfl

variable {R M}

/-- The symmetric algebra is graded by the powers of the submodule `(SymmetricAlgebra.ι R).range`. -/
instance gradedAlgebra :
    GradedAlgebra ((LinearMap.range (ι R M : M →ₗ[R] SymmetricAlgebra R M) ^ ·) : ℕ → Submodule R _) :=
  GradedAlgebra.ofAlgHom _ (lift <| GradedAlgebra.ι R M)
    (by
      ext m
      dsimp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply,
        AlgHom.id_apply]
      change (DirectSum.coeAlgHom (grading R M))
        ((lift (GradedAlgebra.ι R M)) (ι R M m)) = ι R M m
      rw [lift_ι_apply, GradedAlgebra.ι_apply R M, DirectSum.coeAlgHom_of, Subtype.coe_mk])
    fun i x => by
    obtain ⟨x, hx⟩ := x
    dsimp only [Subtype.coe_mk, DirectSum.lof_eq_of]
    induction hx using Submodule.pow_induction_on_left' with
    | algebraMap r =>
      rw [AlgHom.commutes, DirectSum.algebraMap_apply]; rfl
    | add x y i hx hy ihx ihy =>
      rw [map_add, ihx, ihy, ← AddMonoidHom.map_add]
      rfl
    | mem_mul m hm i x hx ih =>
      obtain ⟨_, rfl⟩ := hm
      rw [map_mul, ih, lift_ι_apply, GradedAlgebra.ι_apply R M, DirectSum.of_mul_of]
      exact DirectSum.of_eq_of_gradedMonoid_eq (Sigma.subtype_ext (add_comm _ _) rfl)

end KltDP.SymmetricAlgebra
