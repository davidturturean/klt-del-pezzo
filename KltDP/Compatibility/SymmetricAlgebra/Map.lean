/-
Copyright (c) 2026 KltDP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import KltDP.Compatibility.SymmetricAlgebra.Grading

/-!
# Original symmetric-algebra maps and intrinsic degrees

The compiled universal property extends an original module map to the actual
symmetric quotient algebra. Composition and identities follow by its proved
extensionality theorem. An original module equivalence gives an algebra
equivalence, and its degree preservation follows from powers of the range of
the original inclusion. No basis, finite generation, grading witness or
replacement algebra is an input.
-/

noncomputable section

namespace KltDP.SymmetricAlgebra

universe uR uM uN uP

variable {R : Type uR} [CommSemiring R]
  {M : Type uM} {N : Type uN} {P : Type uP}
  [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]
  [AddCommMonoid P] [Module R P]

/-- Extend the original linear map through the actual symmetric universal property. -/
def map (f : M →ₗ[R] N) : SymmetricAlgebra R M →ₐ[R] SymmetricAlgebra R N :=
  lift (ι R N ∘ₗ f)

@[simp]
theorem map_ι (f : M →ₗ[R] N) (m : M) : map f (ι R M m) = ι R N (f m) := by
  exact lift_ι_apply (ι R N ∘ₗ f) m

/-- The original identity module map induces the identity algebra map. -/
theorem map_id : map (LinearMap.id : M →ₗ[R] M) = AlgHom.id R (SymmetricAlgebra R M) := by
  apply algHom_ext
  apply LinearMap.ext
  intro m
  change map (LinearMap.id : M →ₗ[R] M) (ι R M m) = ι R M m
  rw [map_ι]
  rfl

/-- Composition is preserved on the original algebra maps. -/
theorem map_comp (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    (map g).comp (map f) = map (g.comp f) := by
  apply algHom_ext
  apply LinearMap.ext
  intro m
  change map g (map f (ι R M m)) = map (g.comp f) (ι R M m)
  rw [map_ι, map_ι, map_ι]
  rfl

/-- An original module equivalence induces an equivalence of the actual
symmetric quotient algebras. -/
def congr (e : M ≃ₗ[R] N) : SymmetricAlgebra R M ≃ₐ[R] SymmetricAlgebra R N := by
  refine AlgEquiv.ofAlgHom (map e.toLinearMap) (map e.symm.toLinearMap) ?_ ?_
  · rw [map_comp]
    have h : e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id := by
      apply LinearMap.ext
      intro n
      exact e.apply_symm_apply n
    rw [h, map_id]
  · rw [map_comp]
    have h : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by
      apply LinearMap.ext
      intro m
      exact e.symm_apply_apply m
    rw [h, map_id]

@[simp]
theorem congr_ι (e : M ≃ₗ[R] N) (m : M) : congr e (ι R M m) = ι R N (e m) :=
  map_ι e.toLinearMap m

/-- Every original linear map preserves the intrinsic symmetric degree. -/
theorem map_mem_grading (f : M →ₗ[R] N) {n : ℕ} {x : SymmetricAlgebra R M}
    (hx : x ∈ grading R M n) : map f x ∈ grading R N n := by
  change x ∈ LinearMap.range (ι R M) ^ n at hx
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    rw [(map f).commutes r]
    exact Submodule.algebraMap_mem r
  | add x y i hx hy ihx ihy =>
    rw [map_add]
    exact (grading R N i).add_mem ihx ihy
  | mem_mul m hm i x hx ih =>
    obtain ⟨m, rfl⟩ := hm
    rw [map_mul, map_ι]
    simpa only [add_comm] using
      (SetLike.mul_mem_graded (ι_mem_grading_one R N (f m)) ih)

/-- The actual algebra equivalence preserves and reflects every intrinsic
degree. In particular it supplies, rather than assumes, the Proj hypothesis. -/
theorem congr_mem_grading_iff (e : M ≃ₗ[R] N) (n : ℕ) (x : SymmetricAlgebra R M) :
    congr e x ∈ grading R N n ↔ x ∈ grading R M n := by
  constructor
  · intro hx
    have h := map_mem_grading e.symm.toLinearMap hx
    change (congr e).symm (congr e x) ∈ grading R M n at h
    simpa only [AlgEquiv.symm_apply_apply] using h
  · exact map_mem_grading e.toLinearMap

end KltDP.SymmetricAlgebra
