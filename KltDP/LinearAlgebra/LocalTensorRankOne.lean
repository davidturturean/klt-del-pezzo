import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.RingTheory.LocalRing.Basic

/-!
# Tensor-invertible modules over a local ring

An actual linear equivalence `M ⊗[R] N ≃ₗ[R] R` over a commutative local
ring makes `M` linearly equivalent to `R`. No finite generation, freeness,
projectivity, or rank hypothesis is assumed.

The proof uses the pinned tensor induction principle to find a pure tensor
whose image is a unit. After normalizing that image to one, evaluation at
its second factor is bijective. Its injectivity follows by applying a
tensor map and the right unitor to an equality of pure tensors.

Reuse assessment: Mathlib's `RingTheory/PicardGroup.lean` at revision
`5aedf732b6987e8c26ab3c9ebc855314f82b045f` (Apache 2.0) provides a more
general invertible-module API. The closest route is `Module.Invertible.left`,
`Module.Invertible.free_iff_linearEquiv`, and the local-ring subsingleton
Picard instance (newer file lines 530–542). Direct import is unavailable at
this pin; preserving that route would also port its canonical-dual,
tensor-equivalence, finite/projective and Picard representative machinery.
The four lemmas below isolate the concrete tensor-isomorphism adapter using
existing pinned contraction and local-ring APIs. They are not an unchanged
port of the newer proof. The exact missing imports and bounded-port tradeoff
are recorded in `docs/PICARD_CONVERSE_PORT_ASSESSMENT.md`.
This is a module theorem. Applying it to sheaves requires a separately
proved passage from a sheaf tensor product to the relevant module tensor
product.
-/

namespace KltDP.LinearAlgebra.LocalTensorRankOne

open scoped TensorProduct

universe u v w

variable {R : Type u} [CommRing R]
  {M : Type v} {N : Type w}
  [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

/-- If a pure tensor maps to one under a tensor equivalence, pairing with
its second factor is a bijection from the first module to the ring. -/
theorem bijective_pairing_of_pairing_eq_one
    (e : M ⊗[R] N ≃ₗ[R] R) (m : M) (n : N)
    (h : e (m ⊗ₜ[R] n) = 1) :
    Function.Bijective ((TensorProduct.curry e.toLinearMap).flip n) := by
  let q : N →ₗ[R] R := TensorProduct.curry e.toLinearMap m
  have hq : q n = 1 := h
  constructor
  · intro x y hxy
    have ht : x ⊗ₜ[R] n = y ⊗ₜ[R] n := e.injective hxy
    have hmap := congrArg
      (fun z => TensorProduct.rid R M
        (TensorProduct.map (LinearMap.id : M →ₗ[R] M) q z)) ht
    simpa only [TensorProduct.map_tmul, LinearMap.id_apply,
      TensorProduct.rid_tmul, hq, one_smul] using hmap
  · intro r
    refine ⟨r • m, ?_⟩
    change e ((r • m) ⊗ₜ[R] n) = r
    rw [← TensorProduct.smul_tmul', map_smul, h, smul_eq_mul, mul_one]

/-- The same pairing is bijective when the pure tensor maps to any unit.
Only the first factor needs to be rescaled to normalize its image. -/
theorem bijective_pairing_of_unit_pair
    (e : M ⊗[R] N ≃ₗ[R] R) (m : M) (n : N)
    (hu : IsUnit (e (m ⊗ₜ[R] n))) :
    Function.Bijective ((TensorProduct.curry e.toLinearMap).flip n) := by
  obtain ⟨r, hr⟩ := hu.exists_left_inv
  apply bijective_pairing_of_pairing_eq_one e (r • m) n
  rw [← TensorProduct.smul_tmul', map_smul, smul_eq_mul, hr]

/-- Over a local ring, a tensor equivalence has a pure tensor whose image
is a unit. Tensor induction uses that a unit sum has a unit summand. -/
theorem exists_unit_pair [IsLocalRing R]
    (e : M ⊗[R] N ≃ₗ[R] R) :
    ∃ m : M, ∃ n : N, IsUnit (e (m ⊗ₜ[R] n)) := by
  have H : ∀ z : M ⊗[R] N,
      IsUnit (e z) → ∃ m : M, ∃ n : N, IsUnit (e (m ⊗ₜ[R] n)) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero =>
        intro hz
        have hzero : IsUnit (0 : R) := by simpa only [map_zero] using hz
        exact (not_isUnit_zero hzero).elim
    | tmul m n =>
        intro hz
        exact ⟨m, n, hz⟩
    | add x y hx hy =>
        intro hz
        rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add
          (a := e x) (b := e y)
          (by simpa only [map_add] using hz) with hx' | hy'
        · exact hx hx'
        · exact hy hy'
  exact H (e.symm 1) (by simp)

/-- A module with a tensor inverse over a commutative local ring is
linearly equivalent to the ring, with no finiteness assumptions. -/
theorem nonempty_linearEquiv_ring [IsLocalRing R]
    (e : M ⊗[R] N ≃ₗ[R] R) : Nonempty (M ≃ₗ[R] R) := by
  obtain ⟨m, n, hu⟩ := exists_unit_pair e
  exact ⟨LinearEquiv.ofBijective
    ((TensorProduct.curry e.toLinearMap).flip n)
    (bijective_pairing_of_unit_pair e m n hu)⟩

end KltDP.LinearAlgebra.LocalTensorRankOne
