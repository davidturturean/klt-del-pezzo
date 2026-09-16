/-
Copyright (c) 2026 KltDP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import KltDP.Compatibility.SymmetricAlgebra.Basis
import KltDP.Compatibility.SymmetricAlgebra.Grading
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# The original basis equivalence preserves the intrinsic symmetric degree

The source grading is by powers of the range of the actual module inclusion.
The target is the pinned homogeneous polynomial grading. Preservation follows
from the original inclusion and multiplication; reflection follows from the
uniqueness of homogeneous decomposition. Thus no chosen polynomial grading is
transported back as a definition, and no degree-preservation witness is assumed.

No finiteness, nonempty basis, projective-space identification or projectivity
hypothesis is required. Scheme-level Proj transport remains a separate result.
-/

noncomputable section

namespace KltDP.SymmetricAlgebra

universe uκ uτ uR uM

variable {κ : Type uκ} {τ : Type uτ} {R : Type uR} {M : Type uM}
variable [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The polynomial image of every actual module element has degree one. -/
theorem equivMvPolynomial_ι_mem_homogeneous (b : Basis κ R M) (m : M) :
    equivMvPolynomial b (ι R M m) ∈ MvPolynomial.homogeneousSubmodule κ R 1 := by
  classical
  change lift (Basis.constr b R MvPolynomial.X) (ι R M m) ∈ _
  rw [lift_ι_apply, Basis.constr_apply]
  exact (MvPolynomial.homogeneousSubmodule κ R 1).sum_mem fun i _ =>
    (MvPolynomial.homogeneousSubmodule κ R 1).smul_mem _
      (MvPolynomial.isHomogeneous_X R i)

/-- The actual basis equivalence preserves every intrinsic symmetric degree. -/
theorem equivMvPolynomial_mem_homogeneous (b : Basis κ R M) {n : ℕ}
    {x : SymmetricAlgebra R M} (hx : x ∈ grading R M n) :
    equivMvPolynomial b x ∈ MvPolynomial.homogeneousSubmodule κ R n := by
  change x ∈ LinearMap.range (ι R M) ^ n at hx
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    rw [(equivMvPolynomial b).commutes r]
    exact MvPolynomial.isHomogeneous_C κ r
  | add x y i hx hy ihx ihy =>
    rw [map_add]
    exact (MvPolynomial.homogeneousSubmodule κ R i).add_mem ihx ihy
  | mem_mul m hm i x hx ih =>
    obtain ⟨m, rfl⟩ := hm
    rw [map_mul]
    simpa only [add_comm] using
      (MvPolynomial.IsHomogeneous.mul (equivMvPolynomial_ι_mem_homogeneous b m) ih)

/-- The actual polynomial homogeneous component is the image of the original
symmetric homogeneous component. -/
theorem equivMvPolynomial_proj (b : Basis κ R M) (n : ℕ)
    (x : SymmetricAlgebra R M) :
    equivMvPolynomial b (_root_.GradedAlgebra.proj (grading R M) n x) =
      MvPolynomial.homogeneousComponent n (equivMvPolynomial b x) := by
  have h : (MvPolynomial.homogeneousComponent n).comp
        (equivMvPolynomial b).toLinearEquiv.toLinearMap =
      (equivMvPolynomial b).toLinearEquiv.toLinearMap.comp
        (_root_.GradedAlgebra.proj (grading R M) n) := by
    apply DirectSum.decompose_lhom_ext (grading R M)
    intro i
    apply LinearMap.ext
    intro y
    change MvPolynomial.homogeneousComponent n (equivMvPolynomial b y.val) =
      equivMvPolynomial b (_root_.GradedAlgebra.proj (grading R M) n y.val)
    rw [MvPolynomial.homogeneousComponent_of_mem
      (equivMvPolynomial_mem_homogeneous b y.property), _root_.GradedAlgebra.proj_apply]
    by_cases hi : n = i
    · subst i
      rw [if_pos rfl, DirectSum.decompose_of_mem_same (grading R M) y.property]
    · rw [if_neg hi,
        DirectSum.decompose_of_mem_ne (grading R M) y.property (Ne.symm hi), map_zero]
  exact (LinearMap.congr_fun h x).symm

/-- Degree membership is reflected as well as preserved by the actual basis
equivalence. The zero-dimensional module and empty basis are included. -/
theorem equivMvPolynomial_mem_homogeneous_iff (b : Basis κ R M) (n : ℕ)
    (x : SymmetricAlgebra R M) :
    equivMvPolynomial b x ∈ MvPolynomial.homogeneousSubmodule κ R n ↔
      x ∈ grading R M n := by
  refine ⟨fun hx => ?_, equivMvPolynomial_mem_homogeneous b⟩
  have heq : _root_.GradedAlgebra.proj (grading R M) n x = x := by
    apply (equivMvPolynomial b).injective
    rw [equivMvPolynomial_proj, MvPolynomial.homogeneousComponent_of_mem hx, if_pos rfl]
  have hmem : _root_.GradedAlgebra.proj (grading R M) n x ∈ grading R M n := by
    rw [_root_.GradedAlgebra.proj_apply]
    exact (DirectSum.decompose (grading R M) x n).property
  exact heq ▸ hmem

/-- Changing the basis preserves the polynomial grading because both coordinate
maps identify it with the same intrinsic symmetric grading. -/
theorem basisChange_mem_homogeneous_iff (b : Basis κ R M) (c : Basis τ R M)
    (n : ℕ) (p : MvPolynomial κ R) :
    equivMvPolynomial c ((equivMvPolynomial b).symm p) ∈
        MvPolynomial.homogeneousSubmodule τ R n ↔
      p ∈ MvPolynomial.homogeneousSubmodule κ R n := by
  rw [equivMvPolynomial_mem_homogeneous_iff]
  simpa only [AlgEquiv.apply_symm_apply] using
    (equivMvPolynomial_mem_homogeneous_iff b n ((equivMvPolynomial b).symm p)).symm

end KltDP.SymmetricAlgebra
