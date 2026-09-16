import KltDP.Geometry.QuadraticRootIdeals
import Mathlib.LinearAlgebra.FreeModule.Basic

/-!
# Regular branch equations give regular quadratic root equations

A free algebra preserves multiplication-injectivity of a base scalar:
apply its actual basis coordinates. Applied to the proved free quadratic
algebra, the equality t²=b then proves that t is a non-zero-divisor when
the original b is. Together with the actual ideal-square equality, this
is the local regular-equation content required for Cartier multiplicity
two. No normality, domain, or characteristic assumption is introduced.

Reuse: pinned basis coordinates and non-zero-divisor product criteria.
Newer official Mathlib FreeModule/Basic.lean at revision
80cbd0498ab39e21d24d6730b3f932cec672a702:92-94 derives the newer general
IsTorsionFree instance from a basis (Apache 2.0). The pin does not expose
that interface; the scalar statement below follows directly from its
existing coordinate maps, without porting a replacement torsion API.
-/

noncomputable section

namespace KltDP.Geometry.QuadraticCover

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- A non-zero-divisor of the base remains one in any actual free algebra. -/
theorem algebraMap_mem_nonZeroDivisors_of_free [Module.Free R A]
    (r : R) (hr : r ∈ nonZeroDivisors R) :
    algebraMap R A r ∈ nonZeroDivisors A := by
  intro x hx
  let b := Module.Free.chooseBasis R A
  have hs : r • x = 0 := by
    rw [Algebra.smul_def, mul_comm]
    exact hx
  apply b.repr.injective
  apply Finsupp.ext
  intro i
  simp only [map_zero, Finsupp.zero_apply]
  apply hr (b.repr x i)
  have hc := congrArg (fun y : A => b.repr y i) hs
  simpa only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero,
    Finsupp.zero_apply, mul_comm] using hc

/-- The original regular branch equation forces the actual root equation to be regular. -/
theorem root_mem_nonZeroDivisors (s : R) (hs : s ∈ nonZeroDivisors R) :
    root s ∈ nonZeroDivisors (CoverAlgebra s) := by
  letI := free s
  have h := algebraMap_mem_nonZeroDivisors_of_free (A := CoverAlgebra s) s hs
  rw [← root_sq, pow_two, mul_mem_nonZeroDivisors] at h
  exact h.1

/-- Both the regular root equation and its actual ideal multiplicity are derived. -/
theorem regular_branch_pullback (s : R) (hs : s ∈ nonZeroDivisors R) :
    root s ∈ nonZeroDivisors (CoverAlgebra s) ∧
      Ideal.map (algebraMap R (CoverAlgebra s)) (branchIdeal s) = rootIdeal s ^ 2 :=
  ⟨root_mem_nonZeroDivisors s hs, map_branchIdeal_eq_rootIdeal_sq s⟩

end KltDP.Geometry.QuadraticCover
