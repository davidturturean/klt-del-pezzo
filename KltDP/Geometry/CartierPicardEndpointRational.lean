import KltDP.Geometry.RegularSurfaceWeilPicard
import Mathlib.Algebra.Module.Rat
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Rational Weil divisors and actual Cartier multiples

The rational Cartier space is the rational span of the image of the
constructed Cartier-to-Weil homomorphism. Membership is proved equivalent
to the existence of a positive integral multiple represented by one actual
Cartier divisor. This equivalence clears the denominators in an arbitrary
finite linear combination; it is not the definition of membership.

Every rational Weil divisor has a positive integral multiple in the
original integral divisor group. Consequently all rational Weil divisors
on a regular surface are rational Cartier. The original sheaf, prime-curve
indexing type, and Cartier-to-Weil map are retained throughout.
-/

noncomputable section

universe u v

namespace KltDP.Geometry

section RationalSpan

variable {V : Type v} [AddCommGroup V] [Module ℚ V]

/-- A rational linear combination of elements of an additive subgroup
has a positive integral multiple in that same subgroup. -/
theorem mem_ratSpan_addSubgroup_iff (S : AddSubgroup V) (x : V) :
    x ∈ Submodule.span ℚ (S : Set V) ↔ ∃ n : ℕ, 0 < n ∧ n • x ∈ S := by
  constructor
  · intro hx
    obtain ⟨y, hy, z, hxy⟩ :=
      (IsLocalization.mem_span_iff (nonZeroDivisors ℤ)).mp hx
    have hyS : y ∈ S := by
      change y ∈ (Submodule.span ℤ (S : Set V)).toAddSubgroup at hy
      rwa [Submodule.span_int_eq] at hy
    have hzy : (z : ℤ) • x = y := by
      rw [hxy, ← IsScalarTower.algebraMap_smul ℚ, smul_smul,
        IsLocalization.mk'_spec', map_one, one_smul]
    have hzS : (z : ℤ) • x ∈ S := hzy.symm ▸ hyS
    refine ⟨(z : ℤ).natAbs, Int.natAbs_pos.mpr (nonZeroDivisors.coe_ne_zero z), ?_⟩
    have habs : |(z : ℤ)| • x ∈ S := by
      rcases le_total 0 (z : ℤ) with hz | hz
      · simpa only [abs_of_nonneg hz] using hzS
      · simpa only [abs_of_nonpos hz, neg_smul] using S.neg_mem hzS
    simpa only [← Int.natCast_natAbs, natCast_zsmul] using habs
  · rintro ⟨n, hn, hx⟩
    have h := (Submodule.span ℚ (S : Set V)).smul_mem (n : ℚ)⁻¹
      (Submodule.subset_span hx)
    have hnq : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
    simpa only [← Nat.cast_smul_eq_nsmul ℚ, smul_smul,
      inv_mul_cancel₀ hnq, one_smul] using h

/-- The range formulation retains a witness in the original source
group, rather than only membership in an auxiliary subgroup. -/
theorem mem_ratSpan_range_iff {A : Type*} [AddCommGroup A] (f : A →+ V) (x : V) :
    x ∈ Submodule.span ℚ (Set.range f) ↔
      ∃ n : ℕ, 0 < n ∧ ∃ a : A, f a = n • x := by
  change x ∈ Submodule.span ℚ (f.range : Set V) ↔ _
  rw [mem_ratSpan_addSubgroup_iff]
  rfl

end RationalSpan

namespace NormalProjectiveSurface

variable {k : Type u} [Field k] (X : NormalProjectiveSurface k)

/-- The original integral Weil divisors span all rational Weil divisors.
The proof uses their actual finite prime support. -/
theorem rationalWeilDivisor_mem_span_integral (D : X.RationalWeilDivisor) :
    D ∈ Submodule.span ℚ (Set.range (rationalizeWeilDivisor X)) := by
  classical
  let P := Submodule.span ℚ (Set.range (rationalizeWeilDivisor X))
  have hsum : (∑ C ∈ D.support, Finsupp.single C (D C)) ∈ P := by
    apply Submodule.sum_mem
    intro C hC
    have hC1 : rationalizeWeilDivisor X (Finsupp.single C 1) ∈ P :=
      Submodule.subset_span ⟨Finsupp.single C 1, rfl⟩
    simpa only [rationalizeWeilDivisor_single, Int.cast_one, Finsupp.smul_single,
      smul_eq_mul, mul_one] using P.smul_mem (D C) hC1
  exact (divisor_sum_single D) ▸ hsum

/-- Every rational divisor has an actual integral numerator after
multiplication by some positive integer. No common index is fixed. -/
theorem exists_positive_integral_multiple (D : X.RationalWeilDivisor) :
    ∃ n : ℕ, 0 < n ∧ ∃ A : X.WeilDivisor, rationalizeWeilDivisor X A = n • D :=
  (mem_ratSpan_range_iff (rationalizeWeilDivisor X) D).mp
    (X.rationalWeilDivisor_mem_span_integral D)

/-- Rationalization of the actual geometric Cartier-to-Weil map. -/
def rationalCartierToWeilHom :
    CartierDivisor X.toScheme →+ X.RationalWeilDivisor :=
  (rationalizeWeilDivisor X).comp X.cartierToWeilHom

/-- The rational Cartier space is the rational span of the images of
actual global Cartier divisors. -/
def rationalCartierSubmodule : Submodule ℚ X.RationalWeilDivisor :=
  Submodule.span ℚ (Set.range X.rationalCartierToWeilHom)

/-- A rational Weil divisor is Q-Cartier when it lies in the rational
span of actual Cartier divisors. -/
def QCartier (D : X.RationalWeilDivisor) : Prop :=
  D ∈ X.rationalCartierSubmodule

/-- Q-Cartier membership is equivalent to a positive integral multiple
being the Weil divisor of one actual Cartier divisor. -/
theorem qCartier_iff_exists_positive_multiple (D : X.RationalWeilDivisor) :
    X.QCartier D ↔ ∃ n : ℕ, 0 < n ∧ ∃ A : CartierDivisor X.toScheme,
      rationalizeWeilDivisor X (X.cartierToWeilHom A) = n • D :=
  mem_ratSpan_range_iff X.rationalCartierToWeilHom D

/-- For an integral divisor the criterion is an equality in the
original integral Weil group, proved using injectivity of rationalization. -/
theorem qCartier_integral_iff (D : X.WeilDivisor) :
    X.QCartier (rationalizeWeilDivisor X D) ↔
      ∃ n : ℕ, 0 < n ∧ ∃ A : CartierDivisor X.toScheme,
        X.cartierToWeilHom A = n • D := by
  rw [X.qCartier_iff_exists_positive_multiple]
  constructor
  · rintro ⟨n, hn, A, hA⟩
    refine ⟨n, hn, A, rationalizeWeilDivisor_injective ?_⟩
    exact hA.trans ((rationalizeWeilDivisor X).map_nsmul D n).symm
  · rintro ⟨n, hn, A, hA⟩
    exact ⟨n, hn, A, (congrArg (rationalizeWeilDivisor X) hA).trans
      ((rationalizeWeilDivisor X).map_nsmul D n)⟩

/-- Regularity supplies the actual Cartier representative of the
integral numerator, so every rational Weil divisor is Q-Cartier. -/
theorem qCartier_of_regular [IsAlgClosed k]
    (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)
    (D : X.RationalWeilDivisor) : X.QCartier D := by
  obtain ⟨n, hn, A, hA⟩ := X.exists_positive_integral_multiple D
  apply (X.qCartier_iff_exists_positive_multiple D).mpr
  refine ⟨n, hn, (X.regularCartierWeilEquiv hregular).symm A, ?_⟩
  change rationalizeWeilDivisor X
    (X.regularCartierWeilEquiv hregular ((X.regularCartierWeilEquiv hregular).symm A)) = _
  rw [AddEquiv.apply_symm_apply]
  exact hA

end NormalProjectiveSurface

end KltDP.Geometry
