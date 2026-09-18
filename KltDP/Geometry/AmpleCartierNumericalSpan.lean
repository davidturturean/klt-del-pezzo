import KltDP.Geometry.CartierDifferenceOfAmple
import KltDP.Geometry.RationalHodgeIndex
import KltDP.Geometry.NefNullCurveNegativeSquare

/-!
# Original ample Cartier classes span the original numerical space

Every original Cartier divisor is a proved difference of actual ample
Cartier divisors. The existing positive-denominator theorem and original
Cartier-to-Picard surjectivity then express every original numerical class
in their rational span. No spanning or numerical-descent premise is supplied.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.CanonicalAmpleSpan

open NefNullCurveNegativeSquare

variable {k : Type u} [Field k] [IsAlgClosed k] (S : NormalProjectiveSurface k)

/-- Numerical classes of actual ample Cartier divisors on the original surface. -/
def ampleClasses : Set S.NumericalClassGroup :=
  {c | ∃ D : CartierDivisor S.toScheme,
    AmpleSerre.IsAmple (cartierDivisorInvertibleSheaf S.toScheme D) ∧ cartierClass S D = c}

variable (hregular : ∀ x : S.Point, RegularPoint S.toScheme x)

include hregular

theorem cartierClass_mem_span_ample (D : CartierDivisor S.toScheme) :
    cartierClass S D ∈ Submodule.span ℚ (ampleClasses S) := by
  obtain ⟨A, B, hA, hB, hD⟩ := exists_difference_of_ample S hregular D
  have hmem := (Submodule.span ℚ (ampleClasses S)).sub_mem
    (Submodule.subset_span ⟨A, hA, rfl⟩) (Submodule.subset_span ⟨B, hB, rfl⟩)
  rw [hD]
  change S.picardNumericalMap (cartierPicardHom S.toScheme (A - B)) ∈ _
  rw [map_sub, map_sub]
  exact hmem

/-- The actual ample Cartier classes span all of the original N1 over Q. -/
theorem span_ampleClasses_eq_top : Submodule.span ℚ (ampleClasses S) = ⊤ := by
  apply top_unique
  intro c _
  obtain ⟨n, hn, p, hp⟩ := S.numericalClass_exists_positive_integral_multiple c
  obtain ⟨D, hD⟩ := cartierPicardHom_surjective S.toScheme p
  have hclass : cartierClass S D = (n : ℚ) • c := by
    change S.picardNumericalMap (cartierPicardHom S.toScheme D) = _
    rw [hD]
    exact hp
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hmem := (Submodule.span ℚ (ampleClasses S)).smul_mem (n : ℚ)⁻¹
    (cartierClass_mem_span_ample S hregular D)
  rw [hclass, smul_smul, inv_mul_cancel₀ hnq, one_smul] at hmem
  exact hmem

end KltDP.Geometry.CanonicalAmpleSpan

#check @KltDP.Geometry.CanonicalAmpleSpan.span_ampleClasses_eq_top
#print axioms KltDP.Geometry.CanonicalAmpleSpan.span_ampleClasses_eq_top
