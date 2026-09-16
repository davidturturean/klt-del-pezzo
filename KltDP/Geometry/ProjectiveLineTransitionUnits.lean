import KltDP.Geometry.ProjectiveLineSections
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Degree.Units
import Mathlib.Algebra.GroupWithZero.Associated

/-!
# Units on the actual projective-line charts and overlap

The pinned localization and prime-power divisor theorems give the Laurent-unit
normal form. Transporting this along the actual structure-sheaf section
equivalences identifies overlap units with scalar Laurent monomials. Units on
either affine chart are constants.

These are statements about sections. No line-bundle gluing, Picard group
comparison, or compatibility with geometric divisor degree is assumed.
-/

noncomputable section

open AlgebraicGeometry

universe u

namespace KltDP.Geometry.ProjectiveLineTransitionUnits

open ProjectiveLineComparison ProjectiveLineSections

variable (k : Type u) [Field k]

/-- Localization at X and primality of X classify the Laurent units. -/
theorem exists_scalar_mul_T_of_isUnit (f : LaurentPolynomial k) (hf : IsUnit f) :
    ∃ (c : k) (_ : IsUnit c) (n : ℤ),
      f = LaurentPolynomial.C c * LaurentPolynomial.T n := by
  obtain ⟨n, p, hp⟩ := LaurentPolynomial.exists_T_pow f
  have hpunit : IsUnit (algebraMap (Polynomial k) (LaurentPolynomial k) p) := by
    rw [LaurentPolynomial.algebraMap_eq_toLaurent, hp]
    exact hf.mul (LaurentPolynomial.isUnit_T n)
  obtain ⟨m, hm⟩ := (IsLocalization.Away.algebraMap_isUnit_iff
    (S := LaurentPolynomial k) (Polynomial.X : Polynomial k)).mp hpunit
  obtain ⟨i, _, hi⟩ := (dvd_prime_pow (Polynomial.prime_X (R := k)) m).mp hm
  obtain ⟨v, hv⟩ := hi.symm
  obtain ⟨c, hc, hcv⟩ := Polynomial.isUnit_iff.mp v.isUnit
  have hpm : p = Polynomial.C c * Polynomial.X ^ i := by
    rw [← hv, ← hcv, mul_comm]
  have he := congrArg (fun z : LaurentPolynomial k =>
    z * LaurentPolynomial.T (-(n : ℤ))) hp
  rw [hpm, Polynomial.toLaurent_C_mul_X_pow] at he
  simp only [LaurentPolynomial.mul_T_assoc, add_neg_cancel,
    LaurentPolynomial.T_zero, mul_one] at he
  exact ⟨c, hc, (i : ℤ) - (n : ℤ), by simpa only [sub_eq_add_neg] using he.symm⟩

theorem isUnit_iff_scalar_mul_T (f : LaurentPolynomial k) :
    IsUnit f ↔ ∃ (c : k) (_ : IsUnit c) (n : ℤ),
      f = LaurentPolynomial.C c * LaurentPolynomial.T n := by
  refine ⟨exists_scalar_mul_T_of_isUnit k f, ?_⟩
  rintro ⟨c, hc, n, rfl⟩
  exact (hc.map LaurentPolynomial.C).mul (LaurentPolynomial.isUnit_T n)

/-- Every unit of the actual overlap section ring is a scalar Laurent monomial. -/
theorem overlap_unit_normal_form (s : Γ(projectiveSpace k 1, overlapOpen k)ˣ) :
    ∃ (c : kˣ) (n : ℤ),
      overlapSectionsEquiv k (s : Γ(projectiveSpace k 1, overlapOpen k)) =
        LaurentPolynomial.C (c : k) * LaurentPolynomial.T n := by
  obtain ⟨c, hc, n, hn⟩ := exists_scalar_mul_T_of_isUnit k _
    (s.isUnit.map (overlapSectionsEquiv k).toRingHom)
  obtain ⟨c, rfl⟩ := hc
  exact ⟨c, n, hn⟩

/-- Units on the first actual affine chart have constant polynomial coordinates. -/
theorem left_chart_unit_constant (s : Γ(projectiveSpace k 1, chartOpen k 0)ˣ) :
    ∃ c : kˣ, leftSectionsEquiv k (s : Γ(projectiveSpace k 1, chartOpen k 0)) =
      Polynomial.C (c : k) := by
  obtain ⟨c, hc, he⟩ := Polynomial.isUnit_iff.mp
    (s.isUnit.map (leftSectionsEquiv k).toRingHom)
  obtain ⟨c, rfl⟩ := hc
  exact ⟨c, he.symm⟩

/-- Units on the second actual affine chart have constant polynomial coordinates. -/
theorem right_chart_unit_constant (s : Γ(projectiveSpace k 1, chartOpen k 1)ˣ) :
    ∃ c : kˣ, rightSectionsEquiv k (s : Γ(projectiveSpace k 1, chartOpen k 1)) =
      Polynomial.C (c : k) := by
  obtain ⟨c, hc, he⟩ := Polynomial.isUnit_iff.mp
    (s.isUnit.map (rightSectionsEquiv k).toRingHom)
  obtain ⟨c, rfl⟩ := hc
  exact ⟨c, he.symm⟩

end KltDP.Geometry.ProjectiveLineTransitionUnits
