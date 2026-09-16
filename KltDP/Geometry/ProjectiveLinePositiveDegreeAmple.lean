import KltDP.Geometry.ProjectiveLineDegreeOneAmple
import KltDP.Geometry.ProjectiveLineDegreeExponent
import KltDP.Geometry.AmplePositivity

/-!
# Positive Euler degree implies Serre ampleness on the original projective line

The actual degree-one witness and the existing original Picard classification
identify every positive-exponent line bundle with a positive power of that
witness. The accepted Euler-degree comparison gives the intrinsic degree form.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.ProjectiveLinePositiveDegreeAmple

open RationalTreePicard ProjectiveLineSheafExponent
open ProjectiveLineDegreeOneAmple ProjectiveLinePicardExponent

variable (k : Type u) [Field k]

private theorem value_pow (p : (projectiveSpace k 1).Pic) (n : ℕ) :
    value k (p ^ n) = (n : ℤ) * value k p := by
  induction n with
  | zero => rw [pow_zero, value_one]; simp
  | succ n ih =>
    rw [pow_succ, value_mul, ih]
    push_cast
    ring

/-- The original Picard class of an exponent-n line bundle is the n-th
power of the original degree-one class. -/
theorem toPic_eq_degreeOne_pow (L : InvertibleSheaf (projectiveSpace k 1))
    (n : ℕ) (h : exponent k L = (n : ℤ)) :
    L.toPic = (monomialLineBundle k 1).toPic ^ n := by
  apply hom_injective k
  change Multiplicative.ofAdd (value k L.toPic) =
    Multiplicative.ofAdd (value k ((monomialLineBundle k 1).toPic ^ n))
  apply congrArg Multiplicative.ofAdd
  rw [value_toPic, value_pow, value_toPic, monomialLineBundle_exponent, mul_one]
  exact h

/-- Every original line bundle with positive transition exponent is
ample for the already defined coherent-sheaf Serre condition. -/
theorem isAmple_of_exponent_pos (L : InvertibleSheaf (projectiveSpace k 1))
    (h : 0 < exponent k L) : AmpleSerre.IsAmple L := by
  have hn : 0 < (exponent k L).toNat := by omega
  exact AmplePositivity.isAmple_pow (exponent k L).toNat hn
    (toPic_eq_degreeOne_pow k L (exponent k L).toNat
      (Int.toNat_of_nonneg (le_of_lt h)).symm)
    (degreeOne_isAmple k)

/-- Every positive Laurent-monomial line bundle on the original projective
line is Serre ample. -/
theorem monomial_isAmple (n : ℤ) (hn : 0 < n) :
    AmpleSerre.IsAmple (monomialLineBundle k n) := by
  apply isAmple_of_exponent_pos k
  rwa [monomialLineBundle_exponent]

/-- Positive original Euler degree proves Serre ampleness on P¹ over any field. -/
theorem isAmple_of_degree_pos (L : InvertibleSheaf (projectiveSpace k 1))
    (h : 0 < ProjectiveLineDegree.degree k L) : AmpleSerre.IsAmple L := by
  apply isAmple_of_exponent_pos k L
  rwa [ProjectiveLineDegree.degree_eq_exponent] at h

end KltDP.Geometry.ProjectiveLinePositiveDegreeAmple
