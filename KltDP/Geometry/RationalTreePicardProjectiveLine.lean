import KltDP.Geometry.RationalTreePicardProjectiveLineCocycle
import KltDP.Geometry.ProjectiveLinePicardExponent

/-!
# Every integer occurs as an actual projective-line Picard exponent

The Laurent monomial T^n gives an original overlap unit and hence an actual
invertible sheaf on the two standard opens. Its previously defined invariant
is n. Combining this construction with the existing injectivity theorem
identifies the actual tensor Picard group with the integers. The invariant
here remains the original transition exponent; comparison with independently
defined divisor degree is a separate obligation.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.RationalTreePicard

open ProjectiveLineComparison ProjectiveLineSections
open ProjectiveLineTransitionExponent ProjectiveLineTransitionExtension
open TransitionUnitGluing

variable (k : Type u) [Field k]

/-- The actual overlap section corresponding to the Laurent monomial T^n. -/
def monomialOverlapUnit (n : ℤ) : Γ(projectiveSpace k 1, overlapOpen k)ˣ :=
  Units.map (overlapSectionsEquiv k).symm.toRingHom.toMonoidHom
    (LaurentPolynomial.isUnit_T (R := k) n).unit

/-- The same actual section on the equal intersection of the standard opens. -/
def monomialIntersectionUnit (n : ℤ) :
    Γ(projectiveSpace k 1, chartOpen k 0 ⊓ chartOpen k 1)ˣ :=
  Units.map (res (projectiveSpace k 1) (overlapOpen_eq_inf k).ge).toMonoidHom
    (monomialOverlapUnit k n)

theorem overlapRestriction_monomialIntersectionUnit (n : ℤ) :
    overlapRestriction k (monomialIntersectionUnit k n) = monomialOverlapUnit k n := by
  apply Units.ext
  change res (projectiveSpace k 1) (overlapOpen_eq_inf k).le
      (res (projectiveSpace k 1) (overlapOpen_eq_inf k).ge
        (monomialOverlapUnit k n : Γ(projectiveSpace k 1, overlapOpen k))) = _
  rw [res_res, res_self]

/-- The original Laurent-coordinate definition computes the specified integer. -/
theorem overlapExponent_monomialOverlapUnit (n : ℤ) :
    overlapExponent k (monomialOverlapUnit k n) = n := by
  apply unitExponent_eq_of_monomial k _ 1 n
  change overlapSectionsEquiv k
      ((overlapSectionsEquiv k).symm
        ((LaurentPolynomial.isUnit_T (R := k) n).unit : LaurentPolynomial k)) =
    LaurentPolynomial.C (1 : k) * LaurentPolynomial.T n
  rw [RingEquiv.apply_symm_apply, IsUnit.unit_spec, map_one, one_mul]

/-- The arbitrary-integer cocycle on the original standard chart cover. -/
def monomialCocycle (n : ℤ) :=
  twoOpenUnits (projectiveSpace k 1) (standardOpens k) (monomialIntersectionUnit k n)

theorem monomialCocycle_isCocycle (n : ℤ) :
    IsCocycle (projectiveSpace k 1) (standardOpens k) (monomialCocycle k n) :=
  twoOpenUnits_isCocycle (projectiveSpace k 1) (standardOpens k)
    (monomialIntersectionUnit k n)

theorem monomialCocycle_exponent (n : ℤ) : cocycleExponent k (monomialCocycle k n) = n := by
  change overlapExponent k (overlapRestriction k (monomialIntersectionUnit k n)) = n
  rw [overlapRestriction_monomialIntersectionUnit, overlapExponent_monomialOverlapUnit]

/-- The actual invertible sheaf obtained by gluing with transition T^n. -/
def monomialLineBundle (n : ℤ) : InvertibleSheaf (projectiveSpace k 1) :=
  invertibleSheaf (projectiveSpace k 1) (standardOpens k) (monomialCocycle k n)
    (monomialCocycle_isCocycle k n)
    (ProjectiveLineSheafExponent.standardCover k
      (InvertibleSheaf.trivial (projectiveSpace k 1)))

/-- Its actual Picard exponent is the prescribed integer. -/
theorem monomialLineBundle_exponent (n : ℤ) :
    ProjectiveLineSheafExponent.exponent k (monomialLineBundle k n) = n :=
  (ProjectiveLineSheafExponent.exponent_eq_of_iso_to_glued k (monomialLineBundle k n)
    (monomialCocycle k n) (monomialCocycle_isCocycle k n) (Iso.refl _)).trans
      (monomialCocycle_exponent k n)

/-- The original Picard-group exponent homomorphism is surjective. -/
theorem projectiveLinePicardExponent_surjective :
    Function.Surjective (ProjectiveLinePicardExponent.hom k) := by
  intro n
  refine ⟨(monomialLineBundle k (Multiplicative.toAdd n)).toPic, ?_⟩
  change Multiplicative.ofAdd
      (ProjectiveLinePicardExponent.value k (monomialLineBundle k (Multiplicative.toAdd n)).toPic) = n
  rw [ProjectiveLinePicardExponent.value_toPic, monomialLineBundle_exponent]
  rfl

/-- An isomorphism from the actual tensor Picard group to the additive
integers, written with Mathlib's multiplicative type tag. -/
def projectiveLinePicardExponentEquiv : (projectiveSpace k 1).Pic ≃* Multiplicative ℤ :=
  MulEquiv.ofBijective (ProjectiveLinePicardExponent.hom k)
    ⟨ProjectiveLinePicardExponent.hom_injective k, projectiveLinePicardExponent_surjective k⟩

end KltDP.Geometry.RationalTreePicard
