import KltDP.Examples.FrobeniusMultiCentreCanonicalIdealFamily
import KltDP.Examples.FrobeniusContactTowerCanonicalFactorPicard

/-!
# The actual exceptional tensor has the accepted double-sum Picard class

Pass the original ordered finite tensor through the original sheaf Picard
quotient. Every factor is literally the accepted pulled total exceptional
line. Its negative ideal-line class is the existing exceptionalClass.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusMultiCentreCanonicalIdealClass

open KltDP.Geometry KltDP.Geometry.RationalTreePicard
open FrobeniusContactTowerCanonicalFactorFiniteTensor FrobeniusContactTowerCanonicalFactorPicard
open FrobeniusContactTowerCanonicalFactorTensor FrobeniusMultiCentreSurface
open FrobeniusMultiCentreCanonicalIdealFamily

/-- The negative class of the actual finite tensor is the sum of the same factor classes. -/
theorem family_neg_toPic {X : Scheme.{u}} (n : ℕ) (L : Fin n → InvertibleSheaf X) :
    -Additive.ofMul (familyLine n L).toPic = ∑ j : Fin n, -Additive.ofMul (L j).toPic := by
  induction n with
  | zero =>
      have h : (familyLine 0 L).toPic = 1 := (toPic_eq_one_iff_iso_unit _).mpr ⟨Iso.refl _⟩
      rw [h, ofMul_one, neg_zero, Fin.sum_univ_zero]
  | succ n ih =>
      rw [familyLine, tensorLine_toPic, ofMul_mul, neg_add, ih, Fin.sum_univ_castSucc]

variable {k : Type u} [Field k]

/-- The actual cluster ideal tensor contributes the accepted original total exceptional classes. -/
theorem clusterIdealClass (p n : ℕ) (a : Fin n → k) (i : Fin n) :
    -Additive.ofMul (clusterIdealLine p n a i).toPic =
      ∑ j : Fin p, exceptionalClass p n a i j :=
  family_neg_toPic p _

/-- The actual whole exceptional ideal tensor contributes the full accepted double sum. -/
theorem multiIdealClass (p n : ℕ) (a : Fin n → k) :
    -Additive.ofMul (multiIdealLine p n a).toPic =
      ∑ i : Fin n, ∑ j : Fin p, exceptionalClass p n a i j := by
  rw [multiIdealLine, family_neg_toPic]
  exact Finset.sum_congr rfl (fun i _ => clusterIdealClass p n a i)

end KltDP.Examples.FrobeniusMultiCentreCanonicalIdealClass
