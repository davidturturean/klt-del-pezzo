import KltDP.Examples.FrobeniusMultiCentreExceptionalTotalMatrix
import KltDP.Examples.FrobeniusPicard

/-!
# The manuscript's integral lattice maps faithfully into the actual Picard group

Send the two ruling coordinates and each exceptional coordinate to the original
global Picard classes. The computed geometric matrix proves that this additive
map preserves the manuscript's pairing and is injective. No pairing or basis
correspondence is assumed. Surjectivity onto the entire Picard group is a
separate geometric obligation and is not asserted here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusMultiCentrePicardRealization

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
  FrobeniusMultiCentreGraphExceptionalPairing
  FrobeniusMultiCentreGraphFiberNumericalValues
  FrobeniusMultiCentreRulingPairing FrobeniusMultiCentreExceptionalRulingRows
  FrobeniusMultiCentreExceptionalTotalMatrix

variable {k : Type u} [Field k] (q n : ℕ) (a : Fin n → k)

/-- The original ruling and total-exceptional classes realize the integral lattice in `Pic S`. -/
def realization : FrobeniusPicard.PicardVector (q + 1) n →+
    Additive (multiSurface (q + 1) n a).Pic where
  toFun x := x.1 • multiFirstFiberClass (q + 1) n a +
    x.2.1 • multiSecondFiberClass (q + 1) n a +
      ∑ i : Fin n, ∑ j : Fin (q + 1), x.2.2 (i, j) • exceptionalClass (q + 1) n a i j
  map_zero' := by simp
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_smul,
      Finset.sum_add_distrib]
    abel

theorem realization_apply (x : FrobeniusPicard.PicardVector (q + 1) n) :
    realization q n a x = x.1 • multiFirstFiberClass (q + 1) n a +
      x.2.1 • multiSecondFiberClass (q + 1) n a +
        ∑ i : Fin n, ∑ j : Fin (q + 1), x.2.2 (i, j) • exceptionalClass (q + 1) n a i j := rfl

variable [IsAlgClosed k] (ha : Function.Injective a)
  [Fact (q + 1).Prime] [CharP k (q + 1)]
  (hproj : IsProjectiveOverField (multiStructure (q + 1) n a))

/-- Expand the actual bilinear pairing on a realized lattice vector. -/
theorem realization_pairing (x : FrobeniusPicard.PicardVector (q + 1) n)
    (y : Additive (multiSurface (q + 1) n a).Pic) :
    multiPairing (q + 1) n a ha hproj (realization q n a x) y =
      x.1 * multiPairing (q + 1) n a ha hproj (multiFirstFiberClass (q + 1) n a) y +
        x.2.1 * multiPairing (q + 1) n a ha hproj (multiSecondFiberClass (q + 1) n a) y +
        ∑ i : Fin n, ∑ j : Fin (q + 1), x.2.2 (i, j) *
          multiPairing (q + 1) n a ha hproj (exceptionalClass (q + 1) n a i j) y := by
  let f := multiPairingHom q n a ha hproj y
  change f (realization q n a x) = _
  rw [realization_apply, map_add, map_add]
  simp only [map_sum, map_zsmul, zsmul_eq_mul]
  rfl

/-- Pairing with the original first ruling recovers the second coordinate. -/
theorem realization_pairing_first (x : FrobeniusPicard.PicardVector (q + 1) n) :
    multiPairing (q + 1) n a ha hproj
      (realization q n a x) (multiFirstFiberClass (q + 1) n a) = x.2.1 := by
  rw [realization_pairing]
  simp only [multiPairing_first_self_zero, multiPairing_second_first_one,
    totalClass_firstFiber_pairing_zero, mul_zero, mul_one, Finset.sum_const_zero,
    zero_add, add_zero]

/-- Pairing with the original second ruling recovers the first coordinate. -/
theorem realization_pairing_second (x : FrobeniusPicard.PicardVector (q + 1) n) :
    multiPairing (q + 1) n a ha hproj
      (realization q n a x) (multiSecondFiberClass (q + 1) n a) = x.1 := by
  rw [realization_pairing]
  simp only [multiPairing_first_second_one, multiPairing_second_self_zero,
    totalClass_secondFiber_pairing_zero, mul_zero, mul_one, Finset.sum_const_zero, add_zero]

/-- Pairing with an original total exceptional class recovers minus its coefficient. -/
theorem realization_pairing_exceptional (x : FrobeniusPicard.PicardVector (q + 1) n)
    (i : Fin n) (j : Fin (q + 1)) :
    multiPairing (q + 1) n a ha hproj
      (realization q n a x) (exceptionalClass (q + 1) n a i j) = -x.2.2 (i, j) := by
  classical
  rw [realization_pairing]
  simp only [firstFiber_totalClass_pairing_zero, secondFiber_totalClass_pairing_zero,
    totalClass_pairing, mul_zero, zero_add]
  simp only [ite_and, mul_ite, mul_neg, mul_one, mul_zero]
  simp

/-- The accepted lattice form is exactly the geometric pairing of the original Picard classes. -/
theorem realization_preserves_pairing (x y : FrobeniusPicard.PicardVector (q + 1) n) :
    multiPairing (q + 1) n a ha hproj (realization q n a x) (realization q n a y) =
      FrobeniusPicard.pairing x y := by
  rw [realization_pairing]
  have hfirst : multiPairing (q + 1) n a ha hproj (multiFirstFiberClass (q + 1) n a)
      (realization q n a y) = y.2.1 := by
    rw [multiPairing_symm, realization_pairing_first]
  have hsecond : multiPairing (q + 1) n a ha hproj (multiSecondFiberClass (q + 1) n a)
      (realization q n a y) = y.1 := by
    rw [multiPairing_symm, realization_pairing_second]
  have he (i : Fin n) (j : Fin (q + 1)) :
      multiPairing (q + 1) n a ha hproj (exceptionalClass (q + 1) n a i j)
        (realization q n a y) = -y.2.2 (i, j) := by
    rw [multiPairing_symm, realization_pairing_exceptional]
  simp only [hfirst, hsecond, he, mul_neg, Finset.sum_neg_distrib]
  simp only [FrobeniusPicard.pairing, Fintype.sum_prod_type, sub_eq_add_neg]

include ha hproj in
/-- The original geometric classes have no nonzero integral lattice relation. -/
theorem realization_injective : Function.Injective (realization q n a) := by
  intro x y hxy
  have hx : x.1 = y.1 := by
    have h := congrArg (fun c => multiPairing (q + 1) n a ha hproj c
      (multiSecondFiberClass (q + 1) n a)) hxy
    simpa only [realization_pairing_second] using h
  have hy : x.2.1 = y.2.1 := by
    have h := congrArg (fun c => multiPairing (q + 1) n a ha hproj c
      (multiFirstFiberClass (q + 1) n a)) hxy
    simpa only [realization_pairing_first] using h
  apply Prod.ext hx
  apply Prod.ext hy
  funext ij
  have h := congrArg (fun c => multiPairing (q + 1) n a ha hproj c
    (exceptionalClass (q + 1) n a ij.1 ij.2)) hxy
  simp only [realization_pairing_exceptional] at h
  exact neg_injective h

end KltDP.Examples.FrobeniusMultiCentrePicardRealization
