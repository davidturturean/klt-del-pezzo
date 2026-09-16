import KltDP.Codes.DoublyEven
import Mathlib.LinearAlgebra.BilinearForm.Basic

/-!
# Parity of divisible sums of orthogonal nodes

These lemmas concern an actual integer-valued bilinear form on a module.
The vectors have square minus two and are pairwise orthogonal. If their
sum is twice an integral vector, its square and pairing with a perpendicular
characteristic vector are determined. The characteristic parity condition
then forces the number of summands to be divisible by four.

This supplies the algebraic adapter in manuscript `lem:picard-parity`.
Identifying the module with the actual Picard group, obtaining divisibility
from its index, and deriving characteristic parity from Riemann--Roch remain
separate geometric obligations.
-/

namespace KltDP.Codes

open scoped BigOperators

variable {M ι : Type*} [AddCommGroup M] [Module ℤ M]

/-- An integral vector is characteristic when its pairing gives the parity
of every integral square. This is a property of the actual bilinear form. -/
def IsCharacteristic (B : LinearMap.BilinForm ℤ M) (K : M) : Prop :=
  ∀ x, Even (B x x - B K x)

/-- Squaring a finite orthogonal sum of vectors of square minus two. -/
theorem orthogonalNodeSum_square (B : LinearMap.BilinForm ℤ M)
    (w : ι → M) (s : Finset ι)
    (hsq : ∀ i ∈ s, B (w i) (w i) = -2)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → B (w i) (w j) = 0) :
    B (∑ i ∈ s, w i) (∑ i ∈ s, w i) = -2 * (s.card : ℤ) := by
  classical
  simp only [map_sum, LinearMap.sum_apply]
  have hrow : ∀ i ∈ s, (∑ j ∈ s, B (w i) (w j)) = -2 := by
    intro i hi
    rw [Finset.sum_eq_single i]
    · exact hsq i hi
    · intro j hj hji
      exact horth i hi j hj (Ne.symm hji)
    · exact fun h => (h hi).elim
  rw [Finset.sum_comm, Finset.sum_congr rfl hrow]
  simp [mul_comm]

/-- Twice an integral half-sum has four times its square. -/
theorem nodeHalfSum_square (B : LinearMap.BilinForm ℤ M)
    (w : ι → M) (s : Finset ι) (m : M)
    (hsq : ∀ i ∈ s, B (w i) (w i) = -2)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → B (w i) (w j) = 0)
    (hm : (2 : ℤ) • m = ∑ i ∈ s, w i) :
    2 * B m m = -(s.card : ℤ) := by
  have h := orthogonalNodeSum_square B w s hsq horth
  rw [← hm] at h
  simp only [two_zsmul, map_add, LinearMap.add_apply] at h
  linarith

/-- A half-sum remains perpendicular to every vector perpendicular to its
summands, since the form takes values in the torsion-free group of integers. -/
theorem nodeHalfSum_pairing_zero (B : LinearMap.BilinForm ℤ M)
    (K : M) (w : ι → M) (s : Finset ι) (m : M)
    (hK : ∀ i ∈ s, B K (w i) = 0)
    (hm : (2 : ℤ) • m = ∑ i ∈ s, w i) : B K m = 0 := by
  have h := congrArg (fun x => B K x) hm
  change B K ((2 : ℤ) • m) = B K (∑ i ∈ s, w i) at h
  simp only [two_zsmul, map_add, map_sum] at h
  have hz : (∑ i ∈ s, B K (w i)) = 0 := Finset.sum_eq_zero hK
  rw [hz] at h
  linarith

/-- Characteristic parity forces four-divisibility of an integral node
half-sum's number of summands. -/
theorem four_dvd_card_of_nodeHalfSum (B : LinearMap.BilinForm ℤ M)
    (K : M) (hchar : IsCharacteristic B K) (w : ι → M) (s : Finset ι)
    (hsq : ∀ i ∈ s, B (w i) (w i) = -2)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → B (w i) (w j) = 0)
    (hK : ∀ i ∈ s, B K (w i) = 0)
    (hdiv : ∃ m : M, (2 : ℤ) • m = ∑ i ∈ s, w i) : 4 ∣ s.card := by
  obtain ⟨m, hm⟩ := hdiv
  have hsqsum := nodeHalfSum_square B w s m hsq horth hm
  have hzero := nodeHalfSum_pairing_zero B K w s m hK hm
  have heven := hchar m
  rw [hzero, sub_zero] at heven
  obtain ⟨a, ha⟩ := heven
  apply Int.natCast_dvd_natCast.mp
  refine ⟨-a, ?_⟩
  push_cast
  linarith

/-- The actual support of a divisible binary node word has doubly-even
Hamming weight. This does not assume the collection is a linear code. -/
theorem doublyEvenWord_of_nodeHalfSum [Fintype ι]
    (B : LinearMap.BilinForm ℤ M) (K : M) (hchar : IsCharacteristic B K)
    (w : ι → M) (x : BinaryWord ι)
    (hsq : ∀ i, B (w i) (w i) = -2)
    (horth : ∀ i j, i ≠ j → B (w i) (w j) = 0)
    (hK : ∀ i, B K (w i) = 0)
    (hdiv : ∃ m : M, (2 : ℤ) • m =
      ∑ i ∈ Finset.univ.filter (fun j => x j ≠ 0), w i) :
    DoublyEvenWord x := by
  classical
  exact four_dvd_card_of_nodeHalfSum B K hchar w _
    (fun i _ => hsq i) (fun i _ j _ hij => horth i j hij)
    (fun i _ => hK i) hdiv

end KltDP.Codes
