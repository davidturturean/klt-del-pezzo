import KltDP.Compatibility.NormalGoingDown
import KltDP.Compatibility.PolynomialMaximalHeight
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# Full height of maximal ideals in finite-type domains

For a finite-type domain over an algebraically closed field, every actual
maximal ideal has height equal to the ring's Krull dimension. Pinned
Noether normalization supplies an actual integral injective polynomial
algebra map. Integral incomparability bounds the ring dimension from above
by the number of variables. The explicit polynomial maximal-prime chain
and proved normal-base going down bound the maximal height from below by
the same number.

The resulting theorem is the algebraic ingredient of Stacks 00OS needed
here. It is proved using actual prime ideals and algebra maps; the
dimension equality is not a literature axiom. This version explicitly
retains the algebraically closed field hypothesis of the reused
polynomial maximal-height proof.
-/

noncomputable section

namespace KltDP.Compatibility

section GoingDownHeight

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.HasGoingDown R S]

/-- Going down transfers every finite lower bound for the contracted
prime height to the actual prime above it. -/
theorem nat_le_primeHeight_of_hasGoingDown (n : ℕ) (Q : Ideal S) [Q.IsPrime]
    (hn : (n : ℕ∞) ≤ (Q.under R).primeHeight) : (n : ℕ∞) ≤ Q.primeHeight := by
  induction n generalizing Q with
  | zero => exact zero_le _
  | succ n ih =>
    let q : PrimeSpectrum R := ⟨Q.under R, inferInstance⟩
    have hnlt : (n : ℕ∞) < Order.height q := by
      apply (ENat.add_one_le_iff (by simp : (n : ℕ∞) ≠ ⊤)).mp
      simpa only [Nat.cast_add, Nat.cast_one] using hn
    have hex : ∃ p : PrimeSpectrum R, p < q ∧ (n : ℕ∞) ≤ Order.height p := by
      by_contra! hnone
      have hqle : Order.height q ≤ (n : ℕ∞) :=
        (Order.height_le_coe_iff (x := q) (n := n)).mpr hnone
      exact hnlt.not_le hqle
    obtain ⟨p, hpq, hnp⟩ := hex
    letI : p.asIdeal.IsPrime := p.isPrime
    obtain ⟨P, hPQ, hP, hPover⟩ :=
      Ideal.exists_ideal_lt_liesOver_of_lt (p := p.asIdeal) (q := Q.under R) Q hpq
    letI : P.IsPrime := hP
    letI : P.LiesOver p.asIdeal := hPover
    have hbase : (n : ℕ∞) ≤ (P.under R).primeHeight := by
      have hp : (⟨P.under R, inferInstance⟩ : PrimeSpectrum R) = p :=
        PrimeSpectrum.ext (P.over_def p.asIdeal).symm
      change (n : ℕ∞) ≤ Order.height (⟨P.under R, inferInstance⟩ : PrimeSpectrum R)
      rw [hp]
      exact hnp
    have hlower : (n : ℕ∞) ≤ P.primeHeight := ih P hbase
    calc
      ((n + 1 : ℕ) : ℕ∞) = (n : ℕ∞) + 1 := by simp
      _ ≤ P.primeHeight + 1 := add_le_add_right hlower 1
      _ ≤ Q.primeHeight := Ideal.primeHeight_add_one_le_of_lt hPQ

end GoingDownHeight

variable (k A : Type*) [Field k] [IsAlgClosed k] [CommRing A] [IsDomain A]
variable [Algebra k A] [Algebra.FiniteType k A]

include k

/-- Every maximal ideal of an actual finite-type domain over an
algebraically closed field has the full Krull dimension of the ring. -/
theorem maximal_height_eq_ringKrullDim (M : Ideal A) [M.IsMaximal] :
    (M.height : WithBot ℕ∞) = ringKrullDim A := by
  obtain ⟨n, f, hinj, hint⟩ := exists_integral_inj_algHom_of_fg k A
  let B := MvPolynomial (Fin n) k
  letI : Algebra B A := f.toRingHom.toAlgebra
  letI : FaithfulSMul B A :=
    (faithfulSMul_iff_algebraMap_injective B A).mpr hinj
  letI : Algebra.IsIntegral B A := ⟨hint⟩
  letI : Algebra.HasGoingDown B A := normal_hasGoingDown
  let m : Ideal B := M.under B
  have hm : m.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M
  have hmheight : (n : ℕ∞) ≤ m.height := polynomial_maximal_height_ge k n m hm
  have hMheight : (n : ℕ∞) ≤ M.primeHeight :=
    nat_le_primeHeight_of_hasGoingDown B A n M
      (by simpa only [Ideal.height_eq_primeHeight] using hmheight)
  have hdim : ringKrullDim A ≤ (n : WithBot ℕ∞) :=
    (ringKrullDim_le_of_integral f.toRingHom hint).trans
      (polynomial_ringKrullDim k n).le
  apply le_antisymm (Ideal.height_le_ringKrullDim_of_ne_top ‹M.IsMaximal›.ne_top)
  exact hdim.trans (WithBot.coe_le_coe.mpr (by
    simpa only [Ideal.height_eq_primeHeight] using hMheight))

/-- The actual localization at each maximal ideal has the same Krull
dimension as the finite-type domain. -/
theorem maximal_localization_dimension (M : Ideal A) [M.IsMaximal] :
    ringKrullDim (Localization.AtPrime M) = ringKrullDim A := by
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height M]
  exact maximal_height_eq_ringKrullDim k A M

end KltDP.Compatibility
