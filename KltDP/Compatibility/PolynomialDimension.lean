import KltDP.Compatibility.NoetherNormalizationDrop
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

/-!
# Polynomial-ring dimension over a field at the existing Mathlib pin

The pinned Noether-normalization construction supplies an actual integral
map from a polynomial ring in one fewer variable into the quotient
whenever the quotient ideal is nonzero. Integral incomparability bounds
the quotient's dimension. Induction using prime coheights then bounds the
dimension of the polynomial ring. Mathlib's existing chain construction
gives the opposite inequality.

This proof uses the existing Lean 4.19.0 / Mathlib
`c44e0c8ee63ca166450922a373c7409c5d26b00b` APIs. The licensed source reuse
for the normalization map is isolated in `NoetherNormalizationDrop`.
No general Krull-height theorem, new literature input, or toolchain upgrade
is required.
-/

noncomputable section

namespace KltDP.Compatibility

/-- Integral extensions do not increase Krull dimension. Actual prime
ideal contraction is strictly monotone by integral incomparability; the
ring map need not be injective. -/
theorem ringKrullDim_le_of_integral {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.IsIntegral) : ringKrullDim S ≤ ringKrullDim R := by
  letI : Algebra R S := f.toAlgebra
  change Order.krullDim (PrimeSpectrum S) ≤ Order.krullDim (PrimeSpectrum R)
  apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap f)
  intro I J hIJ
  letI : I.asIdeal.IsPrime := I.isPrime
  change I.asIdeal.comap f < J.asIdeal.comap f
  obtain ⟨hle, x, hxJ, hxI⟩ := SetLike.lt_iff_le_and_exists.mp
    (show I.asIdeal < J.asIdeal from hIJ)
  exact Ideal.comap_lt_comap_of_integral_mem_sdiff (R := R)
    hle ⟨hxJ, hxI⟩ (hf x)

/-- The dimension of the actual prime quotient is the coheight of that
prime in the actual prime spectrum. -/
theorem ringKrullDim_quotient_eq_coheight {R : Type*} [CommRing R]
    (P : PrimeSpectrum R) :
    ringKrullDim (R ⧸ P.asIdeal) = (Order.coheight P : WithBot ℕ∞) := by
  rw [ringKrullDim_quotient]
  change Order.krullDim (Set.Ici P) = _
  exact (Order.coheight_eq_krullDim_Ici P).symm

/-- For a domain, bounding the dimensions of all nonzero prime quotients
by `d` bounds the ring's dimension by `d + 1`. -/
theorem domain_ringKrullDim_le_succ {R : Type*} [CommRing R] [IsDomain R]
    (d : ℕ)
    (hquot : ∀ P : PrimeSpectrum R, P ≠ ⊥ →
      ringKrullDim (R ⧸ P.asIdeal) ≤ (d : WithBot ℕ∞)) :
    ringKrullDim R ≤ ((d + 1 : ℕ) : WithBot ℕ∞) := by
  have hcoheight : Order.coheight (⊥ : PrimeSpectrum R) ≤ ((d + 1 : ℕ) : ℕ∞) := by
    rw [Order.coheight_le_coe_iff]
    intro P hP
    have hPdim : (Order.coheight P : WithBot ℕ∞) ≤ (d : WithBot ℕ∞) := by
      rw [← ringKrullDim_quotient_eq_coheight]
      exact hquot P hP.ne'
    have hPcoheight : Order.coheight P ≤ (d : ℕ∞) :=
      WithBot.coe_le_coe.mp hPdim
    exact hPcoheight.trans_lt (ENat.coe_lt_coe.mpr (Nat.lt_succ_self d))
  calc
    ringKrullDim R = (Order.coheight (⊥ : PrimeSpectrum R) : WithBot ℕ∞) :=
      (Order.coheight_bot_eq_krullDim (α := PrimeSpectrum R)).symm
    _ ≤ ((d + 1 : ℕ) : WithBot ℕ∞) := WithBot.coe_le_coe.mpr hcoheight

/-- A polynomial ring in `n` variables over a field has Krull dimension
at most `n`. The induction drops one variable in each nonzero prime
quotient using an actual integral algebra map. -/
theorem polynomial_ringKrullDim_le (k : Type*) [Field k] (n : ℕ) :
    ringKrullDim (MvPolynomial (Fin n) k) ≤ (n : WithBot ℕ∞) := by
  induction n with
  | zero =>
      exact
        ((ringKrullDim_mvPolynomial_of_isEmpty (R := k) (Fin 0)).trans
          (ringKrullDim_eq_zero_of_field k)).le
  | succ n ih =>
      apply domain_ringKrullDim_le_succ n
      intro P hP
      have hI : P.asIdeal ≠ ⊥ := by
        intro hI
        apply hP
        exact PrimeSpectrum.ext hI
      obtain ⟨f, hf⟩ := exists_integral_drop_variables k n P.asIdeal hI
      exact (ringKrullDim_le_of_integral f.toRingHom hf).trans ih

/-- A polynomial ring in `n` variables over a field has actual Krull
dimension `n`. The lower bound is the pinned Mathlib prime-chain theorem. -/
theorem polynomial_ringKrullDim (k : Type*) [Field k] (n : ℕ) :
    ringKrullDim (MvPolynomial (Fin n) k) = (n : WithBot ℕ∞) := by
  apply le_antisymm (polynomial_ringKrullDim_le k n)
  simpa only [ringKrullDim_eq_zero_of_field, Nat.card_eq_fintype_card,
    Fintype.card_fin, zero_add] using
    (ringKrullDim_add_natCard_le_ringKrullDim_mvPolynomial (R := k) (Fin n))

end KltDP.Compatibility
