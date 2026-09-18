import KltDP.Geometry.NumericalIsotropicNonnegative
import KltDP.Geometry.CanonicalPicardCharacteristic
import KltDP.Geometry.NefNullCurveNegativeSquare

/-! Original Cartier divisors orthogonal to F with nonnegative square are
integral numerical multiples of F when F²=0 and K.F=-2. Hodge gives the
rational multiple; the original Cartier Riemann--Roch parity makes it integral. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.SmoothCanonicalExteriorComparison
universe u
namespace KltDP.Geometry.NormalProjectiveSurface
open NefNullCurveNegativeSquare

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k)
  (hX : ∀ x : X.Point, RegularPoint X.toScheme x)
  (K : CartierDivisor X.toScheme)
  (eK : cartierDivisorModule X.toScheme K ≅
    relativeDifferentialExterior X.structureMorphism 2)

local instance orthogonalIntegralSourceIntegral : IsIntegral X.toScheme := X.integral

include eK in
/-- The actual canonical pairing and RR parity rule out fractional
multiples, without a supplied lattice or primitivity conclusion. -/
theorem squareZero_orthogonal_integral_multiple (F M : CartierDivisor X.toScheme)
    (hFF : X.intersectionPairing hX F F = 0)
    (hKF : X.intersectionPairing hX K F = -2)
    (hMM : 0 ≤ X.intersectionPairing hX M M)
    (hFM : X.intersectionPairing hX F M = 0) :
    ∃ n : ℤ, cartierClass X M = (n : ℚ) • cartierClass X F ∧
      X.intersectionPairing hX M M = 0 := by
  let B := X.numericalIntersectionBilinForm hX
  have hf : cartierClass X F ≠ 0 := by
    intro hz
    have hp := cartierClass_pairing X hX K F
    rw [hz, map_zero, hKF] at hp
    norm_num at hp
  have hff : B (cartierClass X F) (cartierClass X F) = 0 := by
    rw [cartierClass_pairing, hFF, Int.cast_zero]
  have hmm : 0 ≤ B (cartierClass X M) (cartierClass X M) := by
    rw [cartierClass_pairing]
    exact_mod_cast hMM
  have hfm : B (cartierClass X F) (cartierClass X M) = 0 := by
    rw [cartierClass_pairing, hFM, Int.cast_zero]
  obtain ⟨a, ha⟩ := NumericalIsotropicHodge.exists_smul_eq_of_nonneg X hX
    (cartierClass X F) (cartierClass X M) hf hff hmm hfm
  have hsq : B (cartierClass X M) (cartierClass X M) = 0 := by
    rw [ha]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hff, mul_zero]
  have hMMzero : X.intersectionPairing hX M M = 0 := by
    rw [cartierClass_pairing] at hsq
    exact_mod_cast hsq
  have hKM : (X.intersectionPairing hX K M : ℚ) = a * (-2) := by
    calc
      _ = B (cartierClass X K) (cartierClass X M) := (cartierClass_pairing X hX K M).symm
      _ = a * B (cartierClass X K) (cartierClass X F) := by
        rw [ha, map_smul, smul_eq_mul]
      _ = a * (-2) := by rw [cartierClass_pairing, hKF]; norm_num
  obtain ⟨n, hn⟩ := X.cartier_square_sub_canonical_even hX K eK M
  rw [hMMzero, zero_sub] at hn
  have hnq : -(X.intersectionPairing hX K M : ℚ) = (n : ℚ) + (n : ℚ) := by
    exact_mod_cast hn
  have han : a = (n : ℚ) := by linarith
  exact ⟨n, by rw [← han]; exact ha, hMMzero⟩

end KltDP.Geometry.NormalProjectiveSurface

#check @KltDP.Geometry.NormalProjectiveSurface.squareZero_orthogonal_integral_multiple
#print axioms KltDP.Geometry.NormalProjectiveSurface.squareZero_orthogonal_integral_multiple
