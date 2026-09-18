import KltDP.Geometry.AmpleBignessFromRiemannRoch

/-!
# Effective multiples from a positive square and a nef test divisor

The original divisor D need not be nef or ample. Its positive square makes
the original RR expression positive in sufficiently large multiples. Its
positive intersection with the actual nef test divisor H forces the
complementary sections to vanish. The compiled RR consumer then produces
an actual effective integral divisor linearly equivalent to a positive
multiple of D.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.NormalProjectiveSurface
open KltDP.Geometry.ModuleCohomology KltDP.Geometry.SurfaceRiemannRochSource

universe u

namespace KltDP.Geometry.RiemannRochEffectiveMultiple

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

theorem inverse_toWeil (D : CartierDivisor X.toScheme) :
    (X.regularCartierWeilEquiv hregular).symm (X.cartierToWeilHom D) = D :=
  (X.regularCartierWeilEquiv hregular).symm_apply_apply D

/-- The original Cartier pairing evaluates positive integral multiples. -/
theorem intersection_nsmul_left (n : ℕ) (D H : CartierDivisor X.toScheme) :
    intersectionPairing X hregular (n • D) H =
      (n : ℤ) * intersectionPairing X hregular D H := by
  let f : CartierDivisor X.toScheme →+ ℤ :=
    AddMonoidHom.mk' (fun E => intersectionPairing X hregular E H)
      (fun E F => X.intersectionPairing_add_left hregular E F H)
  have h := f.map_nsmul D n
  change intersectionPairing X hregular (n • D) H =
    n • intersectionPairing X hregular D H at h
  simpa only [nsmul_eq_mul] using h

/-- Positive square and positive intersection with an actual nef test
divisor give an effective positive multiple of the arbitrary original D. -/
theorem exists_positive_effective_multiple (K : X.WeilDivisor)
    (hK : IsCanonical X hregular K) (D H : CartierDivisor X.toScheme)
    (hH : Positivity.IsNef X.structureMorphism
      (cartierDivisorInvertibleSheaf X.toScheme H))
    (hDD : 0 < intersectionPairing X hregular D D)
    (hDH : 0 < intersectionPairing X hregular D H) :
    ∃ n : ℕ, 0 < n ∧ ∃ Z : X.WeilDivisor,
      EffectiveDivisor Z ∧ X.LinearlyEquivalent Z (X.cartierToWeilHom (n • D)) := by
  let a : ℤ := intersectionPairing X hregular D D
  let b : ℤ := intersectionPairing X hregular D
    ((X.regularCartierWeilEquiv hregular).symm K)
  let z : ℤ := eulerCharacteristic X.structureMorphism
    (_root_.SheafOfModules.unit X.toScheme.ringCatSheaf)
  have ha : (1 : ℚ) ≤ (a : ℚ) := by
    have h : (1 : ℤ) ≤ a := by omega
    exact_mod_cast h
  obtain ⟨M, hM⟩ := exists_nat_gt
    (intersectionPairing X hregular ((X.regularCartierWeilEquiv hregular).symm K) H)
  obtain ⟨n, hn, _, hgrowth⟩ :=
    RiemannRochGrowthBound.exists_large_with_quadratic_bound (a : ℚ) (b : ℚ) (z : ℚ)
      ha (max 1 M)
  have hnOne : 1 ≤ n := (Nat.le_max_left 1 M).trans hn
  have hnPos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hnOne
  have hMle : (M : ℤ) ≤ (n : ℤ) := by
    exact_mod_cast ((Nat.le_max_right 1 M).trans hn)
  have hDHOne : (1 : ℤ) ≤ intersectionPairing X hregular D H := by omega
  have hnDH : (n : ℤ) ≤ (n : ℤ) * intersectionPairing X hregular D H := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hDHOne (Nat.cast_nonneg n : (0 : ℤ) ≤ n)
  have hdegree : intersectionPairing X hregular
      ((X.regularCartierWeilEquiv hregular).symm K) H <
        intersectionPairing X hregular
          ((X.regularCartierWeilEquiv hregular).symm
            (X.cartierToWeilHom (n • D))) H := by
    rw [inverse_toWeil, intersection_nsmul_left]
    exact hM.trans_le (hMle.trans hnDH)
  have hrr : 0 < rrNumber X hregular (X.cartierToWeilHom (n • D)) K := by
    rw [AmpleBignessFromRiemannRoch.rrNumber_nsmul]
    have hnQ : (0 : ℚ) < n := Nat.cast_pos.mpr hnPos
    exact (mul_pos (by norm_num : (0 : ℚ) < 1 / 4) (sq_pos_of_pos hnQ)).trans_le hgrowth
  obtain ⟨Z, hZ, hZD⟩ := SurfaceRiemannRochNef.exists_effectiveWeil X hregular
    (X.cartierToWeilHom (n • D)) K H hK hH hdegree hrr
  exact ⟨n, hnPos, Z, hZ, hZD⟩

end KltDP.Geometry.RiemannRochEffectiveMultiple
