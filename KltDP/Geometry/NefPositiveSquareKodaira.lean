import KltDP.Geometry.NefSelfIntersectionNonnegative

/-!
# An effective representative of nD-H for a nef divisor of positive square

The original Riemann–Roch expression for nD-H has a positive quadratic
coefficient. The same bound that makes it positive makes its intersection
with nef D greater than K.D, so the complementary section space vanishes.
Full surface RR then produces an actual effective Weil divisor equivalent
to nD-H. The coefficient of the arbitrary ample Cartier divisor H is one.

The smooth consumer constructs the canonical divisor and requires no
effective representative, section, vanishing, or RR-value hypothesis.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.NormalProjectiveSurface
open KltDP.Geometry.ModuleCohomology KltDP.Geometry.SurfaceRiemannRochSource
open KltDP.Geometry.SmoothCanonicalCartierRepresentative

universe u

namespace KltDP.Geometry.NefPositiveSquareKodaira

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

private theorem intersection_nsmul_right (n : ℕ) (D H : CartierDivisor X.toScheme) :
    intersectionPairing X hregular D (n • H) =
      (n : ℤ) * intersectionPairing X hregular D H := by
  rw [X.intersectionPairing_symm hregular D (n • H),
    RiemannRochEffectiveMultiple.intersection_nsmul_left,
    X.intersectionPairing_symm hregular H D]

/-- The original RR polynomial after subtracting exactly one copy of H. -/
theorem rrNumber_nsmul_sub (D H : CartierDivisor X.toScheme)
    (K : X.WeilDivisor) (n : ℕ) :
    rrNumber X hregular (X.cartierToWeilHom (n • D - H)) K =
      ((intersectionPairing X hregular D D : ℚ) * (n : ℚ) ^ 2 -
        ((2 * intersectionPairing X hregular D H +
          intersectionPairing X hregular D
            ((X.regularCartierWeilEquiv hregular).symm K) : ℤ) : ℚ) * (n : ℚ)) / 2 +
        (((intersectionPairing X hregular H H : ℚ) +
          (intersectionPairing X hregular H
            ((X.regularCartierWeilEquiv hregular).symm K) : ℚ)) / 2 +
          (eulerCharacteristic X.structureMorphism
            (_root_.SheafOfModules.unit X.toScheme.ringCatSheaf) : ℚ)) := by
  unfold rrNumber arithmeticGenus
  simp only [map_sub, RiemannRochEffectiveMultiple.inverse_toWeil]
  simp only [sub_eq_add_neg, X.intersectionPairing_add_left,
    X.intersectionPairing_add_right, X.intersectionPairing_neg_left,
    X.intersectionPairing_neg_right,
    RiemannRochEffectiveMultiple.intersection_nsmul_left, intersection_nsmul_right]
  rw [X.intersectionPairing_symm hregular H D]
  push_cast
  ring

/-- Full RR and actual nefness produce the effective representative of
nD-H; the canonical divisor is the only auxiliary geometric input. -/
theorem exists_effective_sub_ample_of_isCanonical (K : X.WeilDivisor)
    (hK : IsCanonical X hregular K) (D H : CartierDivisor X.toScheme)
    (hD : Positivity.IsNef X.structureMorphism
      (cartierDivisorInvertibleSheaf X.toScheme D))
    (hDD : 0 < intersectionPairing X hregular D D)
    (hH : AmpleSerre.IsAmple (cartierDivisorInvertibleSheaf X.toScheme H)) :
    ∃ n : ℕ, 0 < n ∧ ∃ E : X.WeilDivisor,
      EffectiveDivisor E ∧
        X.LinearlyEquivalent E (X.cartierToWeilHom (n • D - H)) := by
  let Kc := (X.regularCartierWeilEquiv hregular).symm K
  let a : ℤ := intersectionPairing X hregular D D
  let b : ℤ := 2 * intersectionPairing X hregular D H +
    intersectionPairing X hregular D Kc
  let z : ℚ :=
    ((intersectionPairing X hregular H H : ℚ) +
      (intersectionPairing X hregular H Kc : ℚ)) / 2 +
      (eulerCharacteristic X.structureMorphism
        (_root_.SheafOfModules.unit X.toScheme.ringCatSheaf) : ℚ)
  have ha : (1 : ℚ) ≤ (a : ℚ) := by
    have h : (1 : ℤ) ≤ a := by omega
    exact_mod_cast h
  have hDH : 0 ≤ intersectionPairing X hregular D H := by
    rw [X.intersectionPairing_symm hregular D H]
    exact NefSelfIntersectionNonnegative.intersection_nonneg_of_isAmple_isNef
      X hregular H D hH hD
  obtain ⟨n, hn, hbound, hgrowth⟩ :=
    RiemannRochGrowthBound.exists_large_with_quadratic_bound (a : ℚ) (b : ℚ) z ha 1
  have hnPos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hboundZ : b < (n : ℤ) * a := by exact_mod_cast hbound
  have hdegree : intersectionPairing X hregular Kc D <
      intersectionPairing X hregular
        ((X.regularCartierWeilEquiv hregular).symm
          (X.cartierToWeilHom (n • D - H))) D := by
    rw [RiemannRochEffectiveMultiple.inverse_toWeil,
      sub_eq_add_neg (n • D), X.intersectionPairing_add_left,
      X.intersectionPairing_neg_left,
      RiemannRochEffectiveMultiple.intersection_nsmul_left,
      X.intersectionPairing_symm hregular Kc D,
      X.intersectionPairing_symm hregular H D]
    change 2 * intersectionPairing X hregular D H +
      intersectionPairing X hregular D Kc <
        (n : ℤ) * intersectionPairing X hregular D D at hboundZ
    omega
  have hrr : 0 < rrNumber X hregular (X.cartierToWeilHom (n • D - H)) K := by
    rw [rrNumber_nsmul_sub]
    have hnQ : (0 : ℚ) < n := Nat.cast_pos.mpr hnPos
    exact (mul_pos (by norm_num : (0 : ℚ) < 1 / 4) (sq_pos_of_pos hnQ)).trans_le hgrowth
  obtain ⟨E, hE, hED⟩ := SurfaceRiemannRochNef.exists_effectiveWeil X hregular
    (X.cartierToWeilHom (n • D - H)) K D hK hD hdegree hrr
  exact ⟨n, hnPos, E, hE, hED⟩

section Smooth

variable [IsSmoothOfRelativeDimension 2 X.structureMorphism]

local instance source_isSmooth : IsSmooth X.structureMorphism :=
  IsSmoothOfRelativeDimension.isSmooth 2 X.structureMorphism

/-- For an actual nef Cartier divisor D of positive square and any ample
Cartier divisor H on the original smooth projective surface, some nD-H
has an actual effective representative, with n positive. -/
theorem exists_effective_sub_ample (D H : CartierDivisor X.toScheme)
    (hD : Positivity.IsNef X.structureMorphism
      (cartierDivisorInvertibleSheaf X.toScheme D))
    (hDD : 0 < intersectionPairing X X.regularPoints_of_isSmooth D D)
    (hH : AmpleSerre.IsAmple (cartierDivisorInvertibleSheaf X.toScheme H)) :
    ∃ n : ℕ, 0 < n ∧ ∃ E : X.WeilDivisor,
      EffectiveDivisor E ∧
        X.LinearlyEquivalent E (X.cartierToWeilHom (n • D - H)) :=
  exists_effective_sub_ample_of_isCanonical X X.regularPoints_of_isSmooth
    (weilRepresentative X) (SurfaceRiemannRochSource.constructedCanonical_isCanonical X)
    D H hD hDD hH

end Smooth

end KltDP.Geometry.NefPositiveSquareKodaira
