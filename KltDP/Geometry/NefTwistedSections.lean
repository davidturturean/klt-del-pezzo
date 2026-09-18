import KltDP.Geometry.NefPositiveSquareKodaira
import KltDP.Geometry.RiemannRochEventualGrowthBound

/-!
# Eventual original sections after an arbitrary fixed Cartier twist

On the original regular projective surface, a nef Cartier divisor A of
positive square makes the actual H0 of nA + T positive for every n beyond
one positive threshold. The twist T is arbitrary. The same threshold
forces the original complementary sections to vanish by nef intersection.

This consumer remains in the existing private, unaccepted surface
Riemann--Roch dependency branch. It adds no axiom or admission claim and
does not change `Positivity.IsBig` or assert the full Keel bridge.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.NormalProjectiveSurface
open KltDP.Geometry.ModuleCohomology KltDP.Geometry.SurfaceRiemannRochSource

universe u

namespace KltDP.Geometry.NefTwistedSections

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

/-- For every sufficiently large exponent, the original H0 of nA + T
has positive dimension. All vanishing and RR inequalities are derived. -/
theorem eventually_hDimension_pos (K : X.WeilDivisor)
    (hK : IsCanonical X hregular K) (A T : CartierDivisor X.toScheme)
    (hA : Positivity.IsNef X.structureMorphism
      (cartierDivisorInvertibleSheaf X.toScheme A))
    (hpositive : 0 < intersectionPairing X hregular A A) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      0 < hDimension X hregular (X.cartierToWeilHom (n • A + T)) 0 := by
  let H : CartierDivisor X.toScheme := -T
  let Kc := (X.regularCartierWeilEquiv hregular).symm K
  let a : ℤ := intersectionPairing X hregular A A
  let b : ℤ := 2 * intersectionPairing X hregular A H +
    intersectionPairing X hregular A Kc
  let c : ℤ := intersectionPairing X hregular A H +
    intersectionPairing X hregular A Kc
  let bound : ℤ := max b c
  let z : ℚ :=
    ((intersectionPairing X hregular H H : ℚ) +
      (intersectionPairing X hregular H Kc : ℚ)) / 2 +
      (eulerCharacteristic X.structureMorphism
        (_root_.SheafOfModules.unit X.toScheme.ringCatSheaf) : ℚ)
  have ha : (1 : ℚ) ≤ (a : ℚ) := by
    have h : (1 : ℤ) ≤ a := by omega
    exact_mod_cast h
  obtain ⟨N, hN, hthreshold⟩ :=
    RiemannRochGrowthBound.exists_eventual_quadratic_bound
      (a : ℚ) (bound : ℚ) z ha
  refine ⟨N, hN, ?_⟩
  intro n hn
  obtain ⟨hbound, hgrowth⟩ := hthreshold n hn
  have hboundZ : bound < (n : ℤ) * a := by exact_mod_cast hbound
  have hc : c < (n : ℤ) * a := (le_max_right b c).trans_lt hboundZ
  have hdegree : intersectionPairing X hregular Kc A <
      intersectionPairing X hregular
        ((X.regularCartierWeilEquiv hregular).symm
          (X.cartierToWeilHom (n • A - H))) A := by
    rw [RiemannRochEffectiveMultiple.inverse_toWeil,
      sub_eq_add_neg (n • A), X.intersectionPairing_add_left,
      X.intersectionPairing_neg_left,
      RiemannRochEffectiveMultiple.intersection_nsmul_left,
      X.intersectionPairing_symm hregular Kc A,
      X.intersectionPairing_symm hregular H A]
    change intersectionPairing X hregular A H +
      intersectionPairing X hregular A Kc <
        (n : ℤ) * intersectionPairing X hregular A A at hc
    omega
  have hrrBound : (1 / 4 : ℚ) * (n : ℚ) ^ 2 ≤
      rrNumber X hregular (X.cartierToWeilHom (n • A - H)) K := by
    rw [NefPositiveSquareKodaira.rrNumber_nsmul_sub]
    change (1 / 4 : ℚ) * (n : ℚ) ^ 2 ≤
      ((a : ℚ) * (n : ℚ) ^ 2 - (b : ℚ) * (n : ℚ)) / 2 + z
    have hb : (b : ℚ) ≤ (bound : ℚ) := by
      exact_mod_cast (le_max_left b c)
    have hlinear := mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg n : (0 : ℚ) ≤ n)
    linarith
  have hnQ : (0 : ℚ) < n := Nat.cast_pos.mpr (hN.trans_le hn)
  have hrrPositive :
      0 < rrNumber X hregular (X.cartierToWeilHom (n • A - H)) K :=
    (mul_pos (by norm_num : (0 : ℚ) < 1 / 4) (sq_pos_of_pos hnQ)).trans_le hrrBound
  have hnegative := SurfaceRiemannRochNef.complementary_intersection_neg X hregular
    (X.cartierToWeilHom (n • A - H)) K A hdegree
  have hvanish := NefIntersectionSectionVanishing.sections_subsingleton X hregular
    (K - X.cartierToWeilHom (n • A - H)) A hA hnegative
  have hrr := AmpleBignessFromRiemannRoch.rrNumber_le_hDimension X hregular
    (X.cartierToWeilHom (n • A - H)) K hK hvanish
  have hdimension :
      0 < hDimension X hregular (X.cartierToWeilHom (n • A - H)) 0 := by
    exact_mod_cast (hrrPositive.trans_le hrr)
  simpa only [H, sub_neg_eq_add] using hdimension

end KltDP.Geometry.NefTwistedSections
