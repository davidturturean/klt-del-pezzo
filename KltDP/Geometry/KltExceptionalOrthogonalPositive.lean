import KltDP.Geometry.KltExceptionalOrthogonalRank
import KltDP.Geometry.BirationalAmplePullbackPositiveSquare
import KltDP.Geometry.DelPezzoType
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Positive square in the original rank-one exceptional complement

The actual ample anticanonical numerator supplies a signed Cartier pullback
with positive square and zero degree on every original exceptional prime.
The proved target-rank formula makes the literal exceptional orthogonal
space one-dimensional. Every nonzero class in it is therefore a nonzero
rational multiple of that actual positive class. No signature, positive
class, pullback spanning, or numerical descent is an input.
-/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.IsMinimalResolution

open NormalProjectiveSurface ActualExceptionalNumerical
open NefNullCurveNegativeSquare

variable {k : Type u} [Field k] [IsAlgClosed k]
  {S X : NormalProjectiveSurface k} {π : S.toScheme ⟶ X.toScheme}

local instance exceptionalPositiveIntegral (T : NormalProjectiveSurface k) :
    IsIntegral T.toScheme := T.integral

/-- Every nonzero original numerical class orthogonal to the original
exceptional primes has positive square on a rank-one klt del Pezzo minimal
resolution. The characteristic input is exactly that of the compiled
original Picard-rank equality. -/
theorem exceptionalOrthogonal_square_pos_of_kltDelPezzo
    (hmin : IsMinimalResolution S X π) (hDP : IsKltDelPezzo X)
    (p : ℕ) [CharP k p] (hp : 0 < p) (hrank : X.picardRank = 1)
    (v : S.NumericalClassGroup) (hv : v ∈ exceptionalOrthogonal π) (hne : v ≠ 0) :
    0 < S.numericalIntersectionBilinForm hmin.regular v v := by
  letI : IsProper π := hmin.toIsResolution.isProper
  let hbir : IsBirationalScheme π :=
    (isBirational_iff_isBirationalScheme π).mp hmin.birational
  letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
  obtain ⟨KX, hKX, _, _, A, _, hample⟩ := (isLogDelPezzoPair_zero_iff X).mp hDP
  let H : CartierDivisor S.toScheme := DominantCartierPullback.pullbackHom π A
  let c : S.NumericalClassGroup := cartierClass S H
  have hcpos : 0 < S.numericalIntersectionBilinForm hmin.regular c c := by
    change 0 < S.numericalIntersectionBilinForm hmin.regular
      (cartierClass S H) (cartierClass S H)
    rw [cartierClass_pairing]
    exact_mod_cast BirationalAmplePullbackPositiveSquare.intersectionPairing_signedPullback_pos
      π hbir hmin.regular A hample
  have hcorth : c ∈ exceptionalOrthogonal π := by
    apply (mem_exceptionalOrthogonal_iff π c).mpr
    intro E
    rw [← DisjointNegativeCurvesRank.pairing_curveClass S hmin.regular c E.val]
    change S.numericalIntersectionBilinForm hmin.regular
      (cartierClass S H) (DisjointNegativeCurvesRank.curveClass S hmin.regular E.val) = 0
    rw [NullCurveNumericalSpan.cartierClass_curveClass]
    exact_mod_cast E.property.intersectionNumber_pullback_eq_zero
      π hmin.over_base E.val A
  have hcne : c ≠ 0 := by
    intro hzero
    rw [hzero, map_zero] at hcpos
    exact (lt_irrefl 0) hcpos
  let cO : exceptionalOrthogonal π := ⟨c, hcorth⟩
  have hcOne : cO ≠ 0 := by
    intro hzero
    exact hcne (congrArg Subtype.val hzero)
  have hdim := hmin.finrank_exceptionalOrthogonal_eq_one_of_klt ⟨KX, hKX⟩ p hp hrank
  obtain ⟨a, ha⟩ := (_root_.finrank_eq_one_iff_of_nonzero' cO hcOne).mp hdim ⟨v, hv⟩
  have hav : a • c = v := congrArg Subtype.val ha
  have hane : a ≠ 0 := by
    intro hzero
    rw [hzero, zero_smul] at hav
    exact hne hav.symm
  rw [← hav, LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right]
  simpa only [mul_assoc] using mul_pos (mul_self_pos.mpr hane) hcpos

/-- The only square-zero original numerical class in the actual exceptional
orthogonal space is zero. -/
theorem exceptionalOrthogonal_square_eq_zero_iff_of_kltDelPezzo
    (hmin : IsMinimalResolution S X π) (hDP : IsKltDelPezzo X)
    (p : ℕ) [CharP k p] (hp : 0 < p) (hrank : X.picardRank = 1)
    (v : S.NumericalClassGroup) (hv : v ∈ exceptionalOrthogonal π) :
    S.numericalIntersectionBilinForm hmin.regular v v = 0 ↔ v = 0 := by
  constructor
  · intro hzero
    by_contra hne
    have hpositive := hmin.exceptionalOrthogonal_square_pos_of_kltDelPezzo
      hDP p hp hrank v hv hne
    exact (ne_of_gt hpositive) hzero
  · rintro rfl
    exact map_zero (S.numericalIntersectionBilinForm hmin.regular 0)

end KltDP.Geometry.IsMinimalResolution

#check @KltDP.Geometry.IsMinimalResolution.exceptionalOrthogonal_square_pos_of_kltDelPezzo
#check @KltDP.Geometry.IsMinimalResolution.exceptionalOrthogonal_square_eq_zero_iff_of_kltDelPezzo
#print axioms KltDP.Geometry.IsMinimalResolution.exceptionalOrthogonal_square_pos_of_kltDelPezzo
#print axioms KltDP.Geometry.IsMinimalResolution.exceptionalOrthogonal_square_eq_zero_iff_of_kltDelPezzo
