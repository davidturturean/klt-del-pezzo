import KltDP.Geometry.PointBlowupDiscrepancyOffCenter
import KltDP.Geometry.PointBlowupExceptionalCoefficient
import KltDP.Geometry.PointBlowupSNCWeightedBoundary

/-!
# Strict discrepancy bounds after the original point blowup

The literal pullback-plus-exceptional Cartier divisor is used throughout.
At the centre, its correction coefficient is one and its weighted pullback
coefficient is greater than minus two. Away from the centre, the original
prime correspondence preserves the original discrepancy coefficient.
The canonical-module interpretation is a separate theorem.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
namespace KltDP.Geometry.PointBlowupDiscrepancy

open PointBlowupGluing PointBlowupExceptionalPrimeStalk
open PointBlowupExceptionalCartier QCartierPullback

variable {k R : Type u} [Field k] [IsAlgClosed k] [CommRing R]
  (X Y : NormalProjectiveSurface k) [IsSmooth X.structureMorphism]
  (j : Spec (CommRingCat.of R) ⟶ X.toScheme) [IsOpenImmersion j]
  (q : PrimeSpectrum R) [q.asIdeal.IsMaximal]
  (hclosed : IsClosed ({j.base q} : Set X.toScheme))

local instance : IsLocallyNoetherian X.toScheme := X.isLocallyNoetherian
local instance : IsIntegral (scheme j q hclosed) := (sourceSurface X j q hclosed).integral
local instance : GenericPointPreserving (projection j q hclosed) :=
  projection_genericPointPreserving X j q hclosed

theorem coefficients_gt_neg_one
    (f : X.toScheme ⟶ Y.toScheme) [GenericPointPreserving f]
    (K : CartierDivisor X.toScheme) (B : Y.RationalWeilDivisor) (hB : Y.QCartier B)
    (A : CartierDivisor X.toScheme) (hA : IsStrictNormalCrossingsCartier X.toScheme A)
    (hcoeff : ∀ D, X.cartierToWeilHom A D = 0 ∨ X.cartierToWeilHom A D = 1)
    (hcontains : (X.rationalCartierToWeilHom K - pullback f B hB).support ⊆
      (X.cartierToWeilHom A).support)
    (hbound : ∀ D : X.PrimeCurve,
      (-1 : ℚ) < (X.rationalCartierToWeilHom K - pullback f B hB) D)
    (C : (sourceSurface X j q hclosed).PrimeCurve) :
    (-1 : ℚ) <
      ((sourceSurface X j q hclosed).rationalCartierToWeilHom
          (PointBlowupCanonicalCartier.divisor X j q hclosed K) -
        pullback (X := sourceSurface X j q hclosed) (Y := Y)
          (projection j q hclosed ≫ f) B hB) C := by
  let S := sourceSurface X j q hclosed
  let π : S.toScheme ⟶ X.toScheme := projection j q hclosed
  by_cases hcenter : π.base C.genericPoint = j.base q
  · let Δ : X.rationalCartierSubmodule :=
      X.rationalCartierMap K - pullbackLinearMap f ⟨B, hB⟩
    have hw := pullback_coefficient_gt_neg_two_of_snc_containing
      X j q hclosed C hcenter (Δ : X.RationalWeilDivisor) A hA hcoeff hcontains
        (fun D _ => hbound D)
    change (-2 : ℚ) < pullbackToWeil π Δ C at hw
    have hE : S.rationalCartierToWeilHom (exceptionalCartierDivisor j q hclosed) C = 1 := by
      change (S.cartierToWeilHom (exceptionalCartierDivisor j q hclosed) C : ℚ) = 1
      rw [exceptionalCartierDivisor_coefficient_eq_one X j q hclosed C hcenter]
      rfl
    have hformula := congrArg (fun D : S.RationalWeilDivisor => D C)
      (CartierDiscrepancyPullback.pullback_add_formula π f K
        (exceptionalCartierDivisor j q hclosed) B hB)
    change (S.rationalCartierToWeilHom
          (PointBlowupCanonicalCartier.divisor X j q hclosed K) -
        pullback (π ≫ f) B hB) C =
      S.rationalCartierToWeilHom (exceptionalCartierDivisor j q hclosed) C +
        pullbackToWeil π Δ C at hformula
    rw [hformula, hE]
    linarith
  · obtain ⟨D, _, hD⟩ := exists_prime_preserving_discrepancy_off_center
      X Y j q hclosed f K B hB C hcenter
    rw [hD]
    exact hbound D

end KltDP.Geometry.PointBlowupDiscrepancy

#check @KltDP.Geometry.PointBlowupDiscrepancy.coefficients_gt_neg_one
#print axioms KltDP.Geometry.PointBlowupDiscrepancy.coefficients_gt_neg_one
