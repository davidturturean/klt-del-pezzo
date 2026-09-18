import KltDP.Geometry.PointBlowupQCartierOffCenter
import KltDP.Geometry.PointBlowupExceptionalCoefficientOffCenter
import KltDP.Geometry.CartierDiscrepancyPullback

/-!
# The original point-blowup discrepancy away from the centre

The actual puncture correspondence selects the target prime. The original
exceptional divisor has coefficient zero there, and the original rational
pullback preserves the remaining coefficient. No discrepancy equality is
an input to the calculation.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
namespace KltDP.Geometry.PointBlowupGluing

open PointBlowupExceptionalPrimeStalk (sourceSurface)
open PointBlowupExceptionalCartier (exceptionalCartierDivisor)
open QCartierPullback

theorem exists_prime_preserving_discrepancy_off_center
    {k R : Type u} [Field k] [IsAlgClosed k] [CommRing R]
    (X Y : NormalProjectiveSurface k) [IsSmooth X.structureMorphism]
    (j : Spec (CommRingCat.of R) ⟶ X.toScheme) [IsOpenImmersion j]
    (q : PrimeSpectrum R) [q.asIdeal.IsMaximal]
    (hclosed : IsClosed ({j.base q} : Set X.toScheme))
    (f : X.toScheme ⟶ Y.toScheme) [GenericPointPreserving f]
    (K : CartierDivisor X.toScheme) (B : Y.RationalWeilDivisor) (hB : Y.QCartier B)
    (C : (sourceSurface X j q hclosed).PrimeCurve)
    (hcenter : (projection j q hclosed).base C.genericPoint ≠ j.base q) :
    letI : IsIntegral (scheme j q hclosed) := (sourceSurface X j q hclosed).integral
    letI : GenericPointPreserving (projection j q hclosed) :=
      ⟨(PointBlowupCanonicalCartier.isBirational_projection X j q hclosed).map_genericPoint⟩
    ∃ D : X.PrimeCurve,
      (projection j q hclosed).base C.genericPoint = D.genericPoint ∧
      ((sourceSurface X j q hclosed).rationalCartierToWeilHom
          (PointBlowupCanonicalCartier.divisor X j q hclosed K) -
        pullback (X := sourceSurface X j q hclosed) (Y := Y)
          (projection j q hclosed ≫ f) B hB) C =
          (X.rationalCartierToWeilHom K - pullback f B hB) D := by
  let S := sourceSurface X j q hclosed
  let π : S.toScheme ⟶ X.toScheme := projection j q hclosed
  letI : IsIntegral (scheme j q hclosed) := S.integral
  letI : GenericPointPreserving π :=
    ⟨(PointBlowupCanonicalCartier.isBirational_projection X j q hclosed).map_genericPoint⟩
  obtain ⟨D, hD, hcoeff⟩ :=
    exists_prime_preserving_qCartier_coefficients_off_center X j q hclosed C hcenter
  let Δ : X.rationalCartierSubmodule :=
    X.rationalCartierMap K - pullbackLinearMap f ⟨B, hB⟩
  let E := exceptionalCartierDivisor j q hclosed
  have hE : S.rationalCartierToWeilHom E C = 0 := by
    change (S.cartierToWeilHom E C : ℚ) = 0
    rw [PointBlowupExceptionalPrimeStalk.exceptionalCartierDivisor_coefficient_eq_zero
      X j q hclosed C hcenter]
    rfl
  have hpull : pullbackToWeil π Δ C = (Δ : X.RationalWeilDivisor) D :=
    hcoeff (Δ : X.RationalWeilDivisor) Δ.property
  refine ⟨D, hD, ?_⟩
  calc
    _ = S.rationalCartierToWeilHom E C + pullbackToWeil π Δ C :=
      congrArg (fun A : S.RationalWeilDivisor => A C)
        (CartierDiscrepancyPullback.pullback_add_formula π f K E B hB)
    _ = (X.rationalCartierToWeilHom K - pullback f B hB) D := by
      rw [hE, hpull, zero_add]
      rfl

end KltDP.Geometry.PointBlowupGluing

#check @KltDP.Geometry.PointBlowupGluing.exists_prime_preserving_discrepancy_off_center
#print axioms KltDP.Geometry.PointBlowupGluing.exists_prime_preserving_discrepancy_off_center
