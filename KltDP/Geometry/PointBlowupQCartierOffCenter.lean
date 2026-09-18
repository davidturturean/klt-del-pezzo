import KltDP.Geometry.QCartierBirationalStalkCoefficient
import KltDP.Geometry.PointBlowupCanonicalDivisor
import KltDP.Geometry.BirationalAdapters

/-!
# Every off-centre prime retains the original rational coefficients

The established puncture correspondence constructs the original target
prime. The proper birational coefficient theorem then applies to every
original rational Cartier divisor, without a supplied prime witness.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
namespace KltDP.Geometry.PointBlowupGluing

open PointBlowupExceptionalPrimeStalk (sourceSurface)

theorem exists_prime_preserving_qCartier_coefficients_off_center
    {k R : Type u} [Field k] [IsAlgClosed k] [CommRing R]
    (X : NormalProjectiveSurface k) [IsSmooth X.structureMorphism]
    (j : Spec (CommRingCat.of R) ⟶ X.toScheme) [IsOpenImmersion j]
    (q : PrimeSpectrum R) [q.asIdeal.IsMaximal]
    (hclosed : IsClosed ({j.base q} : Set X.toScheme))
    (C : (sourceSurface X j q hclosed).PrimeCurve)
    (hcenter : (projection j q hclosed).base C.genericPoint ≠ j.base q) :
    letI : IsIntegral (scheme j q hclosed) := (sourceSurface X j q hclosed).integral
    letI : GenericPointPreserving (projection j q hclosed) :=
      ⟨(PointBlowupCanonicalCartier.isBirational_projection X j q hclosed).map_genericPoint⟩
    ∃ D : X.PrimeCurve,
      (projection j q hclosed).base C.genericPoint = D.genericPoint ∧
      ∀ (B : X.RationalWeilDivisor) (hB : X.QCartier B),
        QCartierPullback.pullback (X := sourceSurface X j q hclosed)
          (projection j q hclosed) B hB C = B D := by
  letI : IsIntegral (scheme j q hclosed) := (sourceSurface X j q hclosed).integral
  let hbir := PointBlowupCanonicalCartier.isBirational_projection X j q hclosed
  letI : GenericPointPreserving (projection j q hclosed) := ⟨hbir.map_genericPoint⟩
  letI : IsProper (projection j q hclosed) :=
    projection_isProper_of_fg j q hclosed (X.affine_point_ideal_fg j q)
  letI : IsIso (projection j q hclosed ∣_ puncture j q hclosed) :=
    projection_restrict_puncture_isIso j q hclosed
  letI : IsIso ((projection j q hclosed).stalkMap C.genericPoint) :=
    isIso_stalkMap_of_isIso_restrict (projection j q hclosed)
      (puncture j q hclosed) C.genericPoint hcenter
  exact QCartierPullback.exists_prime_preserving_coefficients_of_stalkMap_isIso
    (projection j q hclosed) hbir C

end KltDP.Geometry.PointBlowupGluing

#check @KltDP.Geometry.PointBlowupGluing.exists_prime_preserving_qCartier_coefficients_off_center
#print axioms KltDP.Geometry.PointBlowupGluing.exists_prime_preserving_qCartier_coefficients_off_center
