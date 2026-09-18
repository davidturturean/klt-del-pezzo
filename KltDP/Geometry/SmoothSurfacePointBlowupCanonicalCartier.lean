import KltDP.Geometry.PointBlowupCanonicalDivisor
import KltDP.Geometry.SmoothSurfacePointBlowupCanonicalFactor
import KltDP.Geometry.BirationalCanonicalRepresentativeFromFactor

/-!
# The actual canonical Cartier representative on a smooth surface point blowup

Only the original base canonical representative and its original exterior
square isomorphism are inputs. The exceptional Cartier divisor, its regular
equations and its original kernel equality are derived. The proved whole
differential factor gives the line isomorphism for the literal pullback plus E.
Its exact pushforward and canonical representative uniqueness are consequences.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.PointBlowupCanonicalCartier

open PointBlowupGluing PointBlowupExceptionalCartier
open PointBlowupExceptionalPrimeStalk (sourceSurface)
open SmoothCanonicalExteriorComparison (relativeDifferentialExterior)

/-- The literal divisor `π*K+E` represents the original exterior square
on the original whole blowup, using its proved differential factor. -/
def canonicalModuleIso
    {k R : Type u} [Field k] [IsAlgClosed k] [CommRing R]
    (X : NormalProjectiveSurface k) [IsSmooth X.structureMorphism]
    (j : Spec (CommRingCat.of R) ⟶ X.toScheme) [IsOpenImmersion j]
    (q : PrimeSpectrum R) [q.asIdeal.IsMaximal]
    (hclosed : IsClosed ({j.base q} : Set X.toScheme))
    (K : CartierDivisor X.toScheme)
    (eK : cartierDivisorModule X.toScheme K ≅
      relativeDifferentialExterior X.structureMorphism 2) :
    cartierDivisorModule (sourceSurface X j q hclosed).toScheme (divisor X j q hclosed K) ≅
      relativeDifferentialExterior (sourceSurface X j q hclosed).structureMorphism 2 := by
  letI : IsIntegral (scheme j q hclosed) := (sourceSurface X j q hclosed).integral
  letI : GenericPointPreserving (projection j q hclosed) :=
    ⟨(isBirational_projection X j q hclosed).map_genericPoint⟩
  exact CartierPullbackExceptionalModule.ofFactorIso (projection j q hclosed) K
    (relativeDifferentialExterior X.structureMorphism 2)
    (relativeDifferentialExterior (sourceSurface X j q hclosed).structureMorphism 2)
    eK (exceptionalCartierDivisor j q hclosed)
    (exceptionalCartierDivisor_hasRegularEquations j q hclosed)
    (globalCenterFiberι j q hclosed) (exceptionalCartierDivisor_idealData j q hclosed)
    (X.pointBlowupCanonicalFactorIso j q hclosed)

/-- The original point blowup has a unique canonical Cartier representative
whose exact Weil pushforward is the chosen original base representative.
No exceptional equation, factorization or pushforward statement is assumed. -/
theorem existsUnique_canonicalRepresentative
    {k R : Type u} [Field k] [IsAlgClosed k] [CommRing R]
    (X : NormalProjectiveSurface k) [IsSmooth X.structureMorphism]
    (j : Spec (CommRingCat.of R) ⟶ X.toScheme) [IsOpenImmersion j]
    (q : PrimeSpectrum R) [q.asIdeal.IsMaximal]
    (hclosed : IsClosed ({j.base q} : Set X.toScheme))
    (K : CartierDivisor X.toScheme)
    (eK : cartierDivisorModule X.toScheme K ≅
      relativeDifferentialExterior X.structureMorphism 2) :
    letI : IsProper (projection j q hclosed) :=
      projection_isProper_of_fg j q hclosed (X.affine_point_ideal_fg j q)
    ∃! D : CartierDivisor (sourceSurface X j q hclosed).toScheme,
      Nonempty (cartierDivisorModule (sourceSurface X j q hclosed).toScheme D ≅
        relativeDifferentialExterior (sourceSurface X j q hclosed).structureMorphism 2) ∧
      BirationalWeilPushforward.pushforward
        (S := sourceSurface X j q hclosed) (X := X)
        (projection j q hclosed) (isBirational_projection X j q hclosed)
        ((sourceSurface X j q hclosed).cartierToWeilHom D) = X.cartierToWeilHom K := by
  letI : IsIntegral (scheme j q hclosed) := (sourceSurface X j q hclosed).integral
  letI : IsProper (projection j q hclosed) :=
    projection_isProper_of_fg j q hclosed (X.affine_point_ideal_fg j q)
  exact BirationalCanonicalRepresentative.existsUnique_of_exceptional_factor
    (S := sourceSurface X j q hclosed) (X := X)
    (projection j q hclosed) (isBirational_projection X j q hclosed) K eK
    (exceptionalCartierDivisor j q hclosed)
    (exceptionalCartierDivisor_hasRegularEquations j q hclosed)
    (globalCenterFiberι j q hclosed) (exceptionalCartierDivisor_idealData j q hclosed)
    (j.base q) hclosed (centerFiber_maps_to_center j q hclosed)
    (X.pointBlowupCanonicalFactorIso j q hclosed)

end KltDP.Geometry.PointBlowupCanonicalCartier

#check @KltDP.Geometry.PointBlowupCanonicalCartier.canonicalModuleIso
#check @KltDP.Geometry.PointBlowupCanonicalCartier.existsUnique_canonicalRepresentative
#print axioms KltDP.Geometry.PointBlowupCanonicalCartier.canonicalModuleIso
#print axioms KltDP.Geometry.PointBlowupCanonicalCartier.existsUnique_canonicalRepresentative
