import KltDP.Geometry.PointBlowupExceptionalPrimeStalk
import KltDP.Geometry.PointBlowupExceptionalCartier
import KltDP.Geometry.BirationalCartierPullbackAddPushforward

/-!
# The literal pullback plus exceptional divisor on the original point blowup

The source surface is the existing original glued scheme with its proved
surface properties. The exceptional Cartier divisor is constructed from
the original centre-fibre kernel. Its exact Weil pushforward is derived
from that kernel's actual contraction, with no coefficient or pushforward
premise and no assumption that the base Cartier divisor is canonical.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.PointBlowupCanonicalCartier

open PointBlowupGluing PointBlowupExceptionalCartier
open PointBlowupExceptionalPrimeStalk (sourceSurface)

/-- Birationality concerns the original projection from the already proved
source surface, without an additional birationality input. -/
theorem isBirational_projection
    {k R : Type u} [Field k] [IsAlgClosed k] [CommRing R]
    (X : NormalProjectiveSurface k) [IsSmooth X.structureMorphism]
    (j : Spec (CommRingCat.of R) ⟶ X.toScheme) [IsOpenImmersion j]
    (q : PrimeSpectrum R) [q.asIdeal.IsMaximal]
    (hclosed : IsClosed ({j.base q} : Set X.toScheme)) :
    IsBirationalScheme (show (sourceSurface X j q hclosed).toScheme ⟶ X.toScheme from
      projection j q hclosed) :=
  projection_isBirationalScheme j q hclosed
    (X.affine_closed_point_ideal_ne_bot j q hclosed)

/-- The original centre-fibre inclusion contracts to the original closed point. -/
theorem centerFiber_maps_to_center
    {R : Type u} [CommRing R] {X : Scheme.{u}}
    (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
    (q : PrimeSpectrum R) [q.asIdeal.IsMaximal]
    (hclosed : IsClosed ({j.base q} : Set X))
    (z : globalCenterFiber j q hclosed) :
    (projection j q hclosed).base ((globalCenterFiberι j q hclosed).base z) = j.base q := by
  have hz : (globalCenterFiberι j q hclosed).base z ∈
      Set.range (globalCenterFiberι j q hclosed).base := ⟨z, rfl⟩
  rw [range_globalCenterFiberι] at hz
  exact hz

/-- The signed original Cartier pullback plus the actual exceptional Cartier divisor. -/
def divisor
    {k R : Type u} [Field k] [IsAlgClosed k] [CommRing R]
    (X : NormalProjectiveSurface k) [IsSmooth X.structureMorphism]
    (j : Spec (CommRingCat.of R) ⟶ X.toScheme) [IsOpenImmersion j]
    (q : PrimeSpectrum R) [q.asIdeal.IsMaximal]
    (hclosed : IsClosed ({j.base q} : Set X.toScheme))
    (K : CartierDivisor X.toScheme) : CartierDivisor (sourceSurface X j q hclosed).toScheme := by
  letI : IsIntegral (scheme j q hclosed) := (sourceSurface X j q hclosed).integral
  letI : GenericPointPreserving (projection j q hclosed) :=
    ⟨(isBirational_projection X j q hclosed).map_genericPoint⟩
  exact DominantCartierPullback.pullbackHom (projection j q hclosed) K +
    exceptionalCartierDivisor j q hclosed

/-- The actual divisor has exactly the original base divisor's Weil pushforward.
The original exceptional contribution is proved to vanish. -/
theorem divisor_pushforward
    {k R : Type u} [Field k] [IsAlgClosed k] [CommRing R]
    (X : NormalProjectiveSurface k) [IsSmooth X.structureMorphism]
    (j : Spec (CommRingCat.of R) ⟶ X.toScheme) [IsOpenImmersion j]
    (q : PrimeSpectrum R) [q.asIdeal.IsMaximal]
    (hclosed : IsClosed ({j.base q} : Set X.toScheme))
    (K : CartierDivisor X.toScheme) :
    letI : IsProper (projection j q hclosed) :=
      projection_isProper_of_fg j q hclosed (X.affine_point_ideal_fg j q)
    BirationalWeilPushforward.pushforward
      (S := sourceSurface X j q hclosed) (X := X)
      (projection j q hclosed) (isBirational_projection X j q hclosed)
      ((sourceSurface X j q hclosed).cartierToWeilHom (divisor X j q hclosed K)) =
        X.cartierToWeilHom K := by
  letI : IsIntegral (scheme j q hclosed) := (sourceSurface X j q hclosed).integral
  letI : IsProper (projection j q hclosed) :=
    projection_isProper_of_fg j q hclosed (X.affine_point_ideal_fg j q)
  exact BirationalWeilPushforward.pushforward_cartier_pullback_add_of_kernel_maps_to_closed_point
    (S := sourceSurface X j q hclosed) (X := X)
    (projection j q hclosed) (isBirational_projection X j q hclosed) K
    (exceptionalCartierDivisor j q hclosed)
    (exceptionalCartierDivisor_hasRegularEquations j q hclosed)
    (globalCenterFiberι j q hclosed) (exceptionalCartierDivisor_idealData j q hclosed)
    (j.base q) hclosed (centerFiber_maps_to_center j q hclosed)

end KltDP.Geometry.PointBlowupCanonicalCartier

#check @KltDP.Geometry.PointBlowupCanonicalCartier.divisor
#check @KltDP.Geometry.PointBlowupCanonicalCartier.divisor_pushforward
#print axioms KltDP.Geometry.PointBlowupCanonicalCartier.divisor_pushforward
