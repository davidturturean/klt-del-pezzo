import KltDP.Geometry.PointBlowupDiscrepancyBounds
import KltDP.Geometry.CartierDiscrepancySupport
import KltDP.Geometry.PointBlowupStrictNormalCrossings

/-!
# The constructed boundary for the next discrepancy step

The new boundary is the actual reduced support of the original pulled
boundary plus the exceptional divisor. It remains SNC, has coefficients
zero or one, and contains the new discrepancy even if coefficients cancel.
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
local instance : IsLocallyNoetherian (sourceSurface X j q hclosed).toScheme :=
  (sourceSurface X j q hclosed).isLocallyNoetherian
local instance : GenericPointPreserving (projection j q hclosed) :=
  projection_genericPointPreserving X j q hclosed
local instance : ∀ x : X.toScheme, UniqueFactorizationMonoid (X.stalk x) := fun x =>
  (regularLocal_isDomain_and_uniqueFactorizationMonoid (X.stalk x)
    (X.regularPoints_of_isSmooth x)).2
local instance : ∀ y : (sourceSurface X j q hclosed).toScheme,
    UniqueFactorizationMonoid ((sourceSurface X j q hclosed).stalk y) :=
  (sourceSurface X j q hclosed).stalks_uniqueFactorizationMonoid_of_regular
    (PointBlowupSNCBoundary.sourceSurface_regular X j q hclosed)

theorem exists_reduced_boundary_with_discrepancy_bounds
    (f : X.toScheme ⟶ Y.toScheme) [GenericPointPreserving f]
    (K : CartierDivisor X.toScheme) (B : Y.RationalWeilDivisor) (hB : Y.QCartier B)
    (A : CartierDivisor X.toScheme) (hA : IsStrictNormalCrossingsCartier X.toScheme A)
    (hcoeff : ∀ D, X.cartierToWeilHom A D = 0 ∨ X.cartierToWeilHom A D = 1)
    (hcontains : (X.rationalCartierToWeilHom K - pullback f B hB).support ⊆
      (X.cartierToWeilHom A).support)
    (hbound : ∀ D : X.PrimeCurve,
      (-1 : ℚ) < (X.rationalCartierToWeilHom K - pullback f B hB) D) :
    let S := sourceSurface X j q hclosed
    let Δ := S.rationalCartierToWeilHom (PointBlowupCanonicalCartier.divisor X j q hclosed K) -
      pullback (X := S) (Y := Y) (projection j q hclosed ≫ f) B hB
    ∃ A' : CartierDivisor S.toScheme,
      IsStrictNormalCrossingsCartier S.toScheme A' ∧
      (∀ C, S.cartierToWeilHom A' C = 0 ∨ S.cartierToWeilHom A' C = 1) ∧
      Δ.support ⊆ (S.cartierToWeilHom A').support ∧
      ∀ C : S.PrimeCurve, (-1 : ℚ) < Δ C := by
  let S := sourceSurface X j q hclosed
  let A' := S.reducedSupportCartier (PointBlowupCanonicalCartier.divisor X j q hclosed A)
  refine ⟨A', PointBlowupSNCBoundary.reduced_totalBoundary_isStrictNormalCrossings
    X j q hclosed A hA, ?_, ?_, ?_⟩
  · exact S.reducedSupportCartier_coefficient_zero_or_one _
  · exact CartierDiscrepancyPullback.support_subset_reduced_total
      (S := S) (Y := X) (X := Y) (projection j q hclosed) f K
      (exceptionalCartierDivisor j q hclosed) B hB A hA.1
      (exceptionalCartierDivisor_hasRegularEquations j q hclosed) hcoeff hcontains
  · exact coefficients_gt_neg_one X Y j q hclosed f K B hB A hA hcoeff hcontains hbound

end KltDP.Geometry.PointBlowupDiscrepancy

#check @KltDP.Geometry.PointBlowupDiscrepancy.exists_reduced_boundary_with_discrepancy_bounds
#print axioms KltDP.Geometry.PointBlowupDiscrepancy.exists_reduced_boundary_with_discrepancy_bounds
