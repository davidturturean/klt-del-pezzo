import KltDP.Geometry.PointBlowupSNCCartierCoefficient
import KltDP.Geometry.ReducedSupportCartier

/-!
# The original reduced Cartier support has exceptional coefficient at most two

This specializes the actual SNC coefficient calculation to the original
reducedSupportCartier construction. Its local factoriality is derived from
actual smoothness. Rational boundary weights remain separate from this
reduced-support calculation; no discrepancy or klt theorem is asserted.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.PointBlowupExceptionalPrimeStalk

open PointBlowupGluing

variable {k R : Type u} [Field k] [IsAlgClosed k] [CommRing R]
    (X : NormalProjectiveSurface k) [IsSmooth X.structureMorphism]
    (j : Spec (CommRingCat.of R) ⟶ X.toScheme) [IsOpenImmersion j]
    (q : PrimeSpectrum R) [q.asIdeal.IsMaximal]
    (hclosed : IsClosed ({j.base q} : Set X.toScheme))
    (C : (sourceSurface X j q hclosed).PrimeCurve)
    (hcenter : (projection j q hclosed).base C.genericPoint = j.base q)

local instance : IsLocallyNoetherian X.toScheme := X.isLocallyNoetherian

local instance : ∀ x : X.toScheme, UniqueFactorizationMonoid (X.stalk x) := fun x =>
  (regularLocal_isDomain_and_uniqueFactorizationMonoid (X.stalk x)
    (X.regularPoints_of_isSmooth x)).2

include hcenter in
/-- The literal original reduced Cartier support has actual coefficient
zero, one or two on the original exceptional prime of the point blowup. -/
theorem reducedSupport_pullback_coefficient_zero_one_two
    (D : CartierDivisor X.toScheme)
    (hD : IsStrictNormalCrossingsCartier X.toScheme (X.reducedSupportCartier D)) :
    let π : (sourceSurface X j q hclosed).toScheme ⟶ X.toScheme := projection j q hclosed
    letI : GenericPointPreserving π := projection_genericPointPreserving X j q hclosed
    (sourceSurface X j q hclosed).cartierToWeilHom
        (DominantCartierPullback.pullbackHom π (X.reducedSupportCartier D)) C = 0 ∨
      (sourceSurface X j q hclosed).cartierToWeilHom
        (DominantCartierPullback.pullbackHom π (X.reducedSupportCartier D)) C = 1 ∨
      (sourceSurface X j q hclosed).cartierToWeilHom
        (DominantCartierPullback.pullbackHom π (X.reducedSupportCartier D)) C = 2 :=
  cartier_pullback_coefficient_zero_one_two_of_snc X j q hclosed C hcenter
    (X.reducedSupportCartier D) hD

include hcenter in
/-- The exact original reduced-support coefficient lies between zero
and two; this is independent of arbitrary rational boundary weights. -/
theorem reducedSupport_pullback_coefficient_bounds
    (D : CartierDivisor X.toScheme)
    (hD : IsStrictNormalCrossingsCartier X.toScheme (X.reducedSupportCartier D)) :
    let π : (sourceSurface X j q hclosed).toScheme ⟶ X.toScheme := projection j q hclosed
    letI : GenericPointPreserving π := projection_genericPointPreserving X j q hclosed
    let n := (sourceSurface X j q hclosed).cartierToWeilHom
      (DominantCartierPullback.pullbackHom π (X.reducedSupportCartier D)) C
    0 ≤ n ∧ n ≤ 2 := by
  let π : (sourceSurface X j q hclosed).toScheme ⟶ X.toScheme := projection j q hclosed
  letI : GenericPointPreserving π := projection_genericPointPreserving X j q hclosed
  let n := (sourceSurface X j q hclosed).cartierToWeilHom
    (DominantCartierPullback.pullbackHom π (X.reducedSupportCartier D)) C
  have h : n = 0 ∨ n = 1 ∨ n = 2 :=
    reducedSupport_pullback_coefficient_zero_one_two X j q hclosed C hcenter D hD
  change 0 ≤ n ∧ n ≤ 2
  omega

end KltDP.Geometry.PointBlowupExceptionalPrimeStalk
