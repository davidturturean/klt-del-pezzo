import KltDP.Geometry.PointBlowupSNCCartierCoefficient
import KltDP.Geometry.QCartierPullbackSupportBound
import KltDP.Geometry.DiscrepancyWeightedMultiplicity

/-!
# The actual weighted boundary contributes more than minus two

A larger original reduced SNC Cartier divisor controls the total actual
prime multiplicity at the exceptional prime. The original rational boundary
may have any weights greater than minus one and may omit components.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped BigOperators

universe u

namespace KltDP.Geometry.PointBlowupExceptionalPrimeStalk

open PointBlowupGluing QCartierPullback

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
/-- The original point blowup's actual rational boundary coefficient is
strictly greater than minus two. All chart, nonnegative multiplicity and
total-multiplicity facts are derived from the original geometry. -/
theorem pullback_coefficient_gt_neg_two_of_snc_containing
    (B : X.RationalWeilDivisor) (D : CartierDivisor X.toScheme)
    (hD : IsStrictNormalCrossingsCartier X.toScheme D)
    (hcoeff : ∀ F, X.cartierToWeilHom D F = 0 ∨ X.cartierToWeilHom D F = 1)
    (hBD : B.support ⊆ (X.cartierToWeilHom D).support)
    (hweights : ∀ F ∈ B.support, (-1 : ℚ) < B F) :
    let π : (sourceSurface X j q hclosed).toScheme ⟶ X.toScheme := projection j q hclosed
    letI : GenericPointPreserving π := projection_genericPointPreserving X j q hclosed
    (-2 : ℚ) < QCartierPullback.pullback π B
      (X.qCartier_of_regular X.regularPoints_of_isSmooth B) C := by
  classical
  let π : (sourceSurface X j q hclosed).toScheme ⟶ X.toScheme := projection j q hclosed
  letI : GenericPointPreserving π := projection_genericPointPreserving X j q hclosed
  have hDupper : (sourceSurface X j q hclosed).cartierToWeilHom
      (DominantCartierPullback.pullbackHom π D) C ≤ 2 := by
    have hcases :
        (sourceSurface X j q hclosed).cartierToWeilHom
          (DominantCartierPullback.pullbackHom π D) C = 0 ∨
        (sourceSurface X j q hclosed).cartierToWeilHom
          (DominantCartierPullback.pullbackHom π D) C = 1 ∨
        (sourceSurface X j q hclosed).cartierToWeilHom
          (DominantCartierPullback.pullbackHom π D) C = 2 :=
      cartier_pullback_coefficient_zero_one_two_of_snc X j q hclosed C hcenter D hD
    rcases hcases with hzero | hone | htwo
    · rw [hzero]
      norm_num
    · rw [hone]
      norm_num
    · exact le_of_eq htwo
  have htotalInt : (∑ F ∈ B.support, primeMultiplicity π C F) ≤ 2 :=
    (sum_primeMultiplicity_le_pullback_coefficient π C B.support D hcoeff hBD).trans hDupper
  have htotal : (∑ F ∈ B.support, (primeMultiplicity π C F : ℚ)) ≤ 2 := by
    exact_mod_cast htotalInt
  have hnonneg : ∀ F ∈ B.support, (0 : ℚ) ≤ (primeMultiplicity π C F : ℚ) := by
    intro F _
    exact_mod_cast primeMultiplicity_nonneg π C F
  change (-2 : ℚ) < QCartierPullback.pullback π B
    (X.qCartier_of_regular X.regularPoints_of_isSmooth B) C
  rw [pullback_apply_eq_sum]
  exact DiscrepancyWeightedMultiplicity.neg_two_lt_weighted_sum
    B.support B (fun F => (primeMultiplicity π C F : ℚ)) hweights hnonneg htotal

end KltDP.Geometry.PointBlowupExceptionalPrimeStalk
