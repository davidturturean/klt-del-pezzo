import KltDP.Geometry.PointBlowupTotalBoundaryStalkIdeal
import KltDP.Geometry.PointBlowupCanonicalDivisor
import KltDP.Geometry.DominantCartierRegularPullback
import KltDP.Geometry.ReducedSupportCartier
import KltDP.Geometry.RegularStalkUFD
import KltDP.Geometry.SectionEffectiveWeil

/-!
# The original reduced Cartier boundary on a point blowup

The existing signed pullback plus the original exceptional Cartier divisor
is effective when the original boundary has regular equations. Its actual
reduced-support Cartier ideal is the radical of the regular total ideal
used in the original chart and stalk computations.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.PointBlowupSNCBoundary

open PointBlowupGluing PointBlowupChartStalk PointBlowupExceptionalCartier
open PointBlowupExceptionalPrimeStalk (sourceSurface)

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k R : Type u} [Field k] [IsAlgClosed k] [CommRing R]
variable (X : NormalProjectiveSurface k) [IsSmooth X.structureMorphism]
variable (j : Spec (CommRingCat.of R) ⟶ X.toScheme) [IsOpenImmersion j]
variable (q : PrimeSpectrum R) [q.asIdeal.IsMaximal]
variable (hclosed : IsClosed ({j.base q} : Set X.toScheme))

/-- Regularity is that of the already constructed original blowup scheme. -/
theorem sourceSurface_regular :
    ∀ y : (sourceSurface X j q hclosed).toScheme,
      RegularPoint (sourceSurface X j q hclosed).toScheme y := by
  let c : PointBlowupChart X.toScheme (j.base q) :=
    { R := R, j := j, q := q, isClosed := hclosed, base_eq := rfl }
  exact (SchemePointBlowup.isAt_projection c).source_regular X

local instance : IsIntegral (PointBlowupGluing.scheme j q hclosed) :=
  (sourceSurface X j q hclosed).integral
local instance : GenericPointPreserving (projection j q hclosed) :=
  ⟨(PointBlowupCanonicalCartier.isBirational_projection X j q hclosed).map_genericPoint⟩
local instance : ∀ y : (sourceSurface X j q hclosed).toScheme,
    UniqueFactorizationMonoid ((sourceSurface X j q hclosed).stalk y) :=
  (sourceSurface X j q hclosed).stalks_uniqueFactorizationMonoid_of_regular
    (sourceSurface_regular X j q hclosed)

private theorem regularIdeal_eq_of_eq (Y : Scheme.{u}) [IsIntegral Y]
    {D E : CartierDivisor Y} (h : D = E)
    (hD : HasRegularCartierEquations Y D) (hE : HasRegularCartierEquations Y E) :
    effectiveCartierIdealDataOfRegularEquations Y D hD =
      effectiveCartierIdealDataOfRegularEquations Y E hE := by
  cases h
  rfl

/-- Regular equations belong to the literal signed pullback plus the
original exceptional Cartier divisor. -/
theorem totalBoundary_hasRegularEquations (D : CartierDivisor X.toScheme)
    (hD : HasRegularCartierEquations X.toScheme D) :
    HasRegularCartierEquations (sourceSurface X j q hclosed).toScheme
      (PointBlowupCanonicalCartier.divisor X j q hclosed D) :=
  CartierDivisorPullbackAdd.hasRegularCartierEquations_add _ _
    (DominantCartierPullback.pullbackHom_hasRegularEquations (projection j q hclosed) D hD)
    (exceptionalCartierDivisor_hasRegularEquations j q hclosed)

/-- The signed total divisor has exactly the regular total ideal already
computed on the original blowup charts. -/
theorem totalBoundary_idealData (D : CartierDivisor X.toScheme)
    (hD : HasRegularCartierEquations X.toScheme D)
    (hB : HasRegularCartierEquations (sourceSurface X j q hclosed).toScheme
      (PointBlowupCanonicalCartier.divisor X j q hclosed D)) :
    effectiveCartierIdealDataOfRegularEquations (sourceSurface X j q hclosed).toScheme
      (PointBlowupCanonicalCartier.divisor X j q hclosed D) hB =
        regularTotalBoundaryIdeal j q hclosed D hD := by
  apply regularIdeal_eq_of_eq (scheme j q hclosed)
  change DominantCartierPullback.pullbackHom (projection j q hclosed) D +
    exceptionalCartierDivisor j q hclosed = _
  rw [DominantCartierPullback.pullbackHom_eq_pullbackDivisor (projection j q hclosed) D hD]

/-- The original reduced-support Cartier construction gives the literal
radical of the same actual total-boundary ideal. -/
theorem reduced_totalBoundary_idealData (D : CartierDivisor X.toScheme)
    (hD : HasRegularCartierEquations X.toScheme D) :
    effectiveCartierIdealDataOfRegularEquations (sourceSurface X j q hclosed).toScheme
      ((sourceSurface X j q hclosed).reducedSupportCartier
        (PointBlowupCanonicalCartier.divisor X j q hclosed D))
      ((sourceSurface X j q hclosed).hasRegularCartierEquations_of_effective_weil _
        ((sourceSurface X j q hclosed).reducedSupportCartier_effective _)) =
      (regularTotalBoundaryIdeal j q hclosed D hD).radical := by
  have heff := (sourceSurface X j q hclosed).effective_cartierToWeilHom_of_regularEquations
    _ (totalBoundary_hasRegularEquations X j q hclosed D hD)
  exact ((sourceSurface X j q hclosed).reducedSupportCartier_idealData _ heff).trans
    (congrArg Scheme.IdealSheafData.radical (totalBoundary_idealData X j q hclosed D hD _))

end KltDP.Geometry.PointBlowupSNCBoundary
