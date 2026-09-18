import KltDP.Geometry.PointBlowupSNCCenterCover
import KltDP.Geometry.PointBlowupSNCOffCenterIdeal
import KltDP.Geometry.PointBlowupSNCBoundaryCartier
import KltDP.Geometry.StrictNormalCrossingsCartierIdealData

/-!
# SNC preservation for the original smooth surface point blowup

The target is the existing reduced Cartier support of the original signed
pullback plus the original exceptional divisor. Every center stalk uses
the actual regular-parameter Rees charts. Every other stalk uses the
original projection's puncture isomorphism. The actual Cartier ideal
comparison and Cartier locality finish the global statement.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.PointBlowupSNCBoundary

open PointBlowupGluing PointBlowupChartStalk
open PointBlowupExceptionalPrimeStalk (sourceSurface)

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k R : Type u} [Field k] [IsAlgClosed k] [CommRing R]
variable (X : NormalProjectiveSurface k) [IsSmooth X.structureMorphism]
variable (j : Spec (CommRingCat.of R) ⟶ X.toScheme) [IsOpenImmersion j]
variable (q : PrimeSpectrum R) [q.asIdeal.IsMaximal]
variable (hclosed : IsClosed ({j.base q} : Set X.toScheme))

local instance : IsLocallyNoetherian X.toScheme := X.isLocallyNoetherian
local instance : IsIntegral (PointBlowupGluing.scheme j q hclosed) :=
  (sourceSurface X j q hclosed).integral
local instance : IsLocallyNoetherian (sourceSurface X j q hclosed).toScheme :=
  (sourceSurface X j q hclosed).isLocallyNoetherian
local instance : GenericPointPreserving (projection j q hclosed) :=
  ⟨(PointBlowupCanonicalCartier.isBirational_projection X j q hclosed).map_genericPoint⟩
local instance : ∀ y : (sourceSurface X j q hclosed).toScheme,
    UniqueFactorizationMonoid ((sourceSurface X j q hclosed).stalk y) :=
  (sourceSurface X j q hclosed).stalks_uniqueFactorizationMonoid_of_regular
    (sourceSurface_regular X j q hclosed)

/-- Blowing up the original smooth surface at its original closed point
preserves strict normal crossings of the reduced total boundary. -/
theorem reduced_totalBoundary_isStrictNormalCrossings (D : CartierDivisor X.toScheme)
    (hD : IsStrictNormalCrossingsCartier X.toScheme D) :
    IsStrictNormalCrossingsCartier (sourceSurface X j q hclosed).toScheme
      ((sourceSurface X j q hclosed).reducedSupportCartier
        (PointBlowupCanonicalCartier.divisor X j q hclosed D)) := by
  apply isStrictNormalCrossingsCartier_of_idealData_generators
    (sourceSurface X j q hclosed).toScheme _ _
    ((regularTotalBoundaryIdeal j q hclosed D hD.1).radical)
    (reduced_totalBoundary_idealData X j q hclosed D hD.1)
  intro y
  by_cases hy : (projection j q hclosed).base y = j.base q
  · exact reduced_total_ideal_snc_at_center X j q hclosed D hD y hy
  · exact reduced_total_ideal_snc_off_center X j q hclosed D hD y hy

end KltDP.Geometry.PointBlowupSNCBoundary

#check @KltDP.Geometry.PointBlowupSNCBoundary.reduced_totalBoundary_isStrictNormalCrossings
#print axioms KltDP.Geometry.PointBlowupSNCBoundary.reduced_totalBoundary_isStrictNormalCrossings
