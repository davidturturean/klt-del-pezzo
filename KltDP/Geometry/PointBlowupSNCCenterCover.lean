import KltDP.Geometry.PointBlowupSNCCenterIdeal
import KltDP.Geometry.PointBlowupCenterChartCover

/-!
# SNC generators of the actual reduced total ideal above the centre

The original point cover removes the chart-witness input from the
proved center-chart theorem. The conclusion is the original affine
ideal/germ interface consumed by Cartier SNC locality.
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
local instance : GenericPointPreserving (projection j q hclosed) :=
  ⟨(PointBlowupCanonicalCartier.isBirational_projection X j q hclosed).map_genericPoint⟩

/-- Every actual point over the original centre has an SNC generator of
the actual reduced total ideal on an original affine neighborhood. -/
theorem reduced_total_ideal_snc_at_center (D : CartierDivisor X.toScheme)
    (hD : IsStrictNormalCrossingsCartier X.toScheme D)
    (y : PointBlowupGluing.scheme j q hclosed)
    (hy : (projection j q hclosed).base y = j.base q) :
    ∃ (U : (PointBlowupGluing.scheme j q hclosed).affineOpens) (hyU : y ∈ U.1)
      (t : (PointBlowupGluing.scheme j q hclosed).presheaf.stalk y),
      Ideal.map ((PointBlowupGluing.scheme j q hclosed).presheaf.germ U.1 y hyU).hom
        ((regularTotalBoundaryIdeal j q hclosed D hD.1).radical.ideal U) = Ideal.span {t} ∧
      IsStrictNormalCrossingsEquation _ t := by
  obtain ⟨a, P, hP, hPq⟩ := exists_original_chart_over_center j q hclosed y hy
  subst y
  obtain ⟨t, ht, hsnc⟩ := reduced_total_ideal_snc_at_center_chart X j q hclosed D hD a P hPq
  exact ⟨wholeChartAffineOpen j q hclosed a,
    mem_chart_image_top (chartInclusion j q hclosed a) P, t, ht, hsnc⟩

end KltDP.Geometry.PointBlowupSNCBoundary
