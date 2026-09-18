import KltDP.Geometry.PointBlowupTotalBoundaryStalkIdeal
import KltDP.Geometry.PointBlowupSNCOriginalBaseIdeal
import KltDP.Geometry.PointBlowupCanonicalDivisor
import KltDP.Geometry.FiniteTypeNoetherian

/-!
# SNC of the actual reduced total ideal over the original centre

The original SNC divisor supplies its actual affine ideal and native
local generator. The proved original Rees chart construction and the
actual exceptional/pullback ideal comparisons give an SNC generator
in the original whole-blowup stalk. No local ideal equality is supplied
as a hypothesis.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.PointBlowupSNCBoundary

open AffineBlowup PointBlowupGluing PointBlowupChartStalk
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

/-- The actual radical of the actual total-boundary ideal has an SNC
generator in every original chart stalk above the original centre. -/
theorem reduced_total_ideal_snc_at_center_chart (D : CartierDivisor X.toScheme)
    (hD : IsStrictNormalCrossingsCartier X.toScheme D)
    (a : q.asIdeal) (P : PrimeSpectrum (chartRing q.asIdeal a))
    (hPq : P.asIdeal.comap (chartBaseMap q.asIdeal a) = q.asIdeal) :
    ∃ t : (PointBlowupGluing.scheme j q hclosed).presheaf.stalk
        ((chartInclusion j q hclosed a).base P),
      Ideal.map ((PointBlowupGluing.scheme j q hclosed).presheaf.germ
        (wholeChartAffineOpen j q hclosed a).1 ((chartInclusion j q hclosed a).base P)
        (mem_chart_image_top (chartInclusion j q hclosed a) P)).hom
        ((regularTotalBoundaryIdeal j q hclosed D hD.1).radical.ideal
          (wholeChartAffineOpen j q hclosed a)) = Ideal.span {t} ∧
      IsStrictNormalCrossingsEquation _ t := by
  obtain ⟨c, hc, hsnc⟩ := strictNormalCrossingsCartier_affine_ideal X.toScheme D hD j q
  let J := sourceChartBoundaryIdeal j D hD.1
  have hJ : Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal)) J = Ideal.span {c} := hc
  obtain ⟨t, ht, htnc⟩ := X.pointBlowup_snc_original_base_ideal j q hclosed
    J c hJ hsnc a P.asIdeal hPq
  let ε := openImmersionStalkLocalizationEquiv (chartInclusion j q hclosed a) P
  refine ⟨ε.symm t, ?_, htnc.map_equiv ε.symm⟩
  have hnative := globalReducedTotalBoundary_native_stalk j q hclosed D hD.1 a P
  have heq := hnative.trans ht
  have hback := congrArg (Ideal.map ε.symm.toRingHom) heq
  rw [Ideal.map_map ε.toRingHom ε.symm.toRingHom,
    RingEquiv.symm_toRingHom_comp_toRingHom, Ideal.map_id] at hback
  simpa only [Ideal.map_span, Set.image_singleton] using hback

end KltDP.Geometry.PointBlowupSNCBoundary
