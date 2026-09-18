import KltDP.Geometry.PointBlowupPullbackStalkIdeal
import KltDP.Geometry.PointBlowupExceptionalCartier
import KltDP.Geometry.EffectiveCartierIdealAddition
import KltDP.Geometry.OpenChartRadicalStalkIdeal

/-!
# The actual total-boundary ideal on the original blowup chart

The accepted regular pullback presentation and the original exceptional
Cartier divisor give the actual total ideal. Its stalk is the product
of the two actual ideals. Reduction is then literal radical of that
product, with both original chart ideals retained.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.PointBlowupChartStalk

open AffineBlowup PointBlowupGluing PointBlowupExceptionalCartier

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {R : Type u} [CommRing R] {X : Scheme.{u}} [IsIntegral X]
variable (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
variable (q : PrimeSpectrum R) [q.asIdeal.IsMaximal]
variable (hclosed : IsClosed ({j.base q} : Set X))
variable [IsIntegral (PointBlowupGluing.scheme j q hclosed)]
variable [GenericPointPreserving (projection j q hclosed)]

/-- The literal source boundary ideal in the original affine chart ring. -/
abbrev sourceChartBoundaryIdeal (D : CartierDivisor X) (hD : HasRegularCartierEquations X D) :
    Ideal R :=
  Ideal.map (KltDP.Geometry.chartSectionsEquiv j).toRingHom
    ((effectiveCartierIdealDataOfRegularEquations X D hD).ideal
      ⟨j ''ᵁ ⊤, chart_image_top_isAffineOpen j⟩)

/-- The actual regular-equation ideal of the pullback plus original exceptional divisor. -/
abbrev regularTotalBoundaryIdeal (D : CartierDivisor X) (hD : HasRegularCartierEquations X D) :
    (PointBlowupGluing.scheme j q hclosed).IdealSheafData :=
  effectiveCartierIdealDataOfRegularEquations _
    (pullbackDivisor (projection j q hclosed) D hD + exceptionalCartierDivisor j q hclosed)
    (CartierDivisorPullbackAdd.hasRegularCartierEquations_add _ _
      (pullbackDivisor_hasRegularEquations (projection j q hclosed) D hD)
      (exceptionalCartierDivisor_hasRegularEquations j q hclosed))

/-- The actual total ideal is the product on every original affine open. -/
theorem regularTotalBoundaryIdeal_ideal (D : CartierDivisor X)
    (hD : HasRegularCartierEquations X D)
    (U : (PointBlowupGluing.scheme j q hclosed).affineOpens) :
    (regularTotalBoundaryIdeal j q hclosed D hD).ideal U =
      (pullbackIdealData (projection j q hclosed) D hD).ideal U *
        (globalCenterFiberι j q hclosed).ker.ideal U := by
  rw [regularTotalBoundaryIdeal, effectiveCartierIdealDataOfRegularEquations_add_ideal,
    exceptionalCartierDivisor_idealData]
  rfl

/-- The actual total boundary in native coordinates retains the exact
exceptional and pulled original boundary ideals. -/
theorem globalTotalBoundary_native_stalk (D : CartierDivisor X)
    (hD : HasRegularCartierEquations X D)
    (a : q.asIdeal) (P : PrimeSpectrum (chartRing q.asIdeal a)) :
    Ideal.map (openImmersionStalkLocalizationEquiv (chartInclusion j q hclosed a) P).toRingHom
      (Ideal.map ((PointBlowupGluing.scheme j q hclosed).presheaf.germ
        (wholeChartAffineOpen j q hclosed a).1 ((chartInclusion j q hclosed a).base P)
        (mem_chart_image_top (chartInclusion j q hclosed a) P)).hom
        ((regularTotalBoundaryIdeal j q hclosed D hD).ideal (wholeChartAffineOpen j q hclosed a))) =
      Ideal.map (algebraMap (chartRing q.asIdeal a) (Localization.AtPrime P.asIdeal))
        (chartCenterIdeal q.asIdeal a *
          Ideal.map (chartBaseMap q.asIdeal a) (sourceChartBoundaryIdeal j D hD)) := by
  rw [regularTotalBoundaryIdeal_ideal, Ideal.map_mul, Ideal.map_mul,
    globalPullback_native_stalk, globalCenterFiber_native_stalk, ← Ideal.map_mul]
  exact congrArg (Ideal.map (algebraMap (chartRing q.asIdeal a) (Localization.AtPrime P.asIdeal)))
    (mul_comm _ _)

/-- The literal radical of the total ideal has the original reduced
exceptional-plus-pulled ideal in the actual chart local ring. -/
theorem globalReducedTotalBoundary_native_stalk (D : CartierDivisor X)
    (hD : HasRegularCartierEquations X D)
    (a : q.asIdeal) (P : PrimeSpectrum (chartRing q.asIdeal a)) :
    Ideal.map (openImmersionStalkLocalizationEquiv (chartInclusion j q hclosed a) P).toRingHom
      (Ideal.map ((PointBlowupGluing.scheme j q hclosed).presheaf.germ
        (wholeChartAffineOpen j q hclosed a).1 ((chartInclusion j q hclosed a).base P)
        (mem_chart_image_top (chartInclusion j q hclosed a) P)).hom
        ((regularTotalBoundaryIdeal j q hclosed D hD).radical.ideal
          (wholeChartAffineOpen j q hclosed a))) =
      Ideal.map (algebraMap (chartRing q.asIdeal a) (Localization.AtPrime P.asIdeal))
        (chartCenterIdeal q.asIdeal a *
          Ideal.map (chartBaseMap q.asIdeal a) (sourceChartBoundaryIdeal j D hD)).radical := by
  rw [Scheme.IdealSheafData.radical_ideal,
    openImmersionStalkLocalizationEquiv_germIdeal_radical,
    globalTotalBoundary_native_stalk,
    ← IsLocalization.map_radical P.asIdeal.primeCompl (Localization.AtPrime P.asIdeal)]

end KltDP.Geometry.PointBlowupChartStalk
