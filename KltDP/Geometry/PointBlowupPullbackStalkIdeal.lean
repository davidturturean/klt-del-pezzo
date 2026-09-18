import KltDP.Geometry.PointBlowupExceptionalStalkIdeal
import KltDP.Geometry.CartierPullbackStalkIdeal
import KltDP.Geometry.OpenChartSquareStalkIdeals

/-!
# The original pulled boundary ideal in an original blowup chart

The original point-blowup chart/projection square transports the actual
source Cartier ideal into the native chart local ring. Principality of
the boundary on the original source affine chart is not assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.PointBlowupChartStalk

open AffineBlowup PointBlowupGluing

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {R : Type u} [CommRing R] {X : Scheme.{u}} [IsIntegral X]
variable (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
variable (q : PrimeSpectrum R) [q.asIdeal.IsMaximal]
variable (hclosed : IsClosed ({j.base q} : Set X))
variable [IsIntegral (PointBlowupGluing.scheme j q hclosed)]
variable [GenericPointPreserving (projection j q hclosed)]

/-- The actual pulled Cartier ideal has its literal native extended
base-ideal description on the original whole-blowup chart stalk. -/
theorem globalPullback_native_stalk (D : CartierDivisor X)
    (hD : HasRegularCartierEquations X D)
    (a : q.asIdeal) (P : PrimeSpectrum (chartRing q.asIdeal a)) :
    Ideal.map (openImmersionStalkLocalizationEquiv (chartInclusion j q hclosed a) P).toRingHom
      (Ideal.map ((PointBlowupGluing.scheme j q hclosed).presheaf.germ
        (wholeChartAffineOpen j q hclosed a).1 ((chartInclusion j q hclosed a).base P)
        (mem_chart_image_top (chartInclusion j q hclosed a) P)).hom
        ((pullbackIdealData (projection j q hclosed) D hD).ideal
          (wholeChartAffineOpen j q hclosed a))) =
      Ideal.map (algebraMap (chartRing q.asIdeal a) (Localization.AtPrime P.asIdeal))
        (Ideal.map (chartBaseMap q.asIdeal a)
          (Ideal.map (KltDP.Geometry.chartSectionsEquiv j).toRingHom
            ((effectiveCartierIdealDataOfRegularEquations X D hD).ideal
              ⟨j ''ᵁ ⊤, chart_image_top_isAffineOpen j⟩))) := by
  have hx : (projection j q hclosed).base ((chartInclusion j q hclosed a).base P) ∈ j ''ᵁ ⊤ := by
    have hp := congrArg
      (fun f : Spec (CommRingCat.of (chartRing q.asIdeal a)) ⟶ X => f.base P)
      (chartInclusion_projection j q hclosed a)
    change (projection j q hclosed).base ((chartInclusion j q hclosed a).base P) =
      j.base (PrimeSpectrum.comap (chartBaseMap q.asIdeal a) P) at hp
    rw [hp]
    exact mem_chart_image_top j (PrimeSpectrum.comap (chartBaseMap q.asIdeal a) P)
  rw [pullbackIdealData_map_germ (projection j q hclosed) D hD
    ⟨j ''ᵁ ⊤, chart_image_top_isAffineOpen j⟩ (wholeChartAffineOpen j q hclosed a)
    ((chartInclusion j q hclosed a).base P)
    (mem_chart_image_top (chartInclusion j q hclosed a) P) hx]
  exact openChartSquare_stalkMap_ideal j (chartInclusion j q hclosed a)
    (projection j q hclosed) (chartBaseMap q.asIdeal a)
    (chartInclusion_projection j q hclosed a) P hx
    ((effectiveCartierIdealDataOfRegularEquations X D hD).ideal
      ⟨j ''ᵁ ⊤, chart_image_top_isAffineOpen j⟩)

end KltDP.Geometry.PointBlowupChartStalk
