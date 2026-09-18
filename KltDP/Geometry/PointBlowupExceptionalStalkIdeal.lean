import KltDP.Geometry.ExtendedCenterStalkIdeal
import KltDP.Geometry.StrictNormalCrossingsCartierAffineIdeal
import KltDP.Geometry.PointBlowupExceptionalIdeal
import KltDP.Geometry.PointBlowupChartStalkAtCenter

/-!
# The original whole exceptional kernel in the native chart stalk

The accepted exceptional-fibre pullback square preserves the actual
affine kernel ideal in the original chart ring. The original affine
exceptional ideal is the extended centre, whose stalk computation gives
the literal localized Rees centre ideal.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.PointBlowupChartStalk

open AffineBlowup PointBlowupGluing

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
variable (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
variable (q : PrimeSpectrum R) [q.asIdeal.IsMaximal]
variable (hclosed : IsClosed ({j.base q} : Set X)) (a : q.asIdeal)

/-- The original whole-blowup chart image, with its proved affineness. -/
abbrev wholeChartAffineOpen : (PointBlowupGluing.scheme j q hclosed).affineOpens :=
  ⟨chartInclusion j q hclosed a ''ᵁ ⊤,
    chart_image_top_isAffineOpen (chartInclusion j q hclosed a)⟩

/-- The actual whole centre-fibre kernel maps to the literal centre ideal
in every native chart local ring of the original blowup. -/
theorem globalCenterFiber_native_stalk (P : PrimeSpectrum (chartRing q.asIdeal a)) :
    Ideal.map (openImmersionStalkLocalizationEquiv (chartInclusion j q hclosed a) P).toRingHom
      (Ideal.map ((PointBlowupGluing.scheme j q hclosed).presheaf.germ
        (wholeChartAffineOpen j q hclosed a).1 ((chartInclusion j q hclosed a).base P)
        (mem_chart_image_top (chartInclusion j q hclosed a) P)).hom
        ((globalCenterFiberι j q hclosed).ker.ideal (wholeChartAffineOpen j q hclosed a))) =
      Ideal.map (algebraMap (chartRing q.asIdeal a) (Localization.AtPrime P.asIdeal))
        (chartCenterIdeal q.asIdeal a) := by
  let U : (AffineBlowup.scheme q.asIdeal).affineOpens :=
    ⟨chartι q.asIdeal a ''ᵁ ⊤, chart_image_top_isAffineOpen (chartι q.asIdeal a)⟩
  have hk := ker_ideal_map_eq_of_isPullback (affineBlowupι j q hclosed)
    (globalCenterFiberι j q hclosed) (exceptionalι q.asIdeal)
    (exceptionalGlobalFiberIso j q hclosed).hom
    (exceptionalGlobalFiber_isPullback j q hclosed)
    (chartInclusion j q hclosed a) (chartι q.asIdeal a) rfl
  simp only [exceptionalι, Scheme.IdealSheafData.ker_gluedTo] at hk
  have hg := openImmersionStalkLocalizationEquiv_germIdeal
    (chartInclusion j q hclosed a) P
    ((globalCenterFiberι j q hclosed).ker.ideal (wholeChartAffineOpen j q hclosed a))
  have ha := openImmersionStalkLocalizationEquiv_germIdeal
    (chartι q.asIdeal a) P ((exceptionalIdeal q.asIdeal).ideal U)
  have hc := extendedCenter_native_stalk q.asIdeal (toSpec q.asIdeal)
    (chartι q.asIdeal a) (chartBaseMap q.asIdeal a) (chartι_toSpec q.asIdeal a)
    P U (mem_chart_image_top (chartι q.asIdeal a) P)
  calc
    _ = _ := hg
    _ = Ideal.map (algebraMap (chartRing q.asIdeal a) (Localization.AtPrime P.asIdeal))
        (Ideal.map (KltDP.Geometry.chartSectionsEquiv (chartι q.asIdeal a)).toRingHom
          ((exceptionalIdeal q.asIdeal).ideal U)) :=
      congrArg (Ideal.map (algebraMap (chartRing q.asIdeal a) (Localization.AtPrime P.asIdeal)))
        hk.symm
    _ = _ := ha.symm.trans hc

end KltDP.Geometry.PointBlowupChartStalk
