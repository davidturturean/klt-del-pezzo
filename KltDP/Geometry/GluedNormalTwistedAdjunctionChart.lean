import KltDP.Geometry.NormalTwistedAdjunctionTensorChart
import KltDP.Geometry.GluedConormalNormalEquationIndependence

/-!
# The affine adjunction chart with the actual global normal factor

The original tensor adjunction chart is followed by the already produced
comparison from the original normal module tilde to the pullback of the
dual of the original global conormal. Both maps are independent of the
regular equation. The ambient factor is still the actual ambient top-form
tilde pulled to the quotient chart; its global canonical identification
and the final gluing are separate consumers.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory
universe u
namespace KltDP.Geometry.GluedNormalTwistedAdjunctionChart

local instance modulesMonoidal (Y : Scheme.{u}) : MonoidalCategory Y.Modules :=
  Scheme.Modules.monoidalCategory Y

variable {X : Scheme.{u}} (I : X.IdealSheafData) (hI : IdealLocallyPrincipalRegular I)
  (U : X.affineOpens) (R : Type u) [CommRing R] [Algebra R Γ(X, U.1)]
  [Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1)]
  [Algebra.IsStandardSmoothOfRelativeDimension 1 R (Γ(X, U.1) ⧸ I.ideal U)]

/-- The actual ambient top differential tilde pulled through the original quotient map. -/
abbrev ambientSheaf : (I.glueDataObj U).Modules :=
  (schemeModulePullback
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U))))).obj
      (ModuleCat.of Γ(X, U.1) (⋀[Γ(X, U.1)]^2 (KaehlerDifferential R Γ(X, U.1)))).tilde

/-- The actual global normal sheaf restricted to the original quotient chart. -/
abbrev normalSheaf : (I.glueDataObj U).Modules :=
  (schemeModulePullback (I.glueData.ι U)).obj
    (GluedConormalTildeDualChart.globalNormalSheaf I)

variable (d : Γ(X, U.1)) (hU : I.ideal U = Ideal.span {d})
  (hd : d ∈ nonZeroDivisors Γ(X, U.1))

/-- Tensor the produced global-normal comparison with the actual ambient factor. -/
def normalTensorIso :
    ambientSheaf I U R ⊗ (PrincipalConormalTildeDual.normalModule (I.ideal U)).tilde ≅
      ambientSheaf I U R ⊗ normalSheaf I U :=
  whiskerLeftIso (ambientSheaf I U R)
    (GluedConormalTildeDualChart.chartIso I hI U d hU hd)

/-- The original quotient Kähler sheaf is the actual ambient factor tensored
with the chart pullback of the actual global conormal dual. -/
def iso :
    SchemeKaehlerSheaf.baseRingSheaf
      (Spec.map (CommRingCat.ofHom (algebraMap R (Γ(X, U.1) ⧸ I.ideal U)))) ≅
        ambientSheaf I U R ⊗ normalSheaf I U :=
  NormalTwistedAdjunctionTensorChart.iso R Γ(X, U.1) (I.ideal U)
    (gluedAffineIdealEquation I U d hU) hU.symm hd ≪≫
      normalTensorIso I hI U R d hU hd

/-- The normal-factor map retains its original evaluation-normalized comparison. -/
theorem normalTensorIso_hom :
    (normalTensorIso I hI U R d hU hd).hom =
      ambientSheaf I U R ◁ (GluedConormalTildeDualChart.chartIso I hI U d hU hd).hom := rfl

/-- Changing the regular equation changes neither original factor comparison. -/
theorem iso_eq (e : Γ(X, U.1)) (hE : I.ideal U = Ideal.span {e})
    (he : e ∈ nonZeroDivisors Γ(X, U.1)) :
    iso I hI U R d hU hd = iso I hI U R e hE he := by
  unfold iso normalTensorIso
  rw [NormalTwistedAdjunctionTensorChart.iso_eq R Γ(X, U.1) (I.ideal U)
    (gluedAffineIdealEquation I U d hU) hU.symm hd
    (gluedAffineIdealEquation I U e hE) hE.symm he]
  rw [GluedConormalNormalEquationIndependence.chartIso_eq I hI U d e hU hd hE he]

end KltDP.Geometry.GluedNormalTwistedAdjunctionChart
