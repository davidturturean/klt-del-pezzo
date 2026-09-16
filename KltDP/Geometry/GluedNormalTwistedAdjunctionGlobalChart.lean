import KltDP.Geometry.GluedChartKaehlerPullback
import KltDP.Geometry.GluedNormalTwistedAdjunctionChart

/-!
# The original global differential and normal sheaves in the adjunction chart

The source is the actual global relative Kähler sheaf restricted to an
original quotient chart. The right tensor factor is the restriction of
the actual dual global conormal. The chosen base algebra comes from the
original global structure morphism. Only the original local standard
smoothness conditions are used. The ambient top-form factor is still its
affine presentation; its canonical comparison and descent remain separate.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory
universe u
namespace KltDP.Geometry.GluedNormalTwistedAdjunctionGlobalChart

local instance modulesMonoidal (Y : Scheme.{u}) : MonoidalCategory Y.Modules :=
  Scheme.Modules.monoidalCategory Y

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of R)) (I : X.IdealSheafData)
  (hI : IdealLocallyPrincipalRegular I) (U : X.affineOpens)
  (d : Γ(X, U.1)) (hU : I.ideal U = Ideal.span {d})
  (hd : d ∈ nonZeroDivisors Γ(X, U.1))

/-- The actual global-object adjunction chart for the induced original base algebra. -/
def iso :
    letI : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
    ∀ [Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1)]
      [Algebra.IsStandardSmoothOfRelativeDimension 1 R (Γ(X, U.1) ⧸ I.ideal U)],
      (schemeModulePullback (I.glueData.ι U)).obj
          (SchemeKaehlerSheaf.baseRingSheaf (I.gluedTo ≫ f)) ≅
        GluedNormalTwistedAdjunctionChart.ambientSheaf I U R ⊗
          GluedNormalTwistedAdjunctionChart.normalSheaf I U := by
  letI : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  intro _ _
  exact GluedChartKaehlerPullback.iso f I U ≪≫
    GluedNormalTwistedAdjunctionChart.iso I hI U R d hU hd

/-- The actual global-object chart is independent of the chosen regular equation. -/
theorem iso_eq (e : Γ(X, U.1)) (hE : I.ideal U = Ideal.span {e})
    (he : e ∈ nonZeroDivisors Γ(X, U.1)) :
    letI : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
    ∀ [Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1)]
      [Algebra.IsStandardSmoothOfRelativeDimension 1 R (Γ(X, U.1) ⧸ I.ideal U)],
      iso f I hI U d hU hd = iso f I hI U e hE he := by
  letI : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  intro _ _
  unfold iso
  rw [GluedNormalTwistedAdjunctionChart.iso_eq I hI U R d hU hd e hE he]

end KltDP.Geometry.GluedNormalTwistedAdjunctionGlobalChart
