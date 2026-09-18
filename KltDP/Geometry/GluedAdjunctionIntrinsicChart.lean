import KltDP.Geometry.GluedAdjunctionAmbientChart

/-!
# Adjunction charts between the original global sheaves

Both endpoints are pullbacks of independently defined global objects:
the original relative differential sheaf on the closed subscheme, and the
ambient exterior sheaf pulled to it, tensored with its original normal
sheaf. The chart map is the existing adjunction map followed by the proved
ambient and tensor comparisons. No transition compatibility is an input.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory
universe u
namespace KltDP.Geometry.GluedAdjunctionIntrinsicChart

local instance modulesMonoidal (Y : Scheme.{u}) : MonoidalCategory Y.Modules :=
  Scheme.Modules.monoidalCategory Y

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of R)) (I : X.IdealSheafData)
  (hI : IdealLocallyPrincipalRegular I) (U : X.affineOpens)

/-- The original global ambient exterior factor tensored with the original normal sheaf. -/
abbrev targetSheaf : I.glueData.glued.Modules :=
  GluedAdjunctionAmbientChart.globalAmbientSheaf f I ⊗
    GluedConormalTildeDualChart.globalNormalSheaf I

/-- The actual target comparison uses the original pullback tensor isomorphism. -/
def targetIso :
    letI : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
    ∀ [Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1)],
      GluedNormalTwistedAdjunctionChart.ambientSheaf I U R ⊗
          GluedNormalTwistedAdjunctionChart.normalSheaf I U ≅
        (schemeModulePullback (I.glueData.ι U)).obj (targetSheaf f I) := by
  letI : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  intro _
  exact whiskerRightIso (GluedAdjunctionAmbientChart.iso f I U)
      (GluedNormalTwistedAdjunctionChart.normalSheaf I U) ≪≫
    (schemeModulePullbackTensorIso (I.glueData.ι U)
      (GluedAdjunctionAmbientChart.globalAmbientSheaf f I)
      (GluedConormalTildeDualChart.globalNormalSheaf I)).symm

variable (d : Γ(X, U.1)) (hU : I.ideal U = Ideal.span {d})
  (hd : d ∈ nonZeroDivisors Γ(X, U.1))

/-- The original local adjunction map now has the original global objects at both ends. -/
def iso :
    letI : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
    ∀ [Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1)]
      [Algebra.IsStandardSmoothOfRelativeDimension 1 R (Γ(X, U.1) ⧸ I.ideal U)],
      (schemeModulePullback (I.glueData.ι U)).obj
          (SchemeKaehlerSheaf.baseRingSheaf (I.gluedTo ≫ f)) ≅
        (schemeModulePullback (I.glueData.ι U)).obj (targetSheaf f I) := by
  letI : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  intro _ _
  exact GluedNormalTwistedAdjunctionGlobalChart.iso f I hI U d hU hd ≪≫ targetIso f I U

/-- Changing the regular equation preserves the actual global-object chart map. -/
theorem iso_eq (e : Γ(X, U.1)) (hE : I.ideal U = Ideal.span {e})
    (he : e ∈ nonZeroDivisors Γ(X, U.1)) :
    letI : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
    ∀ [Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1)]
      [Algebra.IsStandardSmoothOfRelativeDimension 1 R (Γ(X, U.1) ⧸ I.ideal U)],
      iso f I hI U d hU hd = iso f I hI U e hE he := by
  letI : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  intro _ _
  unfold iso
  rw [GluedNormalTwistedAdjunctionGlobalChart.iso_eq f I hI U d hU hd e hE he]

end KltDP.Geometry.GluedAdjunctionIntrinsicChart
