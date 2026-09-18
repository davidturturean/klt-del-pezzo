import KltDP.Geometry.GluedAdjunctionIntrinsicChart
import KltDP.Geometry.ModuleOpenOver
import KltDP.Geometry.ModuleRestrictionPullback

/-!
# Original adjunction charts on the actual open and over-site restrictions

The original quotient-chart isomorphism identifies its scheme with the
original preimage open in the glued closed subscheme. The proved pullback
composition transports the original intrinsic adjunction map to that open.
The existing open-to-over comparison then places the same map on the
original over site, ready for the pinned sheaf descent construction.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.GluedAdjunctionOpenChart

private def transportIso {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (P : D ⥤ E) (G : C ⥤ E) (c : F ⋙ P ≅ G)
    {M N : C} (e : F.obj M ≅ F.obj N) : G.obj M ≅ G.obj N :=
  (c.app M).symm ≪≫ P.mapIso e ≪≫ c.app N

variable {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens)

/-- The original preimage open in the actual glued closed scheme. -/
abbrev chartOpen : I.glueData.glued.Opens := I.gluedTo ⁻¹ᵁ U.1

/-- The inverse of the original quotient-chart isomorphism respects its original inclusion. -/
theorem chartIso_inv_ι :
    (I.glueDataObjIso U).inv ≫ I.glueData.ι U = (chartOpen I U).ι := by
  rw [← I.glueDataObjIso_hom_ι U, Iso.inv_hom_id_assoc]

/-- The original chart pullback is transported to the original preimage-open pullback. -/
def chartOpenPullbackIso :
    schemeModulePullback (I.glueData.ι U) ⋙ schemeModulePullback (I.glueDataObjIso U).inv ≅
      schemeModulePullback (chartOpen I U).ι :=
  schemeModulePullbackCompIso (I.glueDataObjIso U).inv (I.glueData.ι U) ≪≫
    eqToIso (congrArg schemeModulePullback (chartIso_inv_ι I U))

variable {R : Type u} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R))
  (hI : IdealLocallyPrincipalRegular I) (d : Γ(X, U.1))
  (hU : I.ideal U = Ideal.span {d}) (hd : d ∈ nonZeroDivisors Γ(X, U.1))

/-- The original intrinsic adjunction map, on the actual canonical open inclusion. -/
def openIso :
    letI : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
    ∀ [Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1)]
      [Algebra.IsStandardSmoothOfRelativeDimension 1 R (Γ(X, U.1) ⧸ I.ideal U)],
      (schemeModulePullback (chartOpen I U).ι).obj
          (SchemeKaehlerSheaf.baseRingSheaf (I.gluedTo ≫ f)) ≅
        (schemeModulePullback (chartOpen I U).ι).obj
          (GluedAdjunctionIntrinsicChart.targetSheaf f I) := by
  letI : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  intro _ _
  exact transportIso (schemeModulePullback (I.glueData.ι U))
    (schemeModulePullback (I.glueDataObjIso U).inv)
    (schemeModulePullback (chartOpen I U).ι) (chartOpenPullbackIso I U)
    (GluedAdjunctionIntrinsicChart.iso f I hI U d hU hd)

/-- Changing the original regular equation preserves its transported open map. -/
theorem openIso_eq (e : Γ(X, U.1)) (hE : I.ideal U = Ideal.span {e})
    (he : e ∈ nonZeroDivisors Γ(X, U.1)) :
    letI : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
    ∀ [Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1)]
      [Algebra.IsStandardSmoothOfRelativeDimension 1 R (Γ(X, U.1) ⧸ I.ideal U)],
      openIso I U f hI d hU hd = openIso I U f hI e hE he := by
  letI : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  intro _ _
  unfold openIso
  rw [GluedAdjunctionIntrinsicChart.iso_eq f I hI U d hU hd e hE he]

/-- The same actual adjunction map on the original over-site module restrictions. -/
def overIso :
    letI : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
    ∀ [Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1)]
      [Algebra.IsStandardSmoothOfRelativeDimension 1 R (Γ(X, U.1) ⧸ I.ideal U)],
      (SchemeKaehlerSheaf.baseRingSheaf (I.gluedTo ≫ f)).over (chartOpen I U) ≅
        (GluedAdjunctionIntrinsicChart.targetSheaf f I).over (chartOpen I U) := by
  letI : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  intro _ _
  let M := SchemeKaehlerSheaf.baseRingSheaf (I.gluedTo ≫ f)
  let N := GluedAdjunctionIntrinsicChart.targetSheaf f I
  let c := SchemeModuleRestriction.restrictionIsoPullback (chartOpen I U).ι
  exact (openToOverRestrictionIso (chartOpen I U) M).symm ≪≫
    (openToOverFunctor (chartOpen I U)).mapIso
      (c.app M ≪≫ openIso I U f hI d hU hd ≪≫ (c.app N).symm) ≪≫
      openToOverRestrictionIso (chartOpen I U) N

end KltDP.Geometry.GluedAdjunctionOpenChart
