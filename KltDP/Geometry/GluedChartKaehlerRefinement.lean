import KltDP.Geometry.GluedChartKaehlerPullback
import KltDP.Geometry.GluedConormalBasicOpenLocalization

/-!
# Original global Kähler chart maps on an actual basic-open refinement

The actual quotient-chart inclusion commutes with the original global
base map. Composition of the existing Kähler pullback isomorphisms then
identifies its original native Kähler restriction with the restriction of
the actual global source chart. No comparison equality is supplied.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.GluedChartKaehlerRefinement

open SchemeKaehlerSheaf SchemeKaehlerOpenRestriction

private theorem pullbackIso_transport_comp {R : Type u} [CommRing R]
    {X Y Z : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (j : Y ⟶ X) (l : Z ⟶ Y) [IsOpenImmersion j] [IsOpenImmersion l]
    (g : Y ⟶ Spec (CommRingCat.of R)) (hg : j ≫ f = g)
    (t : Z ⟶ X) [IsOpenImmersion t] (ht : l ≫ j = t)
    (q : Z ⟶ Spec (CommRingCat.of R)) (hq : l ≫ g = q) (hqt : t ≫ f = q) :
    (schemeModulePullback l).mapIso (pullbackIso f j ≪≫ eqToIso (congrArg baseRingSheaf hg)) ≪≫
        pullbackIso g l ≪≫ eqToIso (congrArg baseRingSheaf hq) =
      (schemeModulePullbackCompIso l j).app (baseRingSheaf f) ≪≫
        eqToIso (congrArg (fun a => (schemeModulePullback a).obj (baseRingSheaf f)) ht) ≪≫
        pullbackIso f t ≪≫ eqToIso (congrArg baseRingSheaf hqt) := by
  cases hg
  cases ht
  cases hq
  simpa only [eqToIso_refl, Iso.trans_refl, Iso.refl_trans] using
    (pullbackIso_comp f j l).symm

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of R)) (I : X.IdealSheafData)
  (U : X.affineOpens) (r : Γ(X, U.1))

/-- The original native structure maps commute with the actual quotient-chart refinement. -/
theorem basicOpenBaseMap_comp :
    letI : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
    letI : Algebra R Γ(X, (X.affineBasicOpen r).1) :=
      GluedChartKaehlerPullback.chartAlgebra f (X.affineBasicOpen r)
    I.glueDataObjMap (X.affineBasicOpen_le r) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (Γ(X, U.1) ⧸ I.ideal U))) =
      Spec.map (CommRingCat.ofHom
        (algebraMap R (Γ(X, (X.affineBasicOpen r).1) ⧸ I.ideal (X.affineBasicOpen r)))) := by
  letI : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  letI : Algebra R Γ(X, (X.affineBasicOpen r).1) :=
    GluedChartKaehlerPullback.chartAlgebra f (X.affineBasicOpen r)
  calc
    _ = I.glueDataObjMap (X.affineBasicOpen_le r) ≫
        (I.glueData.ι U ≫ (I.gluedTo ≫ f)) :=
      congrArg (fun g => I.glueDataObjMap (X.affineBasicOpen_le r) ≫ g)
        (GluedChartKaehlerPullback.chartBaseMap_comp f I U).symm
    _ = I.glueData.ι (X.affineBasicOpen r) ≫ (I.gluedTo ≫ f) := by
      rw [← Category.assoc, I.glueDataObjMap_ι]
    _ = _ := GluedChartKaehlerPullback.chartBaseMap_comp f I (X.affineBasicOpen r)

/-- The actual Kähler pullback along the original quotient-chart refinement. -/
def refinementIso :
    letI : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
    letI : Algebra R Γ(X, (X.affineBasicOpen r).1) :=
      GluedChartKaehlerPullback.chartAlgebra f (X.affineBasicOpen r)
    (schemeModulePullback (I.glueDataObjMap (X.affineBasicOpen_le r))).obj
        (baseRingSheaf
          (Spec.map (CommRingCat.ofHom (algebraMap R (Γ(X, U.1) ⧸ I.ideal U))))) ≅
      baseRingSheaf (Spec.map (CommRingCat.ofHom
        (algebraMap R (Γ(X, (X.affineBasicOpen r).1) ⧸ I.ideal (X.affineBasicOpen r))))) := by
  letI : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  letI : Algebra R Γ(X, (X.affineBasicOpen r).1) :=
    GluedChartKaehlerPullback.chartAlgebra f (X.affineBasicOpen r)
  exact pullbackIso
      (Spec.map (CommRingCat.ofHom (algebraMap R (Γ(X, U.1) ⧸ I.ideal U))))
      (I.glueDataObjMap (X.affineBasicOpen_le r)) ≪≫
    eqToIso (congrArg baseRingSheaf (basicOpenBaseMap_comp f I U r))

/-- The original global source chart commutes with the actual basic-open Kähler restriction. -/
theorem iso_refinement :
    letI : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
    letI : Algebra R Γ(X, (X.affineBasicOpen r).1) :=
      GluedChartKaehlerPullback.chartAlgebra f (X.affineBasicOpen r)
    (schemeModulePullback (I.glueDataObjMap (X.affineBasicOpen_le r))).mapIso
        (GluedChartKaehlerPullback.iso f I U) ≪≫ refinementIso f I U r =
      (schemeModulePullbackCompIso (I.glueDataObjMap (X.affineBasicOpen_le r))
        (I.glueData.ι U)).app (baseRingSheaf (I.gluedTo ≫ f)) ≪≫
        eqToIso (congrArg
          (fun a => (schemeModulePullback a).obj (baseRingSheaf (I.gluedTo ≫ f)))
          (I.glueDataObjMap_ι (X.affineBasicOpen r) U (X.affineBasicOpen_le r))) ≪≫
        GluedChartKaehlerPullback.iso f I (X.affineBasicOpen r) := by
  letI : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  letI : Algebra R Γ(X, (X.affineBasicOpen r).1) :=
    GluedChartKaehlerPullback.chartAlgebra f (X.affineBasicOpen r)
  exact pullbackIso_transport_comp (I.gluedTo ≫ f) (I.glueData.ι U)
    (I.glueDataObjMap (X.affineBasicOpen_le r)) _
    (GluedChartKaehlerPullback.chartBaseMap_comp f I U)
    (I.glueData.ι (X.affineBasicOpen r))
    (I.glueDataObjMap_ι (X.affineBasicOpen r) U (X.affineBasicOpen_le r)) _
    (basicOpenBaseMap_comp f I U r)
    (GluedChartKaehlerPullback.chartBaseMap_comp f I (X.affineBasicOpen r))

end KltDP.Geometry.GluedChartKaehlerRefinement
