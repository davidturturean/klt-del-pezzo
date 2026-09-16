import KltDP.Geometry.GluedConormalBasicOpenFrames
import KltDP.Geometry.GluedConormalChartRefinement

/-!
# The actual global conormal tilde comparison commutes with basic-open refinement

The original tilde scalar-extension comparison preserves the original
local equation frame. The original global conormal frame satisfies the
same refinement square. Cancelling the produced invertible frame therefore
identifies the two actual sheaf isomorphisms.

The map, ideal cotangent modules, chart inclusions, pullback composition,
and equality transport are the original ones. No compatibility witness is
an input. Global adjunction descent remains separate.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.GluedConormalTildeRefinement

open GluedConormalBasicOpenLocalization GluedConormalEquationIndependence

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens)
  (r d : Γ(X, U.1)) (hI : I.ideal U = Ideal.span {d})
  (hd : d ∈ nonZeroDivisors Γ(X, U.1))

/-- The actual original conormal tilde comparison commutes with the actual quotient-chart
inclusion and the original global pullback composition. -/
theorem tildePullbackIso_refinement :
    (schemeModulePullback (I.glueDataObjMap (X.affineBasicOpen_le r))).mapIso
        (gluedAffineConormalTildePullbackIso I U d hI hd) ≪≫
      (schemeModulePullbackCompIso (I.glueDataObjMap (X.affineBasicOpen_le r))
        (I.glueData.ι U)).app (schemeConormalSheaf I.gluedTo) ≪≫
      (eqToIso (congrArg schemeModulePullback
        (I.glueDataObjMap_ι (X.affineBasicOpen r) U (X.affineBasicOpen_le r)))).app
        (schemeConormalSheaf I.gluedTo) =
    tildeRefinementIso I U r d hI hd ≪≫
      gluedAffineConormalTildePullbackIso I (X.affineBasicOpen r) (sectionMap U r d)
        (equation_span I U r d hI) (equation_regular U r d hd) := by
  let b := I.glueDataObjMap (X.affineBasicOpen_le r)
  let tU := tildeFrame I U d hI hd
  let tV := tildeFrame I (X.affineBasicOpen r) (sectionMap U r d)
    (equation_span I U r d hI) (equation_regular U r d hd)
  let eU := gluedAffineConormalTildePullbackIso I U d hI hd
  let eV := gluedAffineConormalTildePullbackIso I (X.affineBasicOpen r) (sectionMap U r d)
    (equation_span I U r d hI) (equation_regular U r d hd)
  let c := (schemeModulePullbackCompIso b (I.glueData.ι U)).app (schemeConormalSheaf I.gluedTo)
  let t := (eqToIso (congrArg schemeModulePullback
    (I.glueDataObjMap_ι (X.affineBasicOpen r) U (X.affineBasicOpen_le r)))).app
      (schemeConormalSheaf I.gluedTo)
  let e := tildeRefinementIso I U r d hI hd
  letI : IsIso (schemeModulePullbackFrame b tU.hom) := by
    unfold schemeModulePullbackFrame
    infer_instance
  apply Iso.ext
  apply (cancel_epi (schemeModulePullbackFrame b tU.hom)).mp
  change schemeModulePullbackFrame b tU.hom ≫
      ((schemeModulePullback b).map eU.hom ≫ c.hom ≫ t.hom) =
    schemeModulePullbackFrame b tU.hom ≫ (e.hom ≫ eV.hom)
  calc
    _ = schemeModulePullbackFrame b (tU.hom ≫ eU.hom) ≫ c.hom ≫ t.hom := by
      rw [schemeModulePullbackFrame_postcomp]
      simp only [Category.assoc]
    _ = schemeModulePullbackFrame b
        (gluedAffineConormalChartFrameIso I U d hI hd).hom ≫ c.hom ≫ t.hom := by
      rw [tildeFrame_comparison I U d hI hd]
    _ = (gluedAffineConormalChartFrameIso I (X.affineBasicOpen r) (sectionMap U r d)
        (equation_span I U r d hI) (equation_regular U r d hd)).hom :=
      GluedConormalChartRefinement.chartFrame_basicOpen I U r d hI hd
    _ = tV.hom ≫ eV.hom :=
      (tildeFrame_comparison I (X.affineBasicOpen r) (sectionMap U r d)
        (equation_span I U r d hI) (equation_regular U r d hd)).symm
    _ = schemeModulePullbackFrame b tU.hom ≫ (e.hom ≫ eV.hom) := by
      rw [← GluedConormalBasicOpenFrames.tildeFrame_refinement I U r d hI hd]
      simp only [b, tU, e, Category.assoc]

end KltDP.Geometry.GluedConormalTildeRefinement
