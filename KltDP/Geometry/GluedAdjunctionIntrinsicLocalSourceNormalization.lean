import KltDP.Geometry.AdjunctionTensorRestrictionNativeBaseProof
import KltDP.Geometry.GluedAdjunctionBasicOpenAlgebra
import KltDP.Geometry.GluedChartKaehlerRefinement

/-!
# Specialize the original source-refinement equation after its abstract fold

The imported equation already folds both tensor maps and the composite
source isomorphism. Supply the original chart data and its original proved
base-map equality, retaining the formula defining the original refinementIso.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.GluedAdjunctionIntrinsicLocalSourceNormalization

open GluedConormalBasicOpenLocalization

/-- The original local adjunction square, directly specialized from the folded ring equation. -/
def local_square {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (I : X.IdealSheafData)
    (U : X.affineOpens) (r d : Γ(X, U.1))
    (hU : I.ideal U = Ideal.span {d}) (hd : d ∈ nonZeroDivisors Γ(X, U.1)) :=
  let _ : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  let _ : Algebra R Γ(X, (X.affineBasicOpen r).1) :=
    GluedChartKaehlerPullback.chartAlgebra f (X.affineBasicOpen r)
  fun (hAmbient : Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1))
      (hCurve : Algebra.IsStandardSmoothOfRelativeDimension 1 R (Γ(X, U.1) ⧸ I.ideal U)) =>
    let _ : Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1) := hAmbient
    let _ : Algebra.IsStandardSmoothOfRelativeDimension 1 R (Γ(X, U.1) ⧸ I.ideal U) := hCurve
    AdjunctionTensorRestrictionNativeBaseProof.ring_square R
      (I.ideal_le_comap_ideal (X.affineBasicOpen_le r))
      (gluedAffineIdealEquation I U d hU) hU.symm hd
      (equation_span I U r d hU).symm (equation_regular U r d hd)
      (gluedAffineIdealEquation I (X.affineBasicOpen r) (sectionMap U r d)
        (equation_span I U r d hU))
      (equation_span I U r d hU).symm (equation_regular U r d hd)
      (GluedAdjunctionBasicOpenAlgebra.restrictionTower f U r)
      hAmbient (GluedAdjunctionBasicOpenAlgebra.ambient_standardSmooth f U r)
      hCurve (GluedAdjunctionBasicOpenAlgebra.quotient_standardSmooth f I U r)
      (by
        change IsOpenImmersion (I.glueDataObjMap (X.affineBasicOpen_le r))
        infer_instance)
      (GluedChartKaehlerRefinement.basicOpenBaseMap_comp f I U r)

end KltDP.Geometry.GluedAdjunctionIntrinsicLocalSourceNormalization
