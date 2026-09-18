import KltDP.Geometry.AdjunctionTensorRestrictionRingCharts
import KltDP.Geometry.GluedAdjunctionBasicOpenAlgebra

/-!
# Specialize the already-folded original tensor-chart equation

Both tensor-map equalities are checked over abstract rings in the imported
producer. This declaration supplies only the original chart data, including
the exact original smaller equation, and the proved smoothness instances.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.GluedAdjunctionIntrinsicTensorRingSquare

open GluedConormalBasicOpenLocalization

/-- The original tensor-chart square specialized without any concrete map fold. -/
def tensor_square {R : Type u} [CommRing R] {X : Scheme.{u}}
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
    AdjunctionTensorRestrictionRingCharts.ring_square R
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

end KltDP.Geometry.GluedAdjunctionIntrinsicTensorRingSquare
