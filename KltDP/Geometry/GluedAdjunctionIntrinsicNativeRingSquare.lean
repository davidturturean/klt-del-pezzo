import KltDP.Geometry.AdjunctionTensorRestrictionRingDictionaries
import KltDP.Geometry.GluedAdjunctionBasicOpenAlgebra

/-!
# The original generic ring equation at the original principal chart

This declaration only specializes the compiled ring equation. It does not
fold either tensor-chart hom or the original source-refinement hom.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.GluedAdjunctionIntrinsicNativeRingSquare

open GluedConormalBasicOpenLocalization

/-- The native original ring equation on an actual basic-open chart.
Only original ambient and quotient smoothness of the larger chart are inputs. -/
def native_square {R : Type u} [CommRing R] {X : Scheme.{u}}
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
    AdjunctionTensorRestrictionRingDictionaries.ring_square R
      (I.ideal_le_comap_ideal (X.affineBasicOpen_le r))
      (gluedAffineIdealEquation I U d hU) hU.symm hd
      (equation_span I U r d hU).symm (equation_regular U r d hd)
      (GluedAdjunctionBasicOpenAlgebra.restrictionTower f U r)
      hAmbient (GluedAdjunctionBasicOpenAlgebra.ambient_standardSmooth f U r)
      hCurve (GluedAdjunctionBasicOpenAlgebra.quotient_standardSmooth f I U r)
      (by
        change IsOpenImmersion (I.glueDataObjMap (X.affineBasicOpen_le r))
        infer_instance)

end KltDP.Geometry.GluedAdjunctionIntrinsicNativeRingSquare
