import KltDP.Geometry.GluedAdjunctionIntrinsicTargetSquare
import KltDP.Geometry.GluedAdjunctionIntrinsicCarrierAliases

/-! The original target square with the chart and monoidal annotations already
used by the other three compiled diagram inputs. No target map is reconstructed. -/
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.GluedAdjunctionIntrinsicTargetSquareCarriers
open GluedAdjunctionIntrinsicCarrierAliases

/-- Retain the original ambient/normal/tensor square in the native chart presentation. -/
def target_square {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (I : X.IdealSheafData)
    (hI : IdealLocallyPrincipalRegular I) (U : X.affineOpens) (r d : Γ(X, U.1))
    (hU : I.ideal U = Ideal.span {d}) (hd : d ∈ nonZeroDivisors Γ(X, U.1)) :=
  let _ : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  fun (hAmbient : Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1)) => by
    letI : Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1) := hAmbient
    have h := GluedAdjunctionIntrinsicTargetSquare.target_square f I hI U r d hU hd hAmbient
    dsimp only [chart_scheme, Scheme.IdealSheafData.glueDataObj,
      Scheme.IdealSheafData.glueDataObjMap,
      GluedAdjunctionTensorRefinement.refinementTensor,
      Ideal.Quotient.semiring, quotient_commSemiring] at h
    exact h

end KltDP.Geometry.GluedAdjunctionIntrinsicTargetSquareCarriers
