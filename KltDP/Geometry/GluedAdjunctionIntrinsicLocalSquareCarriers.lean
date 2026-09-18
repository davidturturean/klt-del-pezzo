import KltDP.Geometry.GluedAdjunctionIntrinsicLocalSourceNormalization

/-! Retain the original local square and reduce its measured monoidal alias. -/
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.GluedAdjunctionIntrinsicLocalSquareCarriers

/-- The original normalized source/local square with the canonical monoidal annotation. -/
def local_square {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (I : X.IdealSheafData)
    (U : X.affineOpens) (r d : Γ(X, U.1))
    (hU : I.ideal U = Ideal.span {d}) (hd : d ∈ nonZeroDivisors Γ(X, U.1)) :=
  let _ : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  let _ : Algebra R Γ(X, (X.affineBasicOpen r).1) :=
    GluedChartKaehlerPullback.chartAlgebra f (X.affineBasicOpen r)
  fun (hAmbient : Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1))
      (hCurve : Algebra.IsStandardSmoothOfRelativeDimension 1 R (Γ(X, U.1) ⧸ I.ideal U)) => by
    letI : Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1) := hAmbient
    letI : Algebra.IsStandardSmoothOfRelativeDimension 1 R (Γ(X, U.1) ⧸ I.ideal U) := hCurve
    have h := GluedAdjunctionIntrinsicLocalSourceNormalization.local_square
      f I U r d hU hd hAmbient hCurve
    dsimp only [NormalTwistedAdjunctionTensorChart.sheafMonoidal] at h
    exact h

end KltDP.Geometry.GluedAdjunctionIntrinsicLocalSquareCarriers
