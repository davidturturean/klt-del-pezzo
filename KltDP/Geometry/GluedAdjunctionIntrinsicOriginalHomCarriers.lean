import KltDP.Geometry.GluedAdjunctionIntrinsicCarrierAliases

/-!
# Preserve the original chart map with canonical native chart annotations

Only the measured chart projection, monoidal aliases and quotient dictionary
are reduced. The original intrinsic map and its original factors are retained.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.GluedAdjunctionIntrinsicOriginalHomCarriers
open GluedAdjunctionIntrinsicCarrierAliases

/-- The same original chart equation with its native chart carrier annotations. -/
def original_hom {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (I : X.IdealSheafData)
    (hI : IdealLocallyPrincipalRegular I) (U : X.affineOpens)
    (d : Γ(X, U.1)) (hU : I.ideal U = Ideal.span {d})
    (hd : d ∈ nonZeroDivisors Γ(X, U.1)) :=
  let _ : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  fun (hAmbient : Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1))
      (hCurve : Algebra.IsStandardSmoothOfRelativeDimension 1 R (Γ(X, U.1) ⧸ I.ideal U)) => by
    letI : Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1) := hAmbient
    letI : Algebra.IsStandardSmoothOfRelativeDimension 1 R (Γ(X, U.1) ⧸ I.ideal U) := hCurve
    have h := GluedAdjunctionIntrinsicOriginalHom.original_hom f I hI U d hU hd hAmbient hCurve
    dsimp only [chart_scheme, Scheme.IdealSheafData.glueDataObj,
      GluedAdjunctionIntrinsicChartHom.intrinsicHomTensor,
      NormalTwistedAdjunctionTensorChart.sheafMonoidal,
      Ideal.Quotient.semiring, quotient_commSemiring] at h
    exact h

end KltDP.Geometry.GluedAdjunctionIntrinsicOriginalHomCarriers
