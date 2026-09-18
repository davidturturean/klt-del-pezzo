import KltDP.Geometry.GluedAdjunctionIntrinsicChartHom

/-!
# Retain the original intrinsic chart hom in its checked decomposition

Start from the original chart hom's inferred reflexive equality. Expose
only its defining isomorphisms on one side, then use the existing abstract
normalization of that same composition. The original map remains the
literal other side, ready for both ends of the refinement diagram.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.GluedAdjunctionIntrinsicOriginalHom

private theorem replace_expanded {α : Sort*} {expanded original normalized : α}
    (hOriginal : expanded = original) (hNormalized : expanded = normalized) :
    original = normalized := hOriginal.symm.trans hNormalized

private def original_expansion {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (I : X.IdealSheafData)
    (hI : IdealLocallyPrincipalRegular I) (U : X.affineOpens)
    (d : Γ(X, U.1)) (hU : I.ideal U = Ideal.span {d})
    (hd : d ∈ nonZeroDivisors Γ(X, U.1)) :=
  let _ : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  fun (hAmbient : Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1))
      (hCurve : Algebra.IsStandardSmoothOfRelativeDimension 1 R (Γ(X, U.1) ⧸ I.ideal U)) => by
    letI : Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1) := hAmbient
    letI : Algebra.IsStandardSmoothOfRelativeDimension 1 R (Γ(X, U.1) ⧸ I.ideal U) := hCurve
    have h := Eq.refl ((GluedAdjunctionIntrinsicChart.iso f I hI U d hU hd).hom)
    conv at h =>
      lhs
      unfold GluedAdjunctionIntrinsicChart.iso GluedAdjunctionIntrinsicChart.targetIso
        GluedNormalTwistedAdjunctionGlobalChart.iso GluedNormalTwistedAdjunctionChart.iso
        GluedNormalTwistedAdjunctionChart.normalTensorIso
    exact h

/-- The actual original intrinsic chart hom, with the checked original factors. -/
def original_hom {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (I : X.IdealSheafData)
    (hI : IdealLocallyPrincipalRegular I) (U : X.affineOpens)
    (d : Γ(X, U.1)) (hU : I.ideal U = Ideal.span {d})
    (hd : d ∈ nonZeroDivisors Γ(X, U.1)) :=
  let _ : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  fun (hAmbient : Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1))
      (hCurve : Algebra.IsStandardSmoothOfRelativeDimension 1 R (Γ(X, U.1) ⧸ I.ideal U)) =>
    let _ : Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1) := hAmbient
    let _ : Algebra.IsStandardSmoothOfRelativeDimension 1 R (Γ(X, U.1) ⧸ I.ideal U) := hCurve
    replace_expanded (original_expansion f I hI U d hU hd hAmbient hCurve)
      (GluedAdjunctionIntrinsicChartHom.iso_hom f I hI U d hU hd)

end KltDP.Geometry.GluedAdjunctionIntrinsicOriginalHom
