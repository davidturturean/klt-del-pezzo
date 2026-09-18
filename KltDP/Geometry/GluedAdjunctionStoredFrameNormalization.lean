import KltDP.Geometry.GluedAdjunctionAffineExteriorRefinement

/-!
# The original stored affine-frame map on one chart

Specialize the already checked original frame equation. The source map is
`storedFrameHom`; the target is the original transported differential map
followed by the same native inverse. No new projection or map is substituted.
This producer has no dependency on the pending whole ambient refinement.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.GluedAdjunctionStoredFrameNormalization

/-- The original stored-frame equation specialized to the original affine chart.
Its inferred proposition retains both original map constants and all original arguments. -/
def affine_normalization {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (U : X.affineOpens) :=
  let _ : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  fun (hSmooth : Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1)) =>
    let _ : Algebra.IsStandardSmoothOfRelativeDimension 2 R Γ(X, U.1) := hSmooth
    GluedAdjunctionAffineExteriorRefinement.storedFrameHom_transport f U.2.fromSpec
      (Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, U.1))))
      (GluedAdjunctionAmbientChart.affineBaseMap_comp f U) 2
      (AffineDifferentialExteriorTildeMap.standardSmoothIso R Γ(X, U.1))

end KltDP.Geometry.GluedAdjunctionStoredFrameNormalization
