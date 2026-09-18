import KltDP.Geometry.GluedAdjunctionIntrinsicCarrierAliases
import KltDP.Geometry.GluedAdjunctionIntrinsicSourceSquare

/-!
# The original source square with its measured native chart annotations

Expose only the original refinement isomorphism at its occurrence in the
source square, then reduce the measured chart/map/dictionary aliases.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
namespace KltDP.Geometry.GluedAdjunctionIntrinsicSourceSquareCarriers
open GluedAdjunctionIntrinsicCarrierAliases

/-- The same original source square in the common native chart presentation. -/
def source_square {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (I : X.IdealSheafData)
    (U : X.affineOpens) (r : Γ(X, U.1)) :=
  let _ : Algebra R Γ(X, U.1) := GluedChartKaehlerPullback.chartAlgebra f U
  let _ : Algebra R Γ(X, (X.affineBasicOpen r).1) :=
    GluedChartKaehlerPullback.chartAlgebra f (X.affineBasicOpen r)
  by
    have h := GluedAdjunctionIntrinsicSourceSquare.source_square f I U r
    dsimp only at h
    conv at h =>
      lhs
      rhs
      unfold GluedChartKaehlerRefinement.refinementIso
    dsimp only [chart_scheme, Scheme.IdealSheafData.glueDataObj,
      Scheme.IdealSheafData.glueDataObjMap, Ideal.Quotient.semiring,
      quotient_commSemiring] at h
    exact h

end KltDP.Geometry.GluedAdjunctionIntrinsicSourceSquareCarriers
