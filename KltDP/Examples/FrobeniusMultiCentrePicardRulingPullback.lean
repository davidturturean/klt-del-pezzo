import KltDP.Examples.FrobeniusMultiCentrePicardRealization

/-!
# Original ruling pullbacks are the original realized basis vectors

These identities identify the actual two base line bundles under the
original multi-centre projection with the original realization map.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusMultiCentrePicardRulingPullback

open KltDP.Geometry FrobeniusProjectivePoints
open FrobeniusGraphPicardClassFrames FrobeniusGraphPicardClassFiberClasses
open FrobeniusMultiCentreSurface FrobeniusMultiCentrePicardRealization

variable {k : Type u} [Field k] (q n : ℕ) (a : Fin n → k)

/-- The first original ruling class is realized by the first unit vector. -/
theorem realization_first :
    realization q n a FrobeniusPicard.a = multiFirstFiberClass (q + 1) n a := by
  simp [realization_apply, FrobeniusPicard.a]

/-- The second original ruling class is realized by the second unit vector. -/
theorem realization_second :
    realization q n a FrobeniusPicard.b = multiSecondFiberClass (q + 1) n a := by
  simp [realization_apply, FrobeniusPicard.b]

/-- Original first-ruling pullback equals the corresponding actual realization. -/
theorem firstFiberClass_pullback :
    (schemePicardPullbackHom (multiProjection (q + 1) n a)).toAdditive
      (firstFiberClass (k := k)) = realization q n a FrobeniusPicard.a := by
  rw [realization_first]
  simp only [firstFiberClass, map_neg, multiFirstFiberClass]
  change -Additive.ofMul (schemePicardPullbackHom (multiProjection (q + 1) n a)
    (verticalFiberIdealLine (k := k)).toPic) = _
  rw [schemePicardPullbackHom_toPic]

/-- Original second-ruling pullback equals the corresponding actual realization. -/
theorem secondFiberClass_pullback :
    (schemePicardPullbackHom (multiProjection (q + 1) n a)).toAdditive
      (secondFiberClass (k := k)) = realization q n a FrobeniusPicard.b := by
  rw [realization_second]
  simp only [secondFiberClass, map_neg, multiSecondFiberClass]
  change -Additive.ofMul (schemePicardPullbackHom (multiProjection (q + 1) n a)
    (graphIdealLine (k := k) 0).toPic) = _
  rw [schemePicardPullbackHom_toPic]

end KltDP.Examples.FrobeniusMultiCentrePicardRulingPullback
