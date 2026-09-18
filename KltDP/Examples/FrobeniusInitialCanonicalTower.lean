import KltDP.Examples.FrobeniusInitialCanonicalFormula

/-!
# The explicit canonical class at every original contact-tower depth

Substitute the proved original initial canonical formula into the existing
all-depth iteration. Every pullback is the original whole-stage projection
and every exceptional class is the existing total-transform class. There
is no projectivity, characteristic, or initial-canonical-formula premise.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusInitialCanonicalTower

open KltDP.Geometry
open FrobeniusGlobalBlowupStages
open FrobeniusProjectivePoints FrobeniusGraphPicardClassFiberClasses
open FrobeniusStrictTransformClassesTower FrobeniusContactTowerSelectedPoint
open FrobeniusTowerTransportClasses FrobeniusContactTowerCanonicalIteration
open FrobeniusInitialCanonicalFormula

variable {k : Type u} [Field k]

/-- The actual original all-depth canonical class has the two pulled fiber terms
and the existing total exceptional classes. -/
theorem originalCanonicalClass_eq_fibers_exceptionals (N : ℕ) :
    originalCanonicalClass (k := k) N =
      (-2 : ℤ) • (schemePicardPullbackHom (projectiveContactProjection (k := k) N)).toAdditive
          firstFiberClass +
        (-2 : ℤ) • (schemePicardPullbackHom (projectiveContactProjection (k := k) N)).toAdditive
          secondFiberClass +
        ∑ j : Fin N, totalExceptionalClass (k := k) N j := by
  rw [originalCanonicalClass_tower, originalCanonicalClass_zero, map_add, map_zsmul, map_zsmul]

/-- The translated initial scheme has the same original product structure morphism. -/
theorem translatedCanonicalClass_zero (p : ℕ) (a : k) :
    translatedCanonicalClass p a 0 =
      (-2 : ℤ) • firstFiberClass + (-2 : ℤ) • secondFiberClass :=
  canonicalPicard_eq_fiberClasses

/-- The actual translated all-depth canonical class uses its original projection and
its original total exceptional classes. -/
theorem translatedCanonicalClass_eq_fibers_exceptionals (p : ℕ) (a : k) (N : ℕ) :
    translatedCanonicalClass p a N =
      (-2 : ℤ) • (schemePicardPullbackHom (selectedProjection p a N)).toAdditive
          firstFiberClass +
        (-2 : ℤ) • (schemePicardPullbackHom (selectedProjection p a N)).toAdditive
          secondFiberClass +
        ∑ j : Fin N, translatedTotalExceptionalClass p a N j := by
  rw [translatedCanonicalClass_tower, translatedCanonicalClass_zero,
    map_add, map_zsmul, map_zsmul]

end KltDP.Examples.FrobeniusInitialCanonicalTower
