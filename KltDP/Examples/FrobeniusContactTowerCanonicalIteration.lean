import KltDP.Examples.FrobeniusContactTowerCanonicalFormula
import KltDP.Examples.FrobeniusTowerTransportClasses

/-!
# The iterated canonical class of the two original contact towers

The canonical classes below are the classes of the actual atlas canonical
sheaves. The proved one-step differential formula identifies their successor
classes. The original tower projections and the already defined total
exceptional classes then give the iterated formula by finite-sum induction.
No canonical class is defined by the resulting formula, and no projectivity,
intersection number, or canonical-compatibility premise is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusContactTowerCanonicalIteration

open KltDP.Geometry KltDP.Geometry.SmoothSurfaceKaehlerAtlas
open FrobeniusGlobalBlowupStages FrobeniusGlobalBlowupSmooth FrobeniusTranslatedCharts
open FrobeniusContactTowerSelectedPoint FrobeniusContactTowerCanonicalFormula
open FrobeniusGlobalBlowupCanonicalExceptionalCartier
open FrobeniusStrictTransformProductKernel FrobeniusStrictTransformPicardStep
open FrobeniusStrictTransformClassesTower FrobeniusExceptionalFinalConfiguration
open FrobeniusTowerTransportClasses

variable {k : Type u} [Field k]

local instance iterationProductIntegral :
    IsIntegral (projectiveProductInitial (k := k)).carrier :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

local instance iterationTranslatedIntegral (p : ℕ) (a : k) :
    IsIntegral (translatedInitial p a).carrier :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

/-- The actual canonical line class on the original whole stage. -/
abbrev originalCanonicalClass (N : ℕ) :
    Additive (projectiveContactStage (k := k) N).Pic :=
  Additive.ofMul (canonicalSheafOfSmoothSurface
    ((projectiveProductInitial (k := k)).stage N).structureMap).toPic

/-- The actual canonical line class on the original translated whole stage. -/
abbrev translatedCanonicalClass (p : ℕ) (a : k) (N : ℕ) :
    Additive (selectedStage p a N).Pic :=
  Additive.ofMul (canonicalSheafOfSmoothSurface
    ((translatedInitial p a).stage N).structureMap).toPic

/-- The original composite projection pulls a class back one actual step at a time. -/
private theorem toInitialPicardPullback_succ (A : PlaneChartedScheme k) (N : ℕ)
    (c : Additive A.carrier.Pic) :
    (schemePicardPullbackHom (A.toInitial (N + 1))).toAdditive c =
      (schemePicardPullbackHom (A.stepProjection N)).toAdditive
        ((schemePicardPullbackHom (A.toInitial N)).toAdditive c) := by
  rw [PlaneChartedScheme.toInitial_succ, schemePicardPullbackHom_comp]
  rfl

/-- The proved original canonical formula uses the same accepted exceptional class. -/
theorem originalCanonicalClass_succ (N : ℕ) :
    originalCanonicalClass (k := k) (N + 1) =
      (schemePicardPullbackHom ((projectiveProductInitial (k := k)).stepProjection N)).toAdditive
        (originalCanonicalClass N) + stepExceptionalPicardClass N := by
  rw [stepExceptionalPicardClass, ← sub_eq_add_neg]
  exact FrobeniusGlobalBlowupCanonicalPicard.canonicalSheafPicard_formula
    ((projectiveProductInitial (k := k)).stage N)

/-- The actual original canonical class is the pulled initial class plus the accepted total
exceptional classes of all original blowup steps. -/
theorem originalCanonicalClass_tower (N : ℕ) :
    originalCanonicalClass (k := k) N =
      (schemePicardPullbackHom (projectiveContactProjection (k := k) N)).toAdditive
        (originalCanonicalClass 0) +
          ∑ j : Fin N, totalExceptionalClass (k := k) N j := by
  induction N with
  | zero =>
    change originalCanonicalClass (k := k) 0 =
      (schemePicardPullbackHom (𝟙 (projectiveContactStage (k := k) 0))).toAdditive
        (originalCanonicalClass 0) + ∑ j : Fin 0, totalExceptionalClass (k := k) 0 j
    rw [schemePicardPullbackHom_id, Fin.sum_univ_zero, add_zero]
    rfl
  | succ N ih =>
    rw [originalCanonicalClass_succ, ih, map_add, map_sum,
      Fin.sum_univ_castSucc, totalExceptionalClass_last]
    simp only [totalExceptionalClass_castSucc]
    have h :
        (schemePicardPullbackHom (projectiveContactProjection (k := k) (N + 1))).toAdditive
            (originalCanonicalClass 0) =
          (schemePicardPullbackHom
            ((projectiveProductInitial (k := k)).stepProjection N)).toAdditive
            ((schemePicardPullbackHom (projectiveContactProjection (k := k) N)).toAdditive
              (originalCanonicalClass 0)) :=
      toInitialPicardPullback_succ projectiveProductInitial N (originalCanonicalClass 0)
    rw [← h, add_assoc]

/-- The same original translated canonical formula uses the accepted translated exceptional class. -/
theorem translatedCanonicalClass_succ (p : ℕ) (a : k) (N : ℕ) :
    translatedCanonicalClass p a (N + 1) =
      (schemePicardPullbackHom ((translatedInitial p a).stepProjection N)).toAdditive
        (translatedCanonicalClass p a N) + translatedStepExceptionalClass p a N := by
  rw [translatedStepExceptionalClass, ← sub_eq_add_neg]
  exact FrobeniusGlobalBlowupCanonicalPicard.canonicalSheafPicard_formula
    ((translatedInitial p a).stage N)

/-- The earlier accepted translated total exceptional classes pull back along the original step. -/
theorem translatedTotalExceptionalClass_castSucc (p : ℕ) (a : k) (N : ℕ) (j : Fin N) :
    translatedTotalExceptionalClass p a (N + 1) j.castSucc =
      (schemePicardPullbackHom ((translatedInitial p a).stepProjection N)).toAdditive
        (translatedTotalExceptionalClass p a N j) := by
  have h : between (translatedInitial p a) j.castSucc.isLt =
      (translatedInitial p a).stepProjection N ≫ between (translatedInitial p a) j.isLt :=
    between_succ (translatedInitial p a) j.isLt
  unfold translatedTotalExceptionalClass
  rw [h, schemePicardPullbackHom_comp]
  rfl

/-- The actual translated canonical class is the pulled initial class plus the same translated
whole tower's already defined total exceptional classes. -/
theorem translatedCanonicalClass_tower (p : ℕ) (a : k) (N : ℕ) :
    translatedCanonicalClass p a N =
      (schemePicardPullbackHom (selectedProjection p a N)).toAdditive
        (translatedCanonicalClass p a 0) +
          ∑ j : Fin N, translatedTotalExceptionalClass p a N j := by
  induction N with
  | zero =>
    change translatedCanonicalClass p a 0 =
      (schemePicardPullbackHom (𝟙 (selectedStage p a 0))).toAdditive
        (translatedCanonicalClass p a 0) +
          ∑ j : Fin 0, translatedTotalExceptionalClass p a 0 j
    rw [schemePicardPullbackHom_id, Fin.sum_univ_zero, add_zero]
    rfl
  | succ N ih =>
    rw [translatedCanonicalClass_succ, ih, map_add, map_sum,
      Fin.sum_univ_castSucc, translatedTotalExceptionalClass_last]
    simp only [translatedTotalExceptionalClass_castSucc]
    have h :
        (schemePicardPullbackHom (selectedProjection p a (N + 1))).toAdditive
            (translatedCanonicalClass p a 0) =
          (schemePicardPullbackHom ((translatedInitial p a).stepProjection N)).toAdditive
            ((schemePicardPullbackHom (selectedProjection p a N)).toAdditive
              (translatedCanonicalClass p a 0)) :=
      toInitialPicardPullback_succ (translatedInitial p a) N (translatedCanonicalClass p a 0)
    rw [← h, add_assoc]

end KltDP.Examples.FrobeniusContactTowerCanonicalIteration
