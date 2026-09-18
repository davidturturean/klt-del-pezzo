import KltDP.Examples.FrobeniusContactTowerCanonicalIteration
import KltDP.Examples.FrobeniusOldExceptionalAdjacentRows
import KltDP.Examples.FrobeniusStageCanonicalCartier

/-!
# Canonical degree zero on the original older exceptional curves

Every older exceptional curve contracts to the initial point, so its degree
against a pulled initial line is zero. Its degrees against the total exceptional
classes are minus one at its own birth, one at the following birth, and zero
elsewhere. The actual canonical tower formula therefore has degree zero on it.
The projectivity hypotheses are exactly those retained by the existing chain rows.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Examples.FrobeniusOldExceptionalCanonical

open KltDP.Geometry KltDP.Geometry.SmoothSurfaceKaehlerAtlas
open SmoothCanonicalCartierRepresentative SmoothCanonicalCartierPicard
open FrobeniusGlobalBlowupStages FrobeniusGlobalBlowupSmooth
open FrobeniusStageSurface FrobeniusStrictTransformPrimeCurves
open FrobeniusStrictTransformPairing FrobeniusStrictTransformClassesTower
open FrobeniusExceptionalFinalConfiguration FrobeniusOldExceptionalSelfRow
open FrobeniusOldExceptionalLaterRows FrobeniusOldExceptionalAdjacentRows
open FrobeniusContactTowerCanonicalIteration FrobeniusStageCanonicalCartier

variable {k : Type u} [Field k] [IsAlgClosed k]

local instance canonicalProductIntegral :
    IsIntegral (projectiveProductInitial (k := k)).carrier :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

variable (n : ℕ)
  (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)
  (j : ℕ) (h : j + 2 ≤ n + 1)

/-- Any actual class pulled from the initial product has degree zero on the older curve. -/
theorem oldExceptionalPairing_pullback_initial
    (q : Additive (projectiveContactStage (k := k) 0).Pic) :
    oldExceptionalPairing n hproj j h
      ((schemePicardPullbackHom (projectiveContactProjection (k := k) (n + 1))).toAdditive q) =
      0 := by
  have hp := oldExceptionalPairing_pullback_comp n hproj j h
    (between (projectiveProductInitial (k := k)) (Nat.zero_le j)) q
  rw [between_comp, between_zero] at hp
  exact hp

variable (hstages : ∀ i : ℕ, 2 ≤ i → i ≤ n →
  IsProjectiveOverField ((projectiveProductInitial (k := k)).stage i).structureMap)

include hstages

/-- The minus-one and plus-one entries cancel in the total exceptional sum. -/
theorem oldExceptionalPairing_sum_totalExceptional :
    oldExceptionalPairing n hproj j h
      (∑ i : Fin (n + 1), totalExceptionalClass (k := k) (n + 1) i) = 0 := by
  classical
  let a : Fin (n + 1) := ⟨j, by omega⟩
  let b : Fin (n + 1) := ⟨j + 1, by omega⟩
  have hab : a ≠ b := by
    intro hab
    have hv := congrArg Fin.val hab
    change j = j + 1 at hv
    omega
  have hself := oldExceptionalPairing_totalExceptional_self n hproj j h
    (stage_projective_of_le n hstages (j + 1) (by omega) (by omega))
  have hsucc := oldExceptionalPairing_totalExceptional_succ n hproj j h hstages
  have hrow (i : Fin (n + 1)) :
      oldExceptionalPairing n hproj j h (totalExceptionalClass (n + 1) i) =
        (if i = a then -1 else 0) + (if i = b then 1 else 0) := by
    by_cases ha : i = a
    · subst i
      simpa only [a, b, if_pos rfl, if_neg hab, add_zero] using hself
    by_cases hb : i = b
    · subst i
      simpa only [a, b, if_neg (Ne.symm hab), if_pos rfl, zero_add] using hsucc
    have hia : i.val ≠ j := by
      intro hi
      exact ha (Fin.ext hi)
    have hib : i.val ≠ j + 1 := by
      intro hi
      exact hb (Fin.ext hi)
    have hz : oldExceptionalPairing n hproj j h (totalExceptionalClass (n + 1) i) = 0 := by
      by_cases hi : i.val < j
      · exact oldExceptionalPairing_totalExceptional_of_lt n hproj j h i hi
      · exact oldExceptionalPairing_totalExceptional_of_ge n hproj j h i (by omega)
    simpa only [if_neg ha, if_neg hb, zero_add] using hz
  rw [map_sum]
  simp_rw [hrow]
  rw [Finset.sum_add_distrib]
  simp

/-- The actual top-differential canonical class has degree zero on each older curve. -/
theorem oldExceptionalPairing_canonical :
    oldExceptionalPairing n hproj j h (originalCanonicalClass (k := k) (n + 1)) = 0 := by
  rw [originalCanonicalClass_tower, map_add,
    oldExceptionalPairing_pullback_initial,
    oldExceptionalPairing_sum_totalExceptional n hproj j h hstages, add_zero]

/-- The independently chosen canonical Cartier divisor has the same zero intersection. -/
theorem oldExceptional_canonicalIntersection :
    (oldExceptionalPrimeCurve n hproj j h).intersectionNumber
      (canonicalCartier (k := k) (n + 1)) = 0 := by
  rw [← (oldExceptionalPrimeCurve n hproj j h).picardRestrictionDegreeHom_cartierPicardHom]
  change oldExceptionalPairing n hproj j h
    (cartierPicardHom (projectiveContactStage (k := k) (n + 1))
      (cartierRepresentative ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)) = 0
  rw [cartierPicardHom_representative]
  exact oldExceptionalPairing_canonical n hproj j h hstages

end KltDP.Examples.FrobeniusOldExceptionalCanonical
