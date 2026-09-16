import KltDP.Examples.FrobeniusTowerTransportClasses
import KltDP.Examples.FrobeniusFiberZeroClass

/-!
# The fibre relation of the translated contact towers at the Picard level

The Picard-level form of the Cartier fibre identity
`π^*(y = 0) = F̃ + Σ_{j<N} (j+1)·C_j + (N+1)·P` (`f29_tower_fiber_picard_relation_b`), the class `b` of the stage-`0` fibre and the `p`-fold form
of the `B` relation are transported from the origin tower to the translated tower over `(a, a^p)`,
along the Picard isomorphisms `schemePicardPullbackHom (stageTranslationIso p a n).inv` of
`FrobeniusTowerTransportClasses`.  The classes are those of the translated tower's own curves;
the fibre `y = 1 + a^p` plays the role of `y = 1` (`translatedSecondFiberClass`).

`strictTransformClasses_translated_tower_full` collects, for the translated tower, every clause of
the class-table group `ClassTable` of the F29 bundle together with the Picard fibre relation.  The
Cartier-divisor level of the fibre identity on the translated tower is **not** treated here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KltDP.Examples.FrobeniusTowerTransportPicardRelation

open KltDP.Geometry KltDP.Geometry.SchemeKernelIdealIsoTransport
open FrobeniusGlobalBlowupStages FrobeniusContactTowerSelectedPoint FrobeniusTowerTransport
  FrobeniusExceptionalFinalConfiguration FrobeniusTowerTransportClasses
  FrobeniusStrictTransformPicardStep
  FrobeniusStrictTransformClassesTower FrobeniusOldExceptionalLaterStages
  FrobeniusGraphPicardClassTotalTransform FrobeniusStrictTransformClassesFull
  FrobeniusFiberPicard FrobeniusFiberZeroInvertible FrobeniusFiberZeroClass
  FrobeniusGraphPicardClassFiberClasses FrobeniusProjectivePoints FrobeniusTranslatedCharts
  ProjectiveProductTranslation

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k]

/-- `b` on the plane of the translated tower: the class of the fibre `y = 1 + a^p`
(ideal-sheaf sign convention). -/
def translatedSecondFiberClass (p : ℕ) (a : k) : Additive (projectiveProduct k).Pic :=
  -Additive.ofMul (translatedHorizontalIdealLine p a).toPic

theorem translatedSecondFiberClass_eq (p : ℕ) (a : k) :
    translatedSecondFiberClass p a =
      (schemePicardPullbackHom (stageTranslationIso p a 0).inv).toAdditive secondFiberClass := by
  unfold translatedSecondFiberClass secondFiberClass
  rw [map_neg, translatedHorizontalIdealLine_toPic]
  rfl

/-- The strict fibre of stage `0` of the translated tower has the class `b`. -/
theorem translatedFiberClass_zero (p : ℕ) (a : k) :
    translatedFiberClass p a 0 = translatedSecondFiberClass p a := by
  rw [translatedFiberClass_eq, translatedSecondFiberClass_eq, fiberClass,
    fiberPicardClass_zero_eq_secondFiberClass]

/-- `F_N = π_N^* b − Σ_{j<N} E_j^{(N)}` on stage `N` of the translated tower. -/
theorem translatedFiberClass_tower' (p : ℕ) (a : k) (N : ℕ) :
    translatedFiberClass p a N =
      (schemePicardPullbackHom (between (translatedInitial p a) (Nat.zero_le N))).toAdditive
        (translatedSecondFiberClass p a) -
        ∑ j : Fin N, translatedTotalExceptionalClass p a N j := by
  rw [translatedFiberClass_tower, translatedFiberZeroTotalClass, translatedFiberClass_zero]

/-- The `p`-fold form of the `B` relation on the translated tower. -/
theorem translatedStrictCurveClass_pFold (p : ℕ) (a : k) (q N : ℕ) (h : N ≤ q) :
    translatedStrictCurveClass p a N (q - N) =
      q • translatedFirstFiberTotalClass p a N + translatedSecondFiberTotalClass p a N -
        ∑ j : Fin N, translatedTotalExceptionalClass p a N j := by
  rw [translatedStrictCurveClass_tower, Nat.sub_add_cancel h]

/-- **The Picard-level fibre identity on stage `N+1` of the translated tower**:
`π^* b = F̃ + Σ_{j<N} (j+1)·C_j + (N+1)·P`. -/
theorem translated_fiber_picard_relation (p : ℕ) (a : k) (N : ℕ) :
    (schemePicardPullbackHom (between (translatedInitial p a) (Nat.zero_le (N + 1)))).toAdditive
        (translatedSecondFiberClass p a) =
      translatedFiberClass p a (N + 1) +
        ∑ j : Fin N,
          (j.val + 1) • translatedOldExceptionalStrictClass p a (N + 1) j.val (by omega) +
          (N + 1) • translatedTotalExceptionalClass p a (N + 1) (Fin.last N) := by
  rw [translatedSecondFiberClass_eq, translatedFiberClass_eq, translatedTotalExceptionalClass_eq,
    fiberClass]
  simp_rw [translatedOldExceptionalStrictClass_eq, ← map_nsmul]
  rw [← map_sum, ← map_add, ← map_add, ← picardPullback_inv_square_toAdditive _ _ _ _
    (stageTranslationIso_hom_between p a (Nat.zero_le (N + 1))),
    f29_tower_fiber_picard_relation_b k N]

/-- **The class table of the translated contact tower with the Picard fibre relation**: every
clause of the F29 bundle's class-table group, on the translated tower over `(a, a^p)`, with the
classes of the translated tower's own curves (`q` is the parameter of the `p`-fold clause). -/
theorem strictTransformClasses_translated_tower_full (p : ℕ) (a : k) (q : ℕ) :
    (∀ N m : ℕ, translatedStrictCurveClass p a N m =
      (m + N) • translatedFirstFiberTotalClass p a N + translatedSecondFiberTotalClass p a N -
        ∑ j : Fin N, translatedTotalExceptionalClass p a N j) ∧
    (∀ N : ℕ, N ≤ q → translatedStrictCurveClass p a N (q - N) =
      q • translatedFirstFiberTotalClass p a N + translatedSecondFiberTotalClass p a N -
        ∑ j : Fin N, translatedTotalExceptionalClass p a N j) ∧
    (∀ (N j : ℕ) (h : j + 1 + 1 ≤ N),
      translatedOldExceptionalStrictClass p a N j h =
        translatedTotalExceptionalClass p a N ⟨j, by omega⟩ -
          translatedTotalExceptionalClass p a N ⟨j + 1, by omega⟩) ∧
    (∀ N : ℕ, translatedFiberClass p a N =
      (schemePicardPullbackHom (between (translatedInitial p a) (Nat.zero_le N))).toAdditive
        (translatedSecondFiberClass p a) -
        ∑ j : Fin N, translatedTotalExceptionalClass p a N j) ∧
    translatedFiberClass p a 0 = translatedSecondFiberClass p a ∧
    (∀ n : ℕ, translatedFiberClass p a (n + 1) =
      (schemePicardPullbackHom ((translatedInitial p a).stepProjection n)).toAdditive
        (translatedFiberClass p a n) - translatedStepExceptionalClass p a n) ∧
    (∀ N : ℕ, translatedTotalExceptionalClass p a (N + 1) (Fin.last N) =
      translatedStepExceptionalClass p a N) ∧
    (∀ N : ℕ,
      (schemePicardPullbackHom (between (translatedInitial p a) (Nat.zero_le (N + 1)))).toAdditive
        (translatedSecondFiberClass p a) =
      translatedFiberClass p a (N + 1) +
        ∑ j : Fin N,
          (j.val + 1) • translatedOldExceptionalStrictClass p a (N + 1) j.val (by omega) +
          (N + 1) • translatedTotalExceptionalClass p a (N + 1) (Fin.last N)) :=
  ⟨translatedStrictCurveClass_tower p a, fun N h => translatedStrictCurveClass_pFold p a q N h,
    translatedOldExceptionalStrictClasses_tower p a, translatedFiberClass_tower' p a,
    translatedFiberClass_zero p a, translatedFiberClass_succ p a,
    translatedTotalExceptionalClass_last p a, translated_fiber_picard_relation p a⟩

/-- The bundle has exactly one universe parameter. -/
theorem strictTransformClasses_translated_tower_full_universe_check (k : Type u) [Field k]
    (p : ℕ) (a : k) (q : ℕ) : True := by
  have _ := strictTransformClasses_translated_tower_full.{u} p a q
  trivial

end KltDP.Examples.FrobeniusTowerTransportPicardRelation
