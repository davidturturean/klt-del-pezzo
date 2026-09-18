import KltDP.Examples.FrobeniusStageOnePicardSplitting
import KltDP.Examples.FrobeniusStageExceptionalSelfIntersectionValue
import KltDP.Examples.FrobeniusProjectivityProved

/-!
# Picard splitting at every original single-centre contact stage

The original stage `n + 1` is the accepted glued point blowup of stage `n`.
The accepted extension across a regular closed point gives the retraction
of the actual step pullback. The actual newest exceptional prime curve has
self-intersection `-1`, so the accepted exceptional-kernel splitting gives
`Pic (stage (n + 1)) ≃* Pic (stage n) × Multiplicative ℤ`.

This is the arbitrary-stage adapter of `FrobeniusStageOnePicardSplitting`.
Projectivity is supplied by `FrobeniusProjectivityProved.originalStageProjective`;
its existing literature dependency is retained. There is no projectivity,
Picard generation, regularity, or point-blowup literal premise in this module.
No multi-centre decomposition or choice of ruling coordinates is asserted here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusStagePicardSplitting

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open KltDP.Geometry.PrimeCurveComplementKernel
open FrobeniusBlowupChartIteration FrobeniusGlobalBlowupStages FrobeniusStageSurface
open FrobeniusProjectivityProved FrobeniusStageExceptionalSelfIntersection

variable {k : Type u} [Field k] [IsAlgClosed k]

local instance originMaximal : (originPoint (k := k)).asIdeal.IsMaximal :=
  centerIdeal_isMaximal

/-- The original stage, with its proved normal projective surface structure. -/
abbrev surface (n : ℕ) : NormalProjectiveSurface k :=
  stageSurface n (originalStageProjective k n)

/-- The original plane chart used to blow up stage `n`. -/
abbrev chart (n : ℕ) : plane k ⟶ (surface (k := k) n).toScheme :=
  ((projectiveProductInitial (k := k)).stage n).chart

local instance surfaceStalksUFD (n : ℕ) :
    ∀ y : (surface (k := k) n).toScheme,
      UniqueFactorizationMonoid ((surface (k := k) n).stalk y) :=
  (surface (k := k) n).stalks_uniqueFactorizationMonoid_of_regular
    (stageSurface_regularPoints n (originalStageProjective k n))

/-- The actual newest exceptional prime curve, on the original stage `n + 1`. -/
abbrev exceptionalCurve (n : ℕ) : (surface (k := k) (n + 1)).PrimeCurve :=
  exceptionalPrimeCurve n (originalStageProjective k (n + 1))

/-- Its actual Cartier/Picard class, using the proved factorial stalks. -/
abbrev exceptionalClass (n : ℕ) : (projectiveContactStage (k := k) (n + 1)).Pic :=
  primeCurveClass (exceptionalCurve (k := k) n)

theorem coe_exceptionalCurve (n : ℕ) :
    (exceptionalCurve (k := k) n : Set (surface (k := k) (n + 1)).toScheme) =
      ((projectiveProductInitial (k := k)).stepProjection n).base ⁻¹'
        {(chart (k := k) n).base (originPoint (k := k))} :=
  PointBlowupGluing.range_globalCenterFiberι (chart (k := k) n) (originPoint (k := k))
    ((projectiveProductInitial (k := k)).stage n).center_closed

theorem complementOpen_exceptionalCurve (n : ℕ) :
    complementOpen (exceptionalCurve (k := k) n) =
      PointBlowupGluing.exceptionalComplementOpen (chart (k := k) n) (originPoint (k := k))
        ((projectiveProductInitial (k := k)).stage n).center_closed := by
  apply TopologicalSpace.Opens.ext
  show (exceptionalCurve (k := k) n : Set (surface (k := k) (n + 1)).toScheme)ᶜ = _
  rw [coe_exceptionalCurve]
  rfl

/-- The original puncture restriction is bijective, by regularity of the base stage. -/
theorem restrictPuncture_bijective (n : ℕ) :
    Function.Bijective (PointBlowupPicard.restrictPuncture (chart (k := k) n)
      (originPoint (k := k)) ((projectiveProductInitial (k := k)).stage n).center_closed) :=
  CartierExtension.restrictPuncture_bijective (X := surface (k := k) n)
    (chart (k := k) n) (originPoint (k := k))
    ((projectiveProductInitial (k := k)).stage n).center_closed

/-- Restrict, identify the actual punctures, and extend across the original centre. -/
def retraction (n : ℕ) :
    (projectiveContactStage (k := k) (n + 1)).Pic →*
      (projectiveContactStage (k := k) n).Pic :=
  PointBlowupPicard.retraction (chart (k := k) n) (originPoint (k := k))
    ((projectiveProductInitial (k := k)).stage n).center_closed
    (restrictPuncture_bijective (k := k) n)

theorem retraction_pullback (n : ℕ) (c : (projectiveContactStage (k := k) n).Pic) :
    retraction n
      (schemePicardPullbackHom ((projectiveProductInitial (k := k)).stepProjection n) c) = c :=
  PointBlowupPicard.retraction_pullback (chart (k := k) n) (originPoint (k := k))
    ((projectiveProductInitial (k := k)).stage n).center_closed
    (restrictPuncture_bijective (k := k) n) c

theorem ker_retraction (n : ℕ) :
    (retraction (k := k) n).ker =
      (schemePicardPullbackHom (complementOpen (exceptionalCurve (k := k) n)).ι).ker := by
  rw [retraction, PointBlowupPicard.ker_retraction]
  show (schemePicardPullbackHom (PointBlowupGluing.exceptionalComplementOpen
    (chart (k := k) n) (originPoint (k := k))
    ((projectiveProductInitial (k := k)).stage n).center_closed).ι).ker = _
  rw [complementOpen_exceptionalCurve]

private theorem classInfiniteOrderOfSelfIntersection (S : NormalProjectiveSurface k)
    (hreg : ∀ x : S.Point, RegularPoint S.toScheme x) (E : S.PrimeCurve)
    (hEE : E.selfIntersectionNumber hreg = -1) :
    haveI := S.stalks_uniqueFactorizationMonoid_of_regular hreg
    InfiniteOrder (primeCurveClass E) := by
  haveI := S.stalks_uniqueFactorizationMonoid_of_regular hreg
  exact infiniteOrder_of_intersectionNumber_neg_one E hEE

/-- Infinite order is derived from the proved self-intersection of the actual curve. -/
theorem exceptionalClass_infiniteOrder (n : ℕ) :
    InfiniteOrder (X := surface (k := k) (n + 1)) (exceptionalClass (k := k) n) :=
  classInfiniteOrderOfSelfIntersection (surface (k := k) (n + 1))
    (stageRegular n (originalStageProjective k (n + 1))) (exceptionalCurve (k := k) n)
    (KltDP.Examples.f09_exceptional_self_intersection k n
      (originalStageProjective k (n + 1)))

/-- The actual one-step Picard decomposition, with the newest exceptional class as second factor. -/
def picardSplitting (n : ℕ) :
    (projectiveContactStage (k := k) (n + 1)).Pic ≃*
      (projectiveContactStage (k := k) n).Pic × Multiplicative ℤ :=
  picardEquivProdInt (exceptionalCurve (k := k) n)
    (genericPoint_mem_complementOpen_iff (exceptionalCurve (k := k) n))
    (exceptionalClass_infiniteOrder (k := k) n)
    (schemePicardPullbackHom ((projectiveProductInitial (k := k)).stepProjection n))
    (retraction (k := k) n) (retraction_pullback (k := k) n) (ker_retraction (k := k) n)

/-- Each original single-centre step adds one integral Picard factor. -/
theorem stagePicardSplitting (n : ℕ) :
    Nonempty ((projectiveContactStage (k := k) (n + 1)).Pic ≃*
      (projectiveContactStage (k := k) n).Pic × Multiplicative ℤ) :=
  ⟨picardSplitting (k := k) n⟩

end KltDP.Examples.FrobeniusStagePicardSplitting
