import KltDP.Geometry.PrimeCurveClassPairing
import KltDP.Examples.FrobeniusStrictTransformPairing
import KltDP.Examples.FrobeniusStageExceptionalPairing
import KltDP.Examples.FrobeniusFiberZeroInvertible

/-!
# Actual strict-curve classes in the symmetric pairing of a contact stage

The strict graph and fibre have the literal kernel lines used to define their accepted Picard
classes. The generic Cartier/kernel comparison therefore identifies their restriction degrees
with the symmetric surface pairing against those classes. The accepted newest-exceptional rows
then give the transposed rows `B · P = F̃ · P = 1`.

All objects are on one origin contact tower. Only algebraic closure and projectivity of the
indicated stage are retained as geometric hypotheses; initial fibre invertibility is discharged
by the accepted proof.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusContactClassPairing

open KltDP.Geometry KltDP.Geometry.PrimeCurveClassPairing
open KltDP.Geometry.PrimeCurveTransversalPoint
open FrobeniusGlobalBlowupStages FrobeniusGlobalStrictTransform FrobeniusStageSurface
open FrobeniusStrictTransformPrimeCurves FrobeniusStrictTransformPairing
open FrobeniusStrictTransformInvertible FrobeniusStrictTransformPicardStep
open FrobeniusFiberClosure FrobeniusFiberPicard FrobeniusFiberZeroInvertible
open FrobeniusStageExceptionalPullback FrobeniusStageExceptionalSelfIntersection
open FrobeniusStageExceptionalPairing

variable {k : Type u} [Field k] [IsAlgClosed k]

local instance contactPairingInitialIntegral : IsIntegral (projectiveProductInitial (k := k)).carrier :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

variable (n : ℕ)
  (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)

/-- The accepted symmetric pairing on the actual contact stage, in additive notation. -/
abbrev contactPairing (p q : Additive (projectiveContactStage (k := k) (n + 1)).Pic) : ℤ :=
  pairing (stageSurface (n + 1) hproj) (stageRegular n hproj) p q

/-- The actual strict graph's prime Cartier class is its existing inverse kernel class. -/
theorem graphStrictCartier_class (m : ℕ) :
    cartierPicardHom (projectiveContactStage (k := k) (n + 1))
      ((stageSurface (n + 1) hproj).primeCurveCartier (stageRegular n hproj)
        (graphStrictPrimeCurve n hproj m)) = strictCurvePicardClass (n + 1) m :=
  cartierPicardHom_primeCurveCartier_of_kernel (stageRegular n hproj)
    (graphStrictPrimeCurve n hproj m) (strictTransformι (n + 1) (m + (n + 1))) rfl
    (strictKernelLine (n + 1) m) rfl

/-- The actual strict fibre's prime Cartier class is its existing inverse kernel class. -/
theorem fiberStrictCartier_class :
    cartierPicardHom (projectiveContactStage (k := k) (n + 1))
      ((stageSurface (n + 1) hproj).primeCurveCartier (stageRegular n hproj)
        (fiberStrictPrimeCurve n hproj)) =
      fiberPicardClass (fiberKernel_zero_isInvertible (k := k)) (n + 1) :=
  cartierPicardHom_primeCurveCartier_of_kernel (stageRegular n hproj)
    (fiberStrictPrimeCurve n hproj)
    (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1)) rfl
    (fiberKernelLine fiberKernel_zero_isInvertible (n + 1)) rfl

/-- Restriction degree along the strict graph is pairing with its actual class. -/
theorem graphStrictPairing_eq_contactPairing (m : ℕ)
    (q : Additive (projectiveContactStage (k := k) (n + 1)).Pic) :
    graphStrictPairing n hproj m q =
      contactPairing n hproj (strictCurvePicardClass (n + 1) m) q :=
  (pairing_kernelLine_left (stageSurface (n + 1) hproj) (stageRegular n hproj)
    (graphStrictPrimeCurve n hproj m) (strictTransformι (n + 1) (m + (n + 1))) rfl
    (strictKernelLine (n + 1) m) rfl q).symm

/-- Restriction degree along the strict fibre is pairing with its actual class. -/
theorem fiberStrictPairing_eq_contactPairing
    (q : Additive (projectiveContactStage (k := k) (n + 1)).Pic) :
    fiberStrictPairing n hproj q =
      contactPairing n hproj
        (fiberPicardClass (fiberKernel_zero_isInvertible (k := k)) (n + 1)) q :=
  (pairing_kernelLine_left (stageSurface (n + 1) hproj) (stageRegular n hproj)
    (fiberStrictPrimeCurve n hproj)
    (fiberClosureInclusion (projectiveProductInitial (k := k)) (n + 1)) rfl
    (fiberKernelLine fiberKernel_zero_isInvertible (n + 1)) rfl q).symm

/-- Pairing with the newest exceptional class computes its restriction degree. -/
theorem contactPairing_exceptional_right
    (q : Additive (projectiveContactStage (k := k) (n + 1)).Pic) :
    contactPairing n hproj q (stepExceptionalPicardClass n) = exceptionalPairing n hproj q := by
  have h := pairing_primeCurve_right (stageSurface (n + 1) hproj) (stageRegular n hproj)
    (exceptionalPrimeCurve n hproj) q
  change contactPairing n hproj q
    (cartierPicardHom (projectiveContactStage (k := k) (n + 1)) (exceptionalCartier n hproj)) =
      exceptionalPairing n hproj q at h
  rw [cartierPicardHom_exceptionalCartier] at h
  exact h

/-- The strict graph meets the newest exceptional class with degree one. -/
theorem graphStrictPairing_stepExceptional_eq_one (m : ℕ) :
    graphStrictPairing n hproj m (stepExceptionalPicardClass n) = 1 := by
  rw [graphStrictPairing_eq_contactPairing, contactPairing_exceptional_right]
  exact exceptionalPairing_strictCurve n hproj m

/-- The strict fibre meets the newest exceptional class with degree one. -/
theorem fiberStrictPairing_stepExceptional_eq_one :
    fiberStrictPairing n hproj (stepExceptionalPicardClass n) = 1 := by
  rw [fiberStrictPairing_eq_contactPairing, contactPairing_exceptional_right]
  exact exceptionalPairing_fiberStrict n hproj fiberKernel_zero_isInvertible

end KltDP.Examples.FrobeniusContactClassPairing
