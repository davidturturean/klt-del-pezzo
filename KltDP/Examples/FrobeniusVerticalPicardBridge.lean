import KltDP.Examples.FrobeniusStageVerticalDivisor
import KltDP.Examples.ProjectiveProductFiberClassInvariance
import KltDP.Examples.FrobeniusGraphPicardClassTotalTransform
import KltDP.Geometry.CartierPullbackComparison

/-!
# The actual vertical Cartier divisor represents the first fibre class

The glued divisor of `x = 0` is the first ruling at infinity plus the principal divisor of `x`.
Its Picard class is therefore the accepted `firstFiberClass`. The translation carrying `x = 0`
to `x = c` preserves that class: this follows from the actual kernel-line transport square and
the accepted equality of the classes of all vertical fibres. Cartier pullback compatibility then
identifies `verticalFiberDivisorAt c`, and its pullback to every contact stage, with the first
fibre class used in the manuscript's intersection table.

The argument uses actual Cartier divisors and actual ideal sheaves. It needs no characteristic,
algebraic-closure, stage-projectivity, or nonzero-coordinate hypothesis. Computing intersection
numbers of strict transforms is a separate result.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusVerticalPicardBridge

open KltDP.Geometry KltDP.Geometry.ProjectiveLineTranslation
open KltDP.Geometry.CartierPullbackComparison
open KltDP.Geometry.SchemeKernelIdealIsoTransport
open FrobeniusProjectivePoints FrobeniusUnaffectedFibers
open FrobeniusGraphPicardClassRulingCoordinates FrobeniusGraphPicardClassRulingDivisors
open FrobeniusGraphPicardClassFiberClasses FrobeniusGraphPicardClassTotalTransform
open FrobeniusVerticalFiberClass FrobeniusVerticalFiberTranslated
open ProjectiveProductFiberClassInvariance
open FrobeniusGlobalBlowupStages FrobeniusStageVerticalDivisor

variable {k : Type u} [Field k]

local instance verticalPicardProductIntegral : IsIntegral (projectiveProduct k) :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

/-- The fibre `x = 0` differs from the first ruling at infinity by `div(x)`. -/
theorem verticalZeroDivisor_eq_ruling_add_principal :
    verticalZeroDivisor (k := k) =
      rulingInfinityDivisor 0 +
        principalCartierDivisorHom (projectiveProduct k)
          (Additive.ofMul (rulingCoordinateUnit 0)) := by
  apply cartierDivisor_eq_of_restrict_eq (projectiveProduct k)
    (fun i : ULift.{u} (Fin 2) => rulingOpen 0 i.down) verticalZero_cover
  rintro ⟨i⟩
  change (cartierDivisorSheaf (projectiveProduct k)).val.map
      (homOfLE (show rulingOpen (k := k) 0 i ≤ ⊤ from le_top)).op verticalZeroDivisor =
    (cartierDivisorSheaf (projectiveProduct k)).val.map
      (homOfLE (show rulingOpen (k := k) 0 i ≤ ⊤ from le_top)).op
      (rulingInfinityDivisor 0 +
        principalCartierDivisorHom (projectiveProduct k)
          (Additive.ofMul (rulingCoordinateUnit 0)))
  rw [← verticalZeroDivisor_restrict_ruling i, map_add, rulingInfinityDivisor_restrict,
    principalCartierDivisorHom, cartierEquationClassHom_restrict, ← map_add, ← ofMul_mul]
  fin_cases i <;> simp [verticalZeroEquation, rulingInfinityEquation]

/-- The Picard class of the actual vertical zero divisor is the first fibre class. -/
theorem verticalZeroDivisor_picard_eq_firstFiberClass :
    cartierPicardHom (projectiveProduct k) (verticalZeroDivisor (k := k)) =
      firstFiberClass := by
  rw [verticalZeroDivisor_eq_ruling_add_principal, map_add, cartierPicardHom_principal,
    add_zero, firstFiberClass_eq_ruling]

/-- Inverse translation preserves the first fibre class, by transport of actual fibre kernels. -/
theorem verticalTranslation_pullback_firstFiberClass (c : k) :
    (schemePicardPullbackHom (verticalTranslation c).inv).toAdditive
        (firstFiberClass (k := k)) = firstFiberClass := by
  have h := neg_kernelLine_toPic_transport (verticalFiberMorphismAt (0 : k))
    (verticalTranslation c) (verticalFiberMorphismAt c) (projectiveTranslationIso (0 : k))
    (verticalTranslation_fibre c).symm
    (verticalFiberKernel_isInvertible (0 : k)) (verticalFiberKernel_isInvertible c)
  change -Additive.ofMul (verticalFiberLine c).toPic =
    (schemePicardPullbackHom (verticalTranslation c).inv).toAdditive
      (-Additive.ofMul (verticalFiberLine (0 : k)).toPic) at h
  rw [verticalFiberClass_eq_firstFiberClass, verticalFiberClass_eq_firstFiberClass] at h
  exact h.symm

/-- Every translated vertical Cartier fibre represents `a`, including the fibre at zero. -/
theorem verticalFiberDivisorAt_picard_eq_firstFiberClass (c : k) :
    cartierPicardHom (projectiveProduct k) (verticalFiberDivisorAt (k := k) c) =
      firstFiberClass := by
  rw [verticalFiberDivisorAt, cartierPicardHom_pullbackDivisor_eq,
    verticalZeroDivisor_picard_eq_firstFiberClass, verticalTranslation_pullback_firstFiberClass]

local instance verticalPicardInitialIntegral :
    IsIntegral (projectiveProductInitial (k := k)).carrier :=
  FrobeniusGraphPicardClassIntegral.projectiveProduct_isIntegral

local instance verticalPicardStageIntegral (N : ℕ) :
    IsIntegral (projectiveContactStage (k := k) N) :=
  FrobeniusTowerFunctionField.PlaneChartedScheme.instStageIsIntegral
    (projectiveProductInitial (k := k)) N

/-- The accepted total first fibre class is the Picard pullback of the first fibre class. -/
theorem firstFiberTotalClass_eq_pullback_firstFiberClass (N : ℕ) :
    firstFiberTotalClass (k := k) N =
      (schemePicardPullbackHom (projectiveContactProjection N)).toAdditive firstFiberClass := by
  unfold firstFiberTotalClass firstFiberClass
  rw [map_neg]
  change -Additive.ofMul
      (pullbackInvertibleSheaf (projectiveContactProjection N) verticalFiberIdealLine).toPic =
    -Additive.ofMul
      (schemePicardPullbackHom (projectiveContactProjection N) verticalFiberIdealLine.toPic)
  rw [schemePicardPullbackHom_toPic]

/-- The actual Cartier divisor used to compute the vertical intersection represents the table's
total first fibre class on every contact stage. -/
theorem stageVerticalDivisor_picard_eq_firstFiberTotalClass (N : ℕ) (c : k) :
    cartierPicardHom (projectiveContactStage (k := k) N)
        (stageVerticalDivisor (k := k) N c) = firstFiberTotalClass N := by
  rw [stageVerticalDivisor, cartierPicardHom_pullbackDivisor_eq,
    verticalFiberDivisorAt_picard_eq_firstFiberClass,
    firstFiberTotalClass_eq_pullback_firstFiberClass]

end KltDP.Examples.FrobeniusVerticalPicardBridge
