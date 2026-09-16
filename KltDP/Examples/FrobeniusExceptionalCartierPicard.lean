import KltDP.Examples.FrobeniusExceptionalCartier
import KltDP.Examples.FrobeniusOldExceptionalBirthCartier
import KltDP.Examples.FrobeniusOldExceptionalPicard
import KltDP.Geometry.SchemeKernelGluedIso

/-!
# The Cartier classes of `P` and of `C_j` (birth stage) are lane A2's Picard classes

Through the public kernel comparison `kernelIdealGluedIso` (`schemeKernelIdeal f ≅
schemeKernelIdeal f.ker.gluedTo`), the Cartier classes of the effective divisors
`stepExceptionalDivisor n` (the newest exceptional curve `P` on stage `n+1`) and
`oldStrictDivisor j` (`C_j` on its birth stage `j+2`) are the accepted/lane-A2 Picard classes
`stepExceptionalPicardClass n = −[stepExceptionalIdealLine n]` and
`oldStrictPicardClass j = −[oldStrictKernelLine j]` used in the tower relation. Together with
`fiberStrictDivisor_picard` (`F̃`), all three curve divisors have the classes of lane A2's Picard
relation. Bundle `f29_exceptional_cartier_picard` with a universe check.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Examples.FrobeniusExceptionalCartierPicard

open KltDP.Geometry
open FrobeniusGlobalBlowupStages FrobeniusStrictTransformProductKernel
  FrobeniusStrictTransformPicardStep FrobeniusOldExceptionalChartIdeals
  FrobeniusOldExceptionalPicard FrobeniusExceptionalCartier FrobeniusOldExceptionalBirthCartier
  FrobeniusTowerFunctionField FrobeniusGraphPicardClassIntegral FrobeniusBlowupChartIteration

variable {k : Type u} [Field k]

local instance initialIntegral : IsIntegral (projectiveProductInitial (k := k)).carrier :=
  projectiveProduct_isIntegral

local instance originMaximal : (originPoint (k := k)).asIdeal.IsMaximal :=
  FrobeniusBlowupChartIteration.centerIdeal_isMaximal

/-- **`[P] = cartierPicardHom (stepExceptionalDivisor n)`**: the Cartier class of the newest
exceptional curve is the accepted `stepExceptionalPicardClass n`. -/
theorem stepExceptionalDivisor_picard' (n : ℕ) :
    cartierPicardHom (projectiveContactStage (k := k) (n + 1)) (stepExceptionalDivisor n) =
      stepExceptionalPicardClass n := by
  rw [stepExceptionalDivisor_picard]
  change -Additive.ofMul (gluedKernelLine (stepExceptionalIdeal (k := k) n)
      (stepExceptionalIdeal_locallyPrincipalRegular n)).toPic =
    -Additive.ofMul (stepExceptionalIdealLine (k := k) n).toPic
  rw [← toPic_eq_gluedKernelLine (stepExceptionalInclusion (k := k) n)
    (stepExceptionalIdealLine (k := k) n).property]
  rfl

/-- **`[C_j] = cartierPicardHom (oldStrictDivisor j)`** on the birth stage: the Cartier class of
`C_j` is lane A2's `oldStrictPicardClass j`. -/
theorem oldStrictDivisor_picard' (j : ℕ) :
    cartierPicardHom (projectiveContactStage (k := k) (j + 1 + 1)) (oldStrictDivisor j) =
      oldStrictPicardClass j := by
  rw [oldStrictDivisor_picard]
  change -Additive.ofMul (gluedKernelLine (oldStrictIdeal (k := k) j)
      (oldStrictIdeal_locallyPrincipalRegular j)).toPic =
    -Additive.ofMul (oldStrictKernelLine (k := k) j).toPic
  rw [← toPic_eq_gluedKernelLine (oldExceptionalStrictι (k := k) j)
    (oldStrictKernel_isInvertible j)]
  rfl

end KltDP.Examples.FrobeniusExceptionalCartierPicard

namespace KltDP.Examples

open KltDP.Geometry FrobeniusGlobalBlowupStages FrobeniusStrictTransformPicardStep
  FrobeniusOldExceptionalPicard FrobeniusExceptionalCartier FrobeniusOldExceptionalBirthCartier
  FrobeniusExceptionalCartierPicard FrobeniusTowerFunctionField FrobeniusGraphPicardClassIntegral

local instance picardInitialIntegral' {k : Type u} [Field k] :
    IsIntegral (projectiveProductInitial (k := k)).carrier :=
  projectiveProduct_isIntegral

/-- Bundle: the Cartier classes of the divisors `P` (every stage `n+1`) and `C_j` (birth stage
`j+2`) are the Picard classes of lane A2's tower relation. -/
theorem f29_exceptional_cartier_picard (k : Type u) [Field k] :
    (∀ n : ℕ, cartierPicardHom (projectiveContactStage (k := k) (n + 1)) (stepExceptionalDivisor n) =
      stepExceptionalPicardClass n) ∧
    (∀ j : ℕ, cartierPicardHom (projectiveContactStage (k := k) (j + 1 + 1)) (oldStrictDivisor j) =
      oldStrictPicardClass j) :=
  ⟨stepExceptionalDivisor_picard', oldStrictDivisor_picard'⟩

/-- The bundle has exactly one universe parameter. -/
theorem f29_exceptional_cartier_picard_universe_check (k : Type u) [Field k] : True := by
  have _ := f29_exceptional_cartier_picard.{u} k
  trivial

end KltDP.Examples
