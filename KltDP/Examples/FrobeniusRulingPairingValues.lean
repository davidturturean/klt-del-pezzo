import KltDP.Examples.FrobeniusRulingClassPairing
import KltDP.Examples.FrobeniusGraphFirstFiberDegree
import KltDP.Examples.FrobeniusGraphBaseRows
import KltDP.Examples.FrobeniusStageOneProjective

/-!
# The ruling matrix and both numerical graph rows

The compiled geometric intersection of the strict diagonal with `a` on the first blowup gives
`Γ₁ · a = 1` downstairs. The actual graph class is `a + b`, and the actual fibre self-pairings
are zero; symmetry and bilinearity therefore give `a · b = b · a = 1`. Applying the same pairing
to the actual integral graph class `p a + b` proves `Γ_p · a = 1`, `Γ_p · b = p`, and
`Γ_p² = 2p`. The accepted degree transport then gives `B · b = m + (n + 1)` on the contact stage.

There is no assumed degree or transition exponent. Algebraic closure is explicit. The final
contact-stage statement retains its stage-projectivity hypothesis.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusRulingPairingValues

open KltDP.Geometry KltDP.Geometry.PrimeCurveClassPairing
open KltDP.Geometry.PrimeCurveOfClosedImmersion
open FrobeniusProjectivePoints FrobeniusGraphClosed FrobeniusStageZeroProjective
open FrobeniusGraphPicardClassFrames FrobeniusGraphPicardClassFiberClasses
open FrobeniusGraphPicardClassTotalTransform FrobeniusGlobalBlowupStages
open FrobeniusGraphPrimeCurve FrobeniusGraphBaseRows FrobeniusMultiCentreIsoOpenClasses
open FrobeniusRulingClassPairing FrobeniusGraphFirstFiberDegree
open FrobeniusStageOneProjective FrobeniusStrictTransformPairing

variable {k : Type u} [Field k] [IsAlgClosed k]

local instance rulingValuesGraphIntegral (p : ℕ) : IsIntegral (graph (k := k) p) :=
  isIntegral_of_iso_projectiveLine (graphIsoProjectiveLine p)

/-- The graph's restriction-degree homomorphism is pairing with its actual integral ideal class. -/
theorem graphBasePairing_eq_basePairing (p : ℕ) (q : Additive (projectiveProduct k).Pic) :
    graphBasePairing (k := k) p q = basePairing (graphBaseClass p) q := by
  have h := pairing_kernelLine_left projectiveProductSurface baseRegular (graphPrimeCurve p)
    (graphι p) rfl (graphιLine p) rfl q
  change basePairing (-Additive.ofMul (graphιLine p).toPic) q = graphBasePairing p q at h
  rw [graphιLine_toPic] at h
  exact h.symm

/-- The diagonal has degree one against `a`, using the already proved first-blowup computation. -/
theorem diagonal_firstFiber_one :
    graphBasePairing (k := k) 1 firstFiberClass = 1 := by
  have h := graphStrictPairing_firstFiberTotalClass_eq_one (k := k) 0 stage_one_projective 0
  rw [graphStrictPairing_firstFiber_eq_base] at h
  exact h

/-- The two ruling classes have intersection one. -/
theorem basePairing_second_first_one :
    basePairing (secondFiberClass (k := k)) firstFiberClass = 1 := by
  have h := diagonal_firstFiber_one (k := k)
  rw [graphBasePairing_eq_basePairing, graphBaseClass, inverse_graphIdeal_picard_eq_actual_fibers,
    one_nsmul] at h
  change pairing projectiveProductSurface baseRegular (firstFiberClass + secondFiberClass)
    firstFiberClass = 1 at h
  rw [pairing_add_left] at h
  change basePairing firstFiberClass firstFiberClass +
    basePairing secondFiberClass firstFiberClass = 1 at h
  rw [basePairing_first_self_zero, zero_add] at h
  exact h

theorem basePairing_first_second_one :
    basePairing (firstFiberClass (k := k)) secondFiberClass = 1 :=
  (pairing_symm projectiveProductSurface baseRegular _ _).trans basePairing_second_first_one

/-- The actual base graph has first ruling degree one for every exponent, including zero. -/
theorem graphBasePairing_firstFiber_one (p : ℕ) :
    graphBasePairing (k := k) p firstFiberClass = 1 := by
  rw [graphBasePairing_eq_basePairing, graphBaseClass, inverse_graphIdeal_picard_eq_actual_fibers]
  change pairing projectiveProductSurface baseRegular (p • firstFiberClass + secondFiberClass)
    firstFiberClass = 1
  rw [pairing_add_left, pairing_nsmul_left]
  change (p : ℤ) * basePairing firstFiberClass firstFiberClass +
    basePairing secondFiberClass firstFiberClass = 1
  rw [basePairing_first_self_zero,
    basePairing_second_first_one, mul_zero, zero_add]

/-- The actual base graph has second ruling degree equal to its exponent. -/
theorem graphBasePairing_secondFiber_eq_exponent (p : ℕ) :
    graphBasePairing (k := k) p secondFiberClass = (p : ℤ) := by
  rw [graphBasePairing_eq_basePairing, graphBaseClass, inverse_graphIdeal_picard_eq_actual_fibers]
  change pairing projectiveProductSurface baseRegular (p • firstFiberClass + secondFiberClass)
    secondFiberClass = (p : ℤ)
  rw [pairing_add_left, pairing_nsmul_left]
  change (p : ℤ) * basePairing firstFiberClass secondFiberClass +
    basePairing secondFiberClass secondFiberClass = (p : ℤ)
  rw [basePairing_first_second_one,
    basePairing_second_self_zero, mul_one, add_zero]

/-- The actual base graph has self-intersection `2p`. -/
theorem graphBasePairing_graphBaseClass_eq_twice (p : ℕ) :
    graphBasePairing (k := k) p (graphBaseClass p) = 2 * (p : ℤ) := by
  rw [graphBasePairing_graphBaseClass, graphBasePairing_firstFiber_one,
    graphBasePairing_secondFiber_eq_exponent]
  ring

/-- The strict graph has the manuscript's second ruling degree on the actual contact stage. -/
theorem graphStrictPairing_secondFiberTotalClass_eq (n : ℕ)
    (hproj : IsProjectiveOverField ((projectiveProductInitial (k := k)).stage (n + 1)).structureMap)
    (m : ℕ) :
    graphStrictPairing n hproj m (secondFiberTotalClass (n + 1)) = (m + (n + 1) : ℤ) := by
  rw [graphStrictPairing_secondFiber_eq_base]
  simpa only [Nat.cast_add, Nat.cast_one] using
    graphBasePairing_secondFiber_eq_exponent (k := k) (m + (n + 1))

end KltDP.Examples.FrobeniusRulingPairingValues
