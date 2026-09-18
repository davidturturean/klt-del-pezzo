import KltDP.Examples.FrobeniusMultiCentreContractingNef
import KltDP.Examples.FrobeniusMultiCentreRulingFibers
import KltDP.Examples.FrobeniusMultiCentreFiberProjectiveLine
import KltDP.Examples.FrobeniusMultiCentreExceptionalPrime

/-!
# M-null prime curves over a selected ruling height

The actual special fiber is covered by its original strict fiber and embedded
exceptional components. Irreducibility selects one component, and the surface's
proved prime-curve maximality makes that containment equality. The computed
M-degree one excludes the newest exceptional component. The remaining curves
are exactly the strict fiber and the old exceptional components.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Examples.FrobeniusMultiCentreSpecialNullCurves

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open PrimeCurveOfClosedImmersion PrimeCurveTransversalPoint PrimeCurveClassPairing
open FrobeniusProjectivePoints FrobeniusGraphClosed
open FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
open FrobeniusMultiCentreGraphFiber FrobeniusMultiCentreFiberProjectiveLine
open FrobeniusMultiCentreFiberGlobalClass FrobeniusMultiCentreExceptional
open FrobeniusMultiCentreExceptionalPrime FrobeniusMultiCentreExceptionalGlobalClasses
open FrobeniusMultiCentreGraphExceptionalPairing FrobeniusExceptionalFinalConfiguration
open FrobeniusMultiCentreContractingClass FrobeniusMultiCentreContractingNef
open FrobeniusMultiCentreRulingFibers

private theorem prime_eq_of_subset {k : Type u} [Field k]
    {X : NormalProjectiveSurface k} (C E : X.PrimeCurve)
    (h : (C : Set X.toScheme) ⊆ (E : Set X.toScheme)) : C = E := by
  apply PrimeCurve.ext
  exact C.coe_eq_of_subset_irreducibleCloseds E.1 h E.ne_univ

variable {k : Type u} [Field k] [IsAlgClosed k]
  (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
  (a : Fin n → k) (ha : Function.Injective a)
  (hproj : IsProjectiveOverField (multiStructure (q + 1) n a))

/-- The original strict special fiber as an actual prime curve. -/
def fiberPrimeCurve (i : Fin n) :
    (multiSurfaceSurface (q + 1) n a ha hproj).PrimeCurve :=
  primeCurveOfIsoProjectiveLine (multiSurfaceSurface (q + 1) n a ha hproj)
    (fiberStrictι (q + 1) n a i) (globalFiberIsoProjectiveLine q n a ha i)

@[simp] theorem coe_fiberPrimeCurve (i : Fin n) :
    (fiberPrimeCurve q n a ha hproj i :
      Set (multiSurfaceSurface (q + 1) n a ha hproj).toScheme) =
      Set.range (fiberStrictι (q + 1) n a i).base := rfl

/-- The original strict special fiber has actual M-degree zero. -/
theorem fiberPrimeCurve_degree (i : Fin n) :
    (multiSurfaceSurface (q + 1) n a ha hproj).picardRestrictionDegreeHom
      (fiberPrimeCurve q n a ha hproj i) (contractingClass q n a ha) = 0 := by
  letI := isIntegral_of_iso_projectiveLine (globalFiberIsoProjectiveLine q n a ha i)
  have hp := pairing_kernelLine_left (multiSurfaceSurface (q + 1) n a ha hproj)
    (multiSurfaceSurface_regularPoints (q + 1) n a ha hproj)
    (fiberPrimeCurve q n a ha hproj i) (fiberStrictι (q + 1) n a i)
    (coe_fiberPrimeCurve q n a ha hproj i) (fiberKernelLine q n a ha i) rfl
    (contractingClass q n a ha)
  rw [← hp, pairing_symm]
  exact contractingClass_fiber_pairing q n a ha hproj i

/-- All actual embedded exceptional primes have the computed degree: zero
for old components, one for the newest component. -/
theorem exceptionalPrimeCurve_degree (i : Fin n) (idx : FinalIndex.{0} q) :
    (multiSurfaceSurface (q + 1) n a ha hproj).picardRestrictionDegreeHom
      (exceptionalPrimeCurveSPn q n a ha i idx hproj) (contractingClass q n a ha) =
      match idx with | .inl _ => 0 | .inr _ => 1 := by
  letI := exceptionalCurve_isIntegral q n a ha i idx
  have hp := pairing_kernelLine_left (multiSurfaceSurface (q + 1) n a ha hproj)
    (multiSurfaceSurface_regularPoints (q + 1) n a ha hproj)
    (exceptionalPrimeCurveSPn q n a ha i idx hproj) (exceptionalCurveι q n a i idx)
    (coe_exceptionalPrimeCurveSPn q n a ha i idx hproj)
    (exceptionalKernelLine q n a ha i idx) rfl (contractingClass q n a ha)
  rw [← hp, pairing_symm]
  cases idx with
  | inl j => exact contractingClass_old_pairing q n a ha hproj i j
  | inr x =>
      cases x
      exact contractingClass_newest_pairing q n a ha hproj i

/-- Every original M-null prime over a selected height is the strict fiber
or an old exceptional component; the newest component is excluded by its degree. -/
theorem null_curve_over_selected_height (i : Fin n)
    (C : (multiSurfaceSurface (q + 1) n a ha hproj).PrimeCurve)
    (hheight : (C : Set (multiSurfaceSurface (q + 1) n a ha hproj).toScheme) ⊆
      (multiProjection (q + 1) n a ≫ secondProjection).base ⁻¹'
        {point (a i ^ (q + 1))})
    (hnull : (multiSurfaceSurface (q + 1) n a ha hproj).picardRestrictionDegreeHom C
      (contractingClass q n a ha) = 0) :
    C = fiberPrimeCurve q n a ha hproj i ∨
      ∃ j : Fin q, C = exceptionalPrimeCurveSPn q n a ha i (.inl j) hproj := by
  obtain hF | ⟨idx, hE⟩ := irreducible_subset_special_fiber q n a ha i
    (C : Set (multiSurfaceSurface (q + 1) n a ha hproj).toScheme) C.isIrreducible hheight
  · exact Or.inl (prime_eq_of_subset C (fiberPrimeCurve q n a ha hproj i) hF)
  · have heq : C = exceptionalPrimeCurveSPn q n a ha i idx hproj :=
      prime_eq_of_subset C (exceptionalPrimeCurveSPn q n a ha i idx hproj) hE
    cases idx with
    | inl j => exact Or.inr ⟨j, heq⟩
    | inr x =>
        rw [heq, exceptionalPrimeCurve_degree] at hnull
        exact (one_ne_zero hnull).elim

end KltDP.Examples.FrobeniusMultiCentreSpecialNullCurves
