import KltDP.Examples.FrobeniusMultiCentreGraphTotalExceptionalRows
import KltDP.Examples.FrobeniusMultiCentreFiberGlobalClass
import KltDP.Examples.FrobeniusMultiCentreFiberContacts

/-!
# The actual strict fibres against all total exceptional classes

The negative Picard class of the original fibre kernel line is
`b - sum E_ij`. Evaluating it on each newest curve gives the Kronecker
delta. Every old exceptional
curve is actually disjoint from every strict fibre, so its kernel degree
is zero. The proved consecutive-total-class relations propagate the
newest values to all original total exceptional classes.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusMultiCentreFiberExceptionalRows

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
  KltDP.Geometry.PrimeCurveClassPairing
open FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
  FrobeniusMultiCentreExceptional FrobeniusMultiCentreExceptionalPrime
  FrobeniusMultiCentreExceptionalGlobalClasses FrobeniusMultiCentreGraphFiber
  FrobeniusMultiCentreFiberGlobalClass FrobeniusMultiCentreFiberContacts
  FrobeniusMultiCentreGraphExceptionalPairing FrobeniusMultiCentreNewestExceptionalSelf
  FrobeniusMultiCentreNewestExceptionalRows

variable {k : Type u} [Field k] [IsAlgClosed k]
  (q n : ℕ) (a : Fin n → k) (ha : Function.Injective a)
  [Fact (q + 1).Prime] [CharP k (q + 1)]
  (hproj : IsProjectiveOverField (multiStructure (q + 1) n a))

/-- The newest curve has degree one on its own strict fibre and zero on every other one. -/
theorem newestPairing_fiberKernel (i i' : Fin n) :
    newestPairing q n a ha hproj i
      (-Additive.ofMul (fiberKernelLine q n a ha i').toPic) = if i' = i then 1 else 0 := by
  classical
  rw [fiberClass_SPn, map_sub, newestPairing_secondFiber]
  simp only [map_sum, newestPairing_total]
  by_cases h : i' = i <;> simp [h]

/-- The original symmetric pairing with each newest kernel class has the same delta value. -/
theorem newestKernel_fiberKernel_pairing (i i' : Fin n) :
    multiPairing (q + 1) n a ha hproj
      (-Additive.ofMul (exceptionalKernelLine q n a ha i (.inr PUnit.unit)).toPic)
      (-Additive.ofMul (fiberKernelLine q n a ha i').toPic) = if i' = i then 1 else 0 := by
  letI := exceptionalCurve_isIntegral q n a ha i (.inr PUnit.unit)
  exact (pairing_kernelLine_left (multiSurfaceSurface (q + 1) n a ha hproj)
    (multiSurfaceSurface_regularPoints (q + 1) n a ha hproj)
    (exceptionalPrimeCurveSPn q n a ha i (.inr PUnit.unit) hproj)
    (exceptionalCurveι q n a i (.inr PUnit.unit))
    (coe_exceptionalPrimeCurveSPn q n a ha i (.inr PUnit.unit) hproj)
    (exceptionalKernelLine q n a ha i (.inr PUnit.unit)) rfl
    (-Additive.ofMul (fiberKernelLine q n a ha i').toPic)).trans
    (newestPairing_fiberKernel q n a ha hproj i i')

/-- The actual old exceptional prime curves have degree zero on every actual fibre kernel. -/
theorem oldRestrictionDegree_fiberKernel_eq_zero (i i' : Fin n) (j : Fin q) :
    (multiSurfaceSurface (q + 1) n a ha hproj).picardRestrictionDegreeHom
      (exceptionalPrimeCurveSPn q n a ha i (.inl j) hproj)
      (-Additive.ofMul (fiberKernelLine q n a ha i').toPic) = 0 := by
  apply restrictionDegreeHom_neg_kernel_zero (multiSurfaceSurface (q + 1) n a ha hproj)
    (exceptionalPrimeCurveSPn q n a ha i (.inl j) hproj)
    (fiberStrictι (q + 1) n a i') (fiberKernelLine q n a ha i') rfl
  rw [PrimeCurve.range_inclusion, coe_exceptionalPrimeCurveSPn]
  by_cases h : i' = i
  · subst i'
    exact (fiberStrict_disjoint_exceptional_same q n a i j).symm
  · exact (fiberStrict_disjoint_exceptional q n a ha h (.inl j)).symm

theorem oldKernel_fiberKernel_pairing_eq_zero (i i' : Fin n) (j : Fin q) :
    multiPairing (q + 1) n a ha hproj
      (-Additive.ofMul (exceptionalKernelLine q n a ha i (.inl j)).toPic)
      (-Additive.ofMul (fiberKernelLine q n a ha i').toPic) = 0 := by
  letI := exceptionalCurve_isIntegral q n a ha i (.inl j)
  exact (pairing_kernelLine_left (multiSurfaceSurface (q + 1) n a ha hproj)
    (multiSurfaceSurface_regularPoints (q + 1) n a ha hproj)
    (exceptionalPrimeCurveSPn q n a ha i (.inl j) hproj)
    (exceptionalCurveι q n a i (.inl j))
    (coe_exceptionalPrimeCurveSPn q n a ha i (.inl j) hproj)
    (exceptionalKernelLine q n a ha i (.inl j)) rfl
    (-Additive.ofMul (fiberKernelLine q n a ha i').toPic)).trans
    (oldRestrictionDegree_fiberKernel_eq_zero q n a ha hproj i i' j)

/-- The accepted additive pairing homomorphism against an original strict-fibre kernel class. -/
def fiberPairing (i : Fin n) : Additive (multiSurface (q + 1) n a).Pic →+ ℤ :=
  (multiSurfaceSurface (q + 1) n a ha hproj).picardPairingHom
    (multiSurfaceSurface_regularPoints (q + 1) n a ha hproj)
    (-Additive.ofMul (fiberKernelLine q n a ha i).toPic).toMul

/-- Every total exceptional class has fibre pairing one in its own tower and zero elsewhere. -/
theorem fiberPairing_total (i i' : Fin n) (j : Fin (q + 1)) :
    fiberPairing q n a ha hproj i (exceptionalClass (q + 1) n a i' j) =
      if i = i' then 1 else 0 := by
  refine Fin.reverseInduction ?_ (fun r hr => ?_) j
  · change multiPairing (q + 1) n a ha hproj
      (exceptionalClass (q + 1) n a i' (Fin.last q))
      (-Additive.ofMul (fiberKernelLine q n a ha i).toPic) = _
    rw [← newestClass_SPn q n a ha i']
    exact newestKernel_fiberKernel_pairing q n a ha hproj i' i
  · have h : fiberPairing q n a ha hproj i
        (-Additive.ofMul (exceptionalKernelLine q n a ha i' (.inl r)).toPic) = 0 :=
      oldKernel_fiberKernel_pairing_eq_zero q n a ha hproj i' i r
    have hC : -Additive.ofMul (exceptionalKernelLine q n a ha i' (.inl r)).toPic =
        exceptionalClass (q + 1) n a i' r.castSucc -
          exceptionalClass (q + 1) n a i' r.succ := chainClass_SPn q n a ha i' r
    rw [hC, map_sub, hr] at h
    exact sub_eq_zero.mp h

theorem fiberKernel_totalClass_pairing (i i' : Fin n) (j : Fin (q + 1)) :
    multiPairing (q + 1) n a ha hproj
      (-Additive.ofMul (fiberKernelLine q n a ha i).toPic)
      (exceptionalClass (q + 1) n a i' j) = if i = i' then 1 else 0 := by
  rw [multiPairing_symm]
  exact fiberPairing_total q n a ha hproj i i' j

/-- The original full exceptional sum has fibre pairing `q + 1`. -/
theorem fiberPairing_sum_total (i : Fin n) :
    fiberPairing q n a ha hproj i
      (∑ i' : Fin n, ∑ j : Fin (q + 1), exceptionalClass (q + 1) n a i' j) =
      (q + 1 : ℕ) := by
  classical
  simp only [map_sum, fiberPairing_total]
  simp

end KltDP.Examples.FrobeniusMultiCentreFiberExceptionalRows
