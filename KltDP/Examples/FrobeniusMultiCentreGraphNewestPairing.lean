import KltDP.Examples.FrobeniusMultiCentreNewestExceptionalRows

/-!
# The actual global strict graph meets every newest exceptional class with degree one

Apply the actual newest-curve restriction-degree homomorphism to the
proved global strict-graph Picard row. The proved ruling and total
exceptional rows evaluate it as one. The original kernel-class pairing
adapter and symmetry give both orders of the original surface pairing.
Only the existing global surface projectivity premise is retained.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusMultiCentreGraphNewestPairing

open KltDP.Geometry KltDP.Geometry.PrimeCurveClassPairing
open FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
  FrobeniusMultiCentreExceptional FrobeniusMultiCentreExceptionalPrime
  FrobeniusMultiCentreExceptionalGlobalClasses FrobeniusMultiCentreGraphCartierStrict
  FrobeniusMultiCentreGraphPicardClass FrobeniusMultiCentreGraphExceptionalPairing
  FrobeniusMultiCentreNewestExceptionalSelf FrobeniusMultiCentreNewestExceptionalRows

variable {k : Type u} [Field k] [IsAlgClosed k]
  (q n : ℕ) (a : Fin n → k) (ha : Function.Injective a)
  [Fact (q + 1).Prime] [CharP k (q + 1)]
  (hproj : IsProjectiveOverField (multiStructure (q + 1) n a)) (i : Fin n)

/-- The original newest curve has restriction degree one on the actual global graph class. -/
theorem newestPairing_strictGraph :
    newestPairing q n a ha hproj i
      (-Additive.ofMul (multiGraphStrictKernelLine q n a ha).toPic) = 1 := by
  rw [strictGraphKernelLine_picard_row, map_sub, map_add, map_nsmul,
    newestPairing_firstFiber, newestPairing_secondFiber, newestPairing_sum_total]
  simp

/-- `P_i · B = 1` for the actual original negative kernel classes. -/
theorem newestKernel_graphKernel_pairing_eq_one :
    multiPairing (q + 1) n a ha hproj
      (-Additive.ofMul (exceptionalKernelLine q n a ha i (.inr PUnit.unit)).toPic)
      (-Additive.ofMul (multiGraphStrictKernelLine q n a ha).toPic) = 1 := by
  letI := exceptionalCurve_isIntegral q n a ha i (.inr PUnit.unit)
  exact (pairing_kernelLine_left (multiSurfaceSurface (q + 1) n a ha hproj)
    (multiSurfaceSurface_regularPoints (q + 1) n a ha hproj)
    (exceptionalPrimeCurveSPn q n a ha i (.inr PUnit.unit) hproj)
    (exceptionalCurveι q n a i (.inr PUnit.unit))
    (coe_exceptionalPrimeCurveSPn q n a ha i (.inr PUnit.unit) hproj)
    (exceptionalKernelLine q n a ha i (.inr PUnit.unit)) rfl
    (-Additive.ofMul (multiGraphStrictKernelLine q n a ha).toPic)).trans
    (newestPairing_strictGraph q n a ha hproj i)

/-- `B · P_i = 1` for the actual original negative kernel classes. -/
theorem graphKernel_newestKernel_pairing_eq_one :
    multiPairing (q + 1) n a ha hproj
      (-Additive.ofMul (multiGraphStrictKernelLine q n a ha).toPic)
      (-Additive.ofMul (exceptionalKernelLine q n a ha i (.inr PUnit.unit)).toPic) = 1 := by
  rw [multiPairing_symm]
  exact newestKernel_graphKernel_pairing_eq_one q n a ha hproj i

/-- The same original graph intersection with the proved newest total exceptional class. -/
theorem graphKernel_newestTotalClass_pairing_eq_one :
    multiPairing (q + 1) n a ha hproj
      (-Additive.ofMul (multiGraphStrictKernelLine q n a ha).toPic)
      (exceptionalClass (q + 1) n a i (Fin.last q)) = 1 := by
  rw [← newestClass_SPn q n a ha i]
  exact graphKernel_newestKernel_pairing_eq_one q n a ha hproj i

end KltDP.Examples.FrobeniusMultiCentreGraphNewestPairing
