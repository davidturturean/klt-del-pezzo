import KltDP.Examples.FrobeniusMultiCentreExceptionalRulingRows
import KltDP.Examples.FrobeniusMultiCentreFiberExceptionalRows

/-!
# Original global graph and fibre ruling, square and mixed intersection values

Apply the actual additive pairing to the proved original kernel-line
Picard rows, using the proved ruling and exceptional rows. This gives
`B.a=1`, `B.b=p`, `F_i.a=1`, `F_i.b=0`, `B²=2p-np`,
`F_i²=-p`, `B.F_i=0`, and zero pairing of distinct strict fibres.
Here `p=q+1`, and only the actual global surface projectivity premise
already required by the numerical API is retained.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusMultiCentreGraphFiberNumericalValues

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
  FrobeniusMultiCentreGraphCartierStrict FrobeniusMultiCentreGraphPicardClass
  FrobeniusMultiCentreFiberGlobalClass FrobeniusMultiCentreGraphExceptionalPairing
  FrobeniusMultiCentreGraphTotalExceptionalRows FrobeniusMultiCentreFiberExceptionalRows
  FrobeniusMultiCentreRulingPairing FrobeniusMultiCentreExceptionalRulingRows

variable {k : Type u} [Field k] [IsAlgClosed k]
  (q n : ℕ) (a : Fin n → k) (ha : Function.Injective a)
  [Fact (q + 1).Prime] [CharP k (q + 1)]
  (hproj : IsProjectiveOverField (multiStructure (q + 1) n a))

/-- The accepted additive homomorphism in the first argument of the actual global pairing. -/
abbrev multiPairingHom (y : Additive (multiSurface (q + 1) n a).Pic) :
    Additive (multiSurface (q + 1) n a).Pic →+ ℤ :=
  (multiSurfaceSurface (q + 1) n a ha hproj).picardPairingHom
    (multiSurfaceSurface_regularPoints (q + 1) n a ha hproj) y.toMul

theorem multiPairingHom_apply (y x : Additive (multiSurface (q + 1) n a).Pic) :
    multiPairingHom q n a ha hproj y x = multiPairing (q + 1) n a ha hproj x y := rfl

theorem graphPairing_firstFiber_one :
    graphPairing q n a ha hproj (multiFirstFiberClass (q + 1) n a) = 1 := by
  change multiPairing (q + 1) n a ha hproj (multiFirstFiberClass (q + 1) n a)
    (-Additive.ofMul (multiGraphStrictKernelLine q n a ha).toPic) = 1
  rw [multiPairing_symm]
  change multiPairingHom q n a ha hproj (multiFirstFiberClass (q + 1) n a)
    (-Additive.ofMul (multiGraphStrictKernelLine q n a ha).toPic) = 1
  rw [strictGraphKernelLine_picard_row, map_sub, map_add, map_nsmul]
  simp only [map_sum, multiPairingHom_apply, totalClass_firstFiber_pairing_zero,
    multiPairing_first_self_zero, multiPairing_second_first_one, nsmul_zero, zero_add,
    Finset.sum_const_zero, sub_zero]

theorem graphPairing_secondFiber_eq :
    graphPairing q n a ha hproj (multiSecondFiberClass (q + 1) n a) = (q + 1 : ℕ) := by
  change multiPairing (q + 1) n a ha hproj (multiSecondFiberClass (q + 1) n a)
    (-Additive.ofMul (multiGraphStrictKernelLine q n a ha).toPic) = _
  rw [multiPairing_symm]
  change multiPairingHom q n a ha hproj (multiSecondFiberClass (q + 1) n a)
    (-Additive.ofMul (multiGraphStrictKernelLine q n a ha).toPic) = _
  rw [strictGraphKernelLine_picard_row, map_sub, map_add, map_nsmul]
  simp only [map_sum, multiPairingHom_apply, totalClass_secondFiber_pairing_zero,
    multiPairing_first_second_one, multiPairing_second_self_zero, nsmul_eq_mul, mul_one,
    Finset.sum_const_zero, add_zero, sub_zero]

theorem fiberPairing_firstFiber_one (i : Fin n) :
    fiberPairing q n a ha hproj i (multiFirstFiberClass (q + 1) n a) = 1 := by
  change multiPairing (q + 1) n a ha hproj (multiFirstFiberClass (q + 1) n a)
    (-Additive.ofMul (fiberKernelLine q n a ha i).toPic) = 1
  rw [multiPairing_symm]
  change multiPairingHom q n a ha hproj (multiFirstFiberClass (q + 1) n a)
    (-Additive.ofMul (fiberKernelLine q n a ha i).toPic) = 1
  rw [fiberClass_SPn, map_sub]
  simp only [map_sum, multiPairingHom_apply, totalClass_firstFiber_pairing_zero,
    multiPairing_second_first_one, Finset.sum_const_zero, sub_zero]

theorem fiberPairing_secondFiber_zero (i : Fin n) :
    fiberPairing q n a ha hproj i (multiSecondFiberClass (q + 1) n a) = 0 := by
  change multiPairing (q + 1) n a ha hproj (multiSecondFiberClass (q + 1) n a)
    (-Additive.ofMul (fiberKernelLine q n a ha i).toPic) = 0
  rw [multiPairing_symm]
  change multiPairingHom q n a ha hproj (multiSecondFiberClass (q + 1) n a)
    (-Additive.ofMul (fiberKernelLine q n a ha i).toPic) = 0
  rw [fiberClass_SPn, map_sub]
  simp only [map_sum, multiPairingHom_apply, totalClass_secondFiber_pairing_zero,
    multiPairing_second_self_zero, Finset.sum_const_zero, sub_zero]

/-- The original global graph square is `2p - np`, for `p=q+1`. -/
theorem graphKernel_self_pairing :
    multiPairing (q + 1) n a ha hproj
      (-Additive.ofMul (multiGraphStrictKernelLine q n a ha).toPic)
      (-Additive.ofMul (multiGraphStrictKernelLine q n a ha).toPic) =
      2 * (q + 1 : ℕ) - (n : ℤ) * (q + 1 : ℕ) := by
  change graphPairing q n a ha hproj (-Additive.ofMul (multiGraphStrictKernelLine q n a ha).toPic) = _
  rw [strictGraphKernelLine_picard_row, map_sub, map_add, map_nsmul,
    graphPairing_firstFiber_one, graphPairing_secondFiber_eq, graphPairing_sum_total]
  simp only [nsmul_eq_mul, mul_one]
  ring

/-- The actual fibre pairing matrix has diagonal `-p` and zero elsewhere. -/
theorem fiberKernel_pairing (i i' : Fin n) :
    multiPairing (q + 1) n a ha hproj
      (-Additive.ofMul (fiberKernelLine q n a ha i').toPic)
      (-Additive.ofMul (fiberKernelLine q n a ha i).toPic) =
      if i = i' then -((q + 1 : ℕ) : ℤ) else 0 := by
  classical
  change fiberPairing q n a ha hproj i (-Additive.ofMul (fiberKernelLine q n a ha i').toPic) = _
  rw [fiberClass_SPn, map_sub, fiberPairing_secondFiber_zero]
  simp only [map_sum, fiberPairing_total]
  by_cases h : i = i' <;> simp [h]

theorem fiberKernel_self_pairing (i : Fin n) :
    multiPairing (q + 1) n a ha hproj
      (-Additive.ofMul (fiberKernelLine q n a ha i).toPic)
      (-Additive.ofMul (fiberKernelLine q n a ha i).toPic) = -((q + 1 : ℕ) : ℤ) := by
  rw [fiberKernel_pairing, if_pos rfl]

/-- The original strict graph and every original strict tangent fibre have pairing zero. -/
theorem fiberKernel_graphKernel_pairing_zero (i : Fin n) :
    multiPairing (q + 1) n a ha hproj
      (-Additive.ofMul (fiberKernelLine q n a ha i).toPic)
      (-Additive.ofMul (multiGraphStrictKernelLine q n a ha).toPic) = 0 := by
  change graphPairing q n a ha hproj (-Additive.ofMul (fiberKernelLine q n a ha i).toPic) = 0
  rw [fiberClass_SPn, map_sub, graphPairing_secondFiber_eq]
  simp only [map_sum, graphPairing_total, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, sub_self]

theorem graphKernel_fiberKernel_pairing_zero (i : Fin n) :
    multiPairing (q + 1) n a ha hproj
      (-Additive.ofMul (multiGraphStrictKernelLine q n a ha).toPic)
      (-Additive.ofMul (fiberKernelLine q n a ha i).toPic) = 0 := by
  rw [multiPairing_symm]
  exact fiberKernel_graphKernel_pairing_zero q n a ha hproj i

end KltDP.Examples.FrobeniusMultiCentreGraphFiberNumericalValues
