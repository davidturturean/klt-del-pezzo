import KltDP.Examples.FrobeniusMultiCentreGraphNewestPairing
import KltDP.Geometry.HodgeIndexReduction

/-!
# The actual global graph pairs to one with every total exceptional class

The proved old-component rows say that pairing with the graph has the
same value on consecutive total classes. Its proved value on the newest
class is one. Reverse induction gives every original total exceptional
row, and the accepted additive pairing homomorphism gives their sum.
Only the existing projectivity premise of the actual global surface is
retained; no numerical value or geometric identity is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusMultiCentreGraphTotalExceptionalRows

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
  FrobeniusMultiCentreExceptionalGlobalClasses FrobeniusMultiCentreGraphCartierStrict
  FrobeniusMultiCentreGraphExceptionalPairing FrobeniusMultiCentreGraphNewestPairing

variable {k : Type u} [Field k] [IsAlgClosed k]
  (q n : ℕ) (a : Fin n → k) (ha : Function.Injective a)
  [Fact (q + 1).Prime] [CharP k (q + 1)]
  (hproj : IsProjectiveOverField (multiStructure (q + 1) n a))

/-- The existing additive pairing homomorphism against the original strict-graph kernel class. -/
def graphPairing : Additive (multiSurface (q + 1) n a).Pic →+ ℤ :=
  (multiSurfaceSurface (q + 1) n a ha hproj).picardPairingHom
    (multiSurfaceSurface_regularPoints (q + 1) n a ha hproj)
    (-Additive.ofMul (multiGraphStrictKernelLine q n a ha).toPic).toMul

/-- Every actual total exceptional class pairs to one with the original global graph. -/
theorem graphPairing_total (i : Fin n) (j : Fin (q + 1)) :
    graphPairing q n a ha hproj (exceptionalClass (q + 1) n a i j) = 1 := by
  refine Fin.reverseInduction ?_ (fun r hr => ?_) j
  · change multiPairing (q + 1) n a ha hproj
      (exceptionalClass (q + 1) n a i (Fin.last q))
      (-Additive.ofMul (multiGraphStrictKernelLine q n a ha).toPic) = 1
    rw [multiPairing_symm]
    exact graphKernel_newestTotalClass_pairing_eq_one q n a ha hproj i
  · have h : graphPairing q n a ha hproj
        (exceptionalClass (q + 1) n a i r.castSucc -
          exceptionalClass (q + 1) n a i r.succ) = 0 := by
      change multiPairing (q + 1) n a ha hproj
        (exceptionalClass (q + 1) n a i r.castSucc -
          exceptionalClass (q + 1) n a i r.succ)
        (-Additive.ofMul (multiGraphStrictKernelLine q n a ha).toPic) = 0
      rw [multiPairing_symm]
      exact graphKernel_oldTotalDifference_pairing_eq_zero q n a ha hproj i r
    rw [map_sub, hr] at h
    exact sub_eq_zero.mp h

theorem totalClass_graphKernel_pairing_eq_one (i : Fin n) (j : Fin (q + 1)) :
    multiPairing (q + 1) n a ha hproj
      (exceptionalClass (q + 1) n a i j)
      (-Additive.ofMul (multiGraphStrictKernelLine q n a ha).toPic) = 1 :=
  graphPairing_total q n a ha hproj i j

theorem graphKernel_totalClass_pairing_eq_one (i : Fin n) (j : Fin (q + 1)) :
    multiPairing (q + 1) n a ha hproj
      (-Additive.ofMul (multiGraphStrictKernelLine q n a ha).toPic)
      (exceptionalClass (q + 1) n a i j) = 1 := by
  rw [multiPairing_symm]
  exact totalClass_graphKernel_pairing_eq_one q n a ha hproj i j

/-- The full original total-exceptional sum has graph pairing `n * (q + 1)`. -/
theorem graphPairing_sum_total :
    graphPairing q n a ha hproj
      (∑ i : Fin n, ∑ j : Fin (q + 1), exceptionalClass (q + 1) n a i j) =
      (n : ℤ) * (q + 1 : ℕ) := by
  classical
  simp only [map_sum, graphPairing_total, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]

theorem graphKernel_sumTotalClass_pairing :
    multiPairing (q + 1) n a ha hproj
      (-Additive.ofMul (multiGraphStrictKernelLine q n a ha).toPic)
      (∑ i : Fin n, ∑ j : Fin (q + 1), exceptionalClass (q + 1) n a i j) =
      (n : ℤ) * (q + 1 : ℕ) := by
  rw [multiPairing_symm]
  exact graphPairing_sum_total q n a ha hproj

end KltDP.Examples.FrobeniusMultiCentreGraphTotalExceptionalRows
