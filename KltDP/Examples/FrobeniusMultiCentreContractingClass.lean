import KltDP.Examples.FrobeniusMultiCentreRetainedGram
import KltDP.Examples.FrobeniusMultiCentreRetainedPrimeCurves

/-!
# The original class M = B + (n-2)b and its actual geometric intersections

Define the class using the original embedded strict-graph kernel and the
original second ruling. The compiled original Picard realization identifies
this class with the existing nefVector; its previously proved lattice
calculations then give the actual geometric degrees. This file does not use
a canonical formula and does not assert nefness or construct a contraction.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusMultiCentreContractingClass

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open KltDP.Geometry.PrimeCurveClassPairing
open FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
open FrobeniusMultiCentreGraphCartierStrict FrobeniusMultiCentreFiberGlobalClass
open FrobeniusMultiCentreExceptionalGlobalClasses FrobeniusMultiCentreGraphExceptionalPairing
open FrobeniusMultiCentrePicardRealization FrobeniusMultiCentreRealizedCurveClasses
open FrobeniusMultiCentreRetainedGram FrobeniusMultiCentreRetainedPrimeCurves

variable {k : Type u} [Field k] [IsAlgClosed k]

section General

variable (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
  (a : Fin n → k) (ha : Function.Injective a)

/-- The manuscript's class, using the original graph and ruling classes. -/
def contractingClass : Additive (multiSurface (q + 1) n a).Pic :=
  -Additive.ofMul (multiGraphStrictKernelLine q n a ha).toPic +
    ((n : ℤ) - 2) • multiSecondFiberClass (q + 1) n a

/-- The original geometric class realizes the already calculated integral vector M. -/
theorem contractingClass_eq_realization :
    contractingClass q n a ha = realization q n a (FrobeniusPicard.nefVector (q + 1) n) := by
  simp only [FrobeniusPicard.nefVector_eq_graph_add, map_add, map_zsmul,
    realization_graphVector q n a ha, realization_secondFiber q n a, contractingClass]

variable (hproj : IsProjectiveOverField (multiStructure (q + 1) n a))

/-- Its actual square is p(n-2), with p=q+1 and subtraction in the integers. -/
theorem contractingClass_square :
    multiPairing (q + 1) n a ha hproj
        (contractingClass q n a ha) (contractingClass q n a ha) =
      ((q + 1 : ℕ) : ℤ) * ((n : ℤ) - 2) := by
  rw [contractingClass_eq_realization, realization_preserves_pairing]
  exact FrobeniusPicard.nef_square (q + 1) n

/-- The actual square is positive at more than two distinct centres. -/
theorem contractingClass_square_pos (hn : 2 < n) :
    0 < multiPairing (q + 1) n a ha hproj
      (contractingClass q n a ha) (contractingClass q n a ha) := by
  rw [contractingClass_square]
  have hn' : (2 : ℤ) < n := by exact_mod_cast hn
  exact mul_pos (by positivity) (sub_pos.mpr hn')

/-- The original graph has degree zero against this actual class. -/
theorem contractingClass_graph_pairing :
    multiPairing (q + 1) n a ha hproj (contractingClass q n a ha)
      (-Additive.ofMul (multiGraphStrictKernelLine q n a ha).toPic) = 0 := by
  rw [contractingClass_eq_realization, ← realization_graphVector q n a ha,
    realization_preserves_pairing]
  exact FrobeniusPicard.pairing_nef_graph (q + 1) n

/-- Every original strict tangent fibre has degree zero against this class. -/
theorem contractingClass_fiber_pairing (i : Fin n) :
    multiPairing (q + 1) n a ha hproj (contractingClass q n a ha)
      (-Additive.ofMul (fiberKernelLine q n a ha i).toPic) = 0 := by
  rw [contractingClass_eq_realization, ← realization_fiberVector q n a ha i,
    realization_preserves_pairing]
  exact FrobeniusPicard.pairing_nef_fiber (q + 1) n i

/-- Every original old exceptional component has degree zero against this class. -/
theorem contractingClass_old_pairing (i : Fin n) (j : Fin q) :
    multiPairing (q + 1) n a ha hproj (contractingClass q n a ha)
      (-Additive.ofMul (exceptionalKernelLine q n a ha i (.inl j)).toPic) = 0 := by
  rw [contractingClass_eq_realization, ← realization_chainVector q n a ha i j,
    realization_preserves_pairing, FrobeniusPicard.pairing_comm]
  exact FrobeniusPicard.pairing_chain_nef (q + 1) n i j.castSucc
    (by simpa only [Fin.coe_castSucc] using Nat.succ_lt_succ j.isLt)

/-- Every original total exceptional class has degree one against this class. -/
theorem contractingClass_totalExceptional_pairing (i : Fin n) (j : Fin (q + 1)) :
    multiPairing (q + 1) n a ha hproj (contractingClass q n a ha)
      (exceptionalClass (q + 1) n a i j) = 1 := by
  rw [contractingClass_eq_realization, ← realization_exceptional q n a i j,
    realization_preserves_pairing]
  exact FrobeniusPicard.pairing_nef_exceptional (q + 1) n i j

/-- In particular the original newest embedded exceptional curve has degree one. -/
theorem contractingClass_newest_pairing (i : Fin n) :
    multiPairing (q + 1) n a ha hproj (contractingClass q n a ha)
      (-Additive.ofMul (exceptionalKernelLine q n a ha i (.inr PUnit.unit)).toPic) = 1 := by
  rw [newestClass_SPn]
  exact contractingClass_totalExceptional_pairing q n a ha hproj i (Fin.last q)

end General

section CharacteristicTwo

variable [CharP k 2] (n : ℕ) (a : Fin n → k) (ha : Function.Injective a)
  (hproj : IsProjectiveOverField (multiStructure 2 n a))

local instance contractingClassPrimeTwo : Fact (1 + 1).Prime := ⟨Nat.prime_two⟩

/-- The actual class M is orthogonal to every original characteristic-two retained class. -/
theorem contractingClass_retained_pairing (r : FrobeniusCharacteristicTwo.RetainedLabel n) :
    multiPairing 2 n a ha hproj (contractingClass 1 n a ha) (retainedClass n a ha r) = 0 := by
  rw [contractingClass_eq_realization, retainedClass_eq_realization,
    realization_preserves_pairing]
  rcases r with r | (i | i)
  · exact FrobeniusPicard.pairing_nef_graph 2 n
  · exact FrobeniusPicard.pairing_nef_fiber 2 n i
  · exact (FrobeniusPicard.pairing_comm _ _).trans
      (FrobeniusCharacteristicTwo.node_nef_pairing n i)

/-- Orthogonality is also the actual restriction degree on each original retained prime. -/
theorem contractingClass_retained_primeDegree (r : FrobeniusCharacteristicTwo.RetainedLabel n) :
    (multiSurfaceSurface 2 n a ha hproj).picardRestrictionDegreeHom
      (retainedPrimeCurve n a ha hproj r) (contractingClass 1 n a ha) = 0 := by
  rw [← pairing_primeCurve_right (multiSurfaceSurface 2 n a ha hproj)
    (multiSurfaceSurface_regularPoints 2 n a ha hproj)
    (retainedPrimeCurve n a ha hproj r) (contractingClass 1 n a ha)]
  rw [retainedPrimeCurve_cartierClass]
  exact contractingClass_retained_pairing n a ha hproj r

end CharacteristicTwo

end KltDP.Examples.FrobeniusMultiCentreContractingClass
