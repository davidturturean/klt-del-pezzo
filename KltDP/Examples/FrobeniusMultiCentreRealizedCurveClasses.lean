import KltDP.Examples.FrobeniusMultiCentrePicardRealization

/-!
# The lattice realization carries the named vectors to the original curve classes

These comparisons use the original global kernel-line Picard identities.
In particular the graph, strict fibres and chain components are not defined
by the lattice vectors; they are the previously constructed embedded curves.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Examples.FrobeniusMultiCentreRealizedCurveClasses

open KltDP.Geometry
open FrobeniusMultiCentreSurface FrobeniusMultiCentreExceptionalGlobalClasses
  FrobeniusMultiCentreGraphCartierStrict FrobeniusMultiCentreGraphPicardClass
  FrobeniusMultiCentreFiberGlobalClass FrobeniusMultiCentrePicardRealization

variable {k : Type u} [Field k] (q n : ℕ) (a : Fin n → k)

theorem realization_firstFiber :
    realization q n a (FrobeniusPicard.a : FrobeniusPicard.PicardVector (q + 1) n) =
      multiFirstFiberClass (q + 1) n a := by
  simp [realization_apply, FrobeniusPicard.a]

theorem realization_secondFiber :
    realization q n a (FrobeniusPicard.b : FrobeniusPicard.PicardVector (q + 1) n) =
      multiSecondFiberClass (q + 1) n a := by
  simp [realization_apply, FrobeniusPicard.b]

theorem realization_exceptional (i : Fin n) (j : Fin (q + 1)) :
    realization q n a (FrobeniusPicard.exceptional (i, j)) =
      exceptionalClass (q + 1) n a i j := by
  classical
  simp [realization_apply, FrobeniusPicard.exceptional, Prod.mk.injEq, ite_and, ite_smul]

variable [IsAlgClosed k] (ha : Function.Injective a)
  [Fact (q + 1).Prime] [CharP k (q + 1)]

/-- The accepted graph vector realizes the class of the original strict-graph kernel. -/
theorem realization_graphVector :
    realization q n a (FrobeniusPicard.graphVector (q + 1) n) =
      -Additive.ofMul (multiGraphStrictKernelLine q n a ha).toPic := by
  rw [realization_apply, strictGraphKernelLine_picard_row]
  change ((q + 1 : ℕ) : ℤ) • multiFirstFiberClass (q + 1) n a +
      (1 : ℤ) • multiSecondFiberClass (q + 1) n a +
      (∑ i : Fin n, ∑ j : Fin (q + 1), (-1 : ℤ) • exceptionalClass (q + 1) n a i j) = _
  simp only [natCast_zsmul, one_zsmul, neg_one_zsmul, Finset.sum_neg_distrib, sub_eq_add_neg]

/-- The accepted fibre vector realizes the class of the original strict-fibre kernel. -/
theorem realization_fiberVector (i : Fin n) :
    realization q n a (FrobeniusPicard.fiberVector (q + 1) n i) =
      -Additive.ofMul (fiberKernelLine q n a ha i).toPic := by
  classical
  rw [realization_apply, fiberClass_SPn]
  change (0 : ℤ) • multiFirstFiberClass (q + 1) n a +
      (1 : ℤ) • multiSecondFiberClass (q + 1) n a +
      (∑ i' : Fin n, ∑ j : Fin (q + 1),
        (if i' = i then (-1 : ℤ) else 0) • exceptionalClass (q + 1) n a i' j) = _
  simp [ite_smul, Finset.sum_neg_distrib, sub_eq_add_neg]

omit [Fact (q + 1).Prime] [CharP k (q + 1)] in
/-- The original old component is the realization of the consecutive exceptional difference. -/
theorem realization_chainVector (i : Fin n) (j : Fin q) :
    realization q n a
      (FrobeniusPicard.chainVector (q + 1) n i j.castSucc
        (by simpa only [Fin.coe_castSucc] using Nat.succ_lt_succ j.isLt)) =
      -Additive.ofMul (exceptionalKernelLine q n a ha i (.inl j)).toPic := by
  rw [FrobeniusPicard.chainVector, FrobeniusPicard.exceptionalDifference, map_sub,
    realization_exceptional, realization_exceptional]
  exact (chainClass_SPn q n a ha i j).symm

omit [Fact (q + 1).Prime] [CharP k (q + 1)] in
/-- At characteristic-two tower length, the node vector realizes the actual old exceptional curve. -/
theorem realization_nodeVector (i : Fin n) :
    realization 1 n a (FrobeniusPicard.nodeVector n i) =
      -Additive.ofMul (exceptionalKernelLine 1 n a ha i (.inl (0 : Fin 1))).toPic := by
  rw [FrobeniusPicard.nodeVector, FrobeniusPicard.exceptionalDifference, map_sub,
    realization_exceptional, realization_exceptional]
  exact (chainClass_SPn 1 n a ha i (0 : Fin 1)).symm

end KltDP.Examples.FrobeniusMultiCentreRealizedCurveClasses
