import KltDP.Examples.FrobeniusMultiCentreNullCurveClassification
import KltDP.Examples.FrobeniusMultiCentreContractingBig
import KltDP.Geometry.NefBigNullLocus

/-!
# The exact original reduced null locus of M

The complete prime-curve classification identifies the union with the
original graph, strict fibers, and old exceptional components. This finite
union of actual closed supports is already closed. The original nef-big
exceptional-locus comparison then proves equality with the independently
defined null locus. The range of the original reduced induced inclusion is identified by this exact equality.
This consumer inherits the existing private surface Riemann--Roch dependency
of the actual M-bigness proof; no contraction is asserted.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Examples.FrobeniusMultiCentreContractingNullLocus

open KltDP.Geometry KltDP.Geometry.NormalProjectiveSurface
open FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
open FrobeniusMultiCentreGraphFiber FrobeniusMultiCentreExceptional
open FrobeniusMultiCentreExceptionalPrime FrobeniusMultiCentreContractingNef
open FrobeniusMultiCentreSpecialNullCurves FrobeniusMultiCentreNullCurveClassification
open FrobeniusMultiCentreContractingBig

variable {k : Type u} [Field k] [IsAlgClosed k]
  (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
  (a : Fin n → k) (ha : Function.Injective a)
  (hproj : IsProjectiveOverField (multiStructure (q + 1) n a))

/-- The manuscript's original reduced divisor support D. -/
def contractingSupport : Set (multiSurfaceSurface (q + 1) n a ha hproj).toScheme :=
  (Set.range (graphStrictι (q + 1) n a).base ∪
    ⋃ i : Fin n, Set.range (fiberStrictι (q + 1) n a i).base) ∪
    ⋃ (i : Fin n) (j : Fin q), Set.range (exceptionalCurveι q n a i (.inl j)).base

/-- The actual finite support is closed before taking any closure. -/
theorem contractingSupport_isClosed : IsClosed (contractingSupport q n a ha hproj) :=
  ((graphStrictι (q + 1) n a).isClosedEmbedding.isClosed_range.union
    (isClosed_iUnion_of_finite fun i =>
      (fiberStrictι (q + 1) n a i).isClosedEmbedding.isClosed_range)).union
    (isClosed_iUnion_of_finite fun i => isClosed_iUnion_of_finite fun j =>
      (exceptionalCurveι q n a i (.inl j)).isClosedEmbedding.isClosed_range)

/-- The entire union of actual degree-zero prime curves is the original support. -/
theorem null_curve_union_eq_support (hn : 2 < n) :
    (⋃ C ∈ {C : (multiSurfaceSurface (q + 1) n a ha hproj).PrimeCurve |
        C.restrictionDegree (contractingLine q n a ha hproj) = 0},
      (C : Set (multiSurfaceSurface (q + 1) n a ha hproj).toScheme)) =
      contractingSupport q n a ha hproj := by
  ext x
  constructor
  · intro hx
    obtain ⟨C, hzero, hx⟩ := Set.mem_iUnion₂.mp hx
    rcases (restrictionDegree_eq_zero_iff q n a ha hproj hn C).mp hzero with
      rfl | ⟨i, rfl⟩ | ⟨i, j, rfl⟩
    · exact Or.inl (Or.inl hx)
    · exact Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨i, hx⟩))
    · exact Or.inr (Set.mem_iUnion₂.mpr ⟨i, j, hx⟩)
  · rintro ((hx | hx) | hx)
    · exact Set.mem_iUnion₂.mpr ⟨graphPrimeCurve q n a ha hproj,
        (restrictionDegree_eq_zero_iff q n a ha hproj hn _).mpr (Or.inl rfl), hx⟩
    · obtain ⟨i, hx⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion₂.mpr ⟨fiberPrimeCurve q n a ha hproj i,
        (restrictionDegree_eq_zero_iff q n a ha hproj hn _).mpr
          (Or.inr (Or.inl ⟨i, rfl⟩)), hx⟩
    · obtain ⟨i, j, hx⟩ := Set.mem_iUnion₂.mp hx
      exact Set.mem_iUnion₂.mpr ⟨exceptionalPrimeCurveSPn q n a ha i (.inl j) hproj,
        (restrictionDegree_eq_zero_iff q n a ha hproj hn _).mpr
          (Or.inr (Or.inr ⟨i, j, rfl⟩)), hx⟩

/-- The independently defined original exceptional locus of M is exactly D. -/
theorem nullLocus_eq_support (hn : 2 < n) :
    Positivity.nullLocus (multiStructure (q + 1) n a) (contractingLine q n a ha hproj) =
      contractingSupport q n a ha hproj := by
  have h := NefBigNullLocus.nullLocus_eq_closure_union
    (multiSurfaceSurface (q + 1) n a ha hproj) (contractingLine q n a ha hproj)
    (contractingLine_isNef q n a ha hproj hn.le)
    (contractingLine_isBig q n a ha hproj hn)
  exact h.trans ((congrArg closure (null_curve_union_eq_support q n a ha hproj hn)).trans
    (contractingSupport_isClosed q n a ha hproj).closure_eq)

/-- The original null-locus inclusion has precisely the original divisor support as its range. -/
theorem nullLocusInclusion_range (hn : 2 < n) :
    Set.range (Positivity.nullLocusInclusion (multiStructure (q + 1) n a)
      (contractingLine q n a ha hproj)).base = contractingSupport q n a ha hproj := by
  have h : Set.range (Positivity.nullLocusInclusion (multiStructure (q + 1) n a)
      (contractingLine q n a ha hproj)).base =
      Positivity.nullLocus (multiStructure (q + 1) n a) (contractingLine q n a ha hproj) :=
    (Scheme.IdealSheafData.vanishingIdeal
      (Positivity.nullLocusClosed (multiStructure (q + 1) n a)
        (contractingLine q n a ha hproj))).range_gluedTo
  exact h.trans (nullLocus_eq_support q n a ha hproj hn)

end KltDP.Examples.FrobeniusMultiCentreContractingNullLocus
