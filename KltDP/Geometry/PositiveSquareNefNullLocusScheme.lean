import KltDP.Geometry.PositiveSquareNefNullLocus
import KltDP.Geometry.PositiveSquareNullCurveLocus
import KltDP.Geometry.PrimeCurveCodimension

/-!
# Dimension, reducedness, and projectivity of the actual null-locus scheme

The proved finite union description excludes the original surface's generic
point: no proper closed prime curve contains it. The existing proper-closed
dimension bound therefore applies, without new finite-union dimension
machinery. The original quotient-chart support homeomorphism transfers this
bound to `Positivity.nullLocusScheme`. Its radical vanishing ideal proves
reducedness, and its original closed immersion inherits a projective embedding
over the same field. The empty null locus is included.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.PositiveSquareNefNullLocusScheme

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)

/-- The actual null-locus inclusion has exactly the original null locus as
its range. -/
theorem range_inclusion (L : InvertibleSheaf X.toScheme) :
    Set.range (Positivity.nullLocusInclusion X.structureMorphism L).base =
      Positivity.nullLocus X.structureMorphism L :=
  (Scheme.IdealSheafData.vanishingIdeal
    (Positivity.nullLocusClosed X.structureMorphism L)).range_gluedTo

/-- The actual glued scheme has the subspace topology of the original locus. -/
def underlyingHomeomorph (L : InvertibleSheaf X.toScheme) :
    Positivity.nullLocusScheme X.structureMorphism L ≃ₜ
      Positivity.nullLocus X.structureMorphism L :=
  (Scheme.IdealSheafData.vanishingIdeal
    (Positivity.nullLocusClosed X.structureMorphism L)).gluedSupportHomeomorph

/-- The radical original vanishing ideal gives reducedness for the actual
null-locus scheme, independently of the positivity hypotheses. -/
instance isReduced (L : InvertibleSheaf X.toScheme) :
    AlgebraicGeometry.IsReduced (Positivity.nullLocusScheme X.structureMorphism L) := by
  let I := Scheme.IdealSheafData.vanishingIdeal
    (Positivity.nullLocusClosed X.structureMorphism L)
  exact I.glued_isReduced (Scheme.IdealSheafData.vanishingIdeal_support (I := I)).symm

/-- The original null-locus inclusion inherits the original projective
embedding, with the actual composite structure morphism. -/
theorem projective (L : InvertibleSheaf X.toScheme) :
    IsProjectiveOverField
      (Positivity.nullLocusInclusion X.structureMorphism L ≫ X.structureMorphism) := by
  obtain ⟨n, i, hi, hcomp⟩ := X.projective
  letI : IsClosedImmersion i := hi
  refine ⟨n, Positivity.nullLocusInclusion X.structureMorphism L ≫ i,
    inferInstance, ?_⟩
  rw [Category.assoc, hcomp]

private theorem surface_genericPoint_not_mem_primeCurve (C : X.PrimeCurve) :
    _root_.genericPoint X.toScheme ∉ (C : Set X.toScheme) := by
  intro hmem
  have hsubset : closure ({_root_.genericPoint X.toScheme} : Set X.toScheme) ⊆ C :=
    closure_minimal (Set.singleton_subset_iff.mpr hmem) C.isClosed
  rw [genericPoint_closure] at hsubset
  exact C.ne_univ (Set.eq_univ_of_univ_subset hsubset)

section Smooth

variable [IsSmoothOfRelativeDimension 2 X.structureMorphism]

local instance source_isSmooth : IsSmooth X.structureMorphism :=
  IsSmoothOfRelativeDimension.isSmooth 2 X.structureMorphism

/-- The actual null locus is proper, by its proved union of actual prime curves. -/
theorem nullLocus_ne_univ (L : InvertibleSheaf X.toScheme)
    (hnef : Positivity.IsNef X.structureMorphism L)
    (hpositive : 0 < X.selfIntersection X.regularPoints_of_isSmooth L) :
    Positivity.nullLocus X.structureMorphism L ≠ Set.univ := by
  rw [PositiveSquareNefNullLocus.nullLocus_eq_union X L hnef hpositive]
  intro hfull
  have hmem : _root_.genericPoint X.toScheme ∈
      ⋃ C ∈ {C : X.PrimeCurve | C.restrictionDegree L = 0}, (C : Set X.toScheme) := by
    rw [hfull]
    exact Set.mem_univ _
  obtain ⟨C, hmem⟩ := Set.mem_iUnion.mp hmem
  obtain ⟨_, hmem⟩ := Set.mem_iUnion.mp hmem
  exact surface_genericPoint_not_mem_primeCurve X C hmem

/-- The actual reduced null-locus scheme has dimension at most one;
the empty case is permitted by topological Krull dimension. -/
theorem dimension_le_one (L : InvertibleSheaf X.toScheme)
    (hnef : Positivity.IsNef X.structureMorphism L)
    (hpositive : 0 < X.selfIntersection X.regularPoints_of_isSmooth L) :
    topologicalKrullDim (Positivity.nullLocusScheme X.structureMorphism L) ≤ 1 := by
  rw [IsHomeomorph.topologicalKrullDim_eq (underlyingHomeomorph X L)
    (underlyingHomeomorph X L).isHomeomorph]
  exact KltDP.Topology.topologicalKrullDim_le_one_of_isClosed_of_ne_univ
    X.dimension_two.le (Positivity.isClosed_nullLocus X.structureMorphism L)
    (nullLocus_ne_univ X L hnef hpositive)

/-- All three conclusions concern the original null-locus scheme and map. -/
theorem dimension_reduced_projective (L : InvertibleSheaf X.toScheme)
    (hnef : Positivity.IsNef X.structureMorphism L)
    (hpositive : 0 < X.selfIntersection X.regularPoints_of_isSmooth L) :
    topologicalKrullDim (Positivity.nullLocusScheme X.structureMorphism L) ≤ 1 ∧
      AlgebraicGeometry.IsReduced (Positivity.nullLocusScheme X.structureMorphism L) ∧
      IsProjectiveOverField
        (Positivity.nullLocusInclusion X.structureMorphism L ≫ X.structureMorphism) :=
  ⟨dimension_le_one X L hnef hpositive, inferInstance, projective X L⟩

end Smooth

end KltDP.Geometry.PositiveSquareNefNullLocusScheme
