import KltDP.Geometry.PrimeCurveBigness
import KltDP.Geometry.BignessIsomorphism
import KltDP.Geometry.SurfaceIrreducibleClosedDimension
import KltDP.Geometry.PositiveSquareNullCurveLocus
import KltDP.Geometry.NefPositiveSelfIntersectionBig

/-!
# The actual exceptional locus of a nef line bundle of positive square

The whole smooth surface is big by the original Riemann--Roch section-growth
argument. Proper positive-dimensional irreducible closed subsets are actual
prime curves, and the curve bigness theorem identifies their exceptionalness
with degree zero. The original exceptional-locus definition is therefore the
finite union of the actual degree-zero curves; its closure adds no points.
All dimension, bigness, and closedness comparisons are constructed here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology

universe u

namespace KltDP.Geometry.PositiveSquareNefNullLocus

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)

/-- The original reduced whole-surface closed immersion is an actual
scheme isomorphism, since the original surface is reduced. -/
theorem inclusion_isIso_of_eq_univ (Z : IrreducibleCloseds X.toScheme)
    (hZ : (Z : Set X.toScheme) = Set.univ) : IsIso (Positivity.inclusion Z) := by
  letI : Surjective (Positivity.inclusion Z) :=
    ⟨Set.range_eq_univ.mp ((Positivity.range_inclusion Z).trans hZ)⟩
  exact isIso_of_isClosedImmersion_of_surjective (Positivity.inclusion Z)

/-- The one-dimensional and whole-surface cases have positive actual
topological dimension, with no dimension comparison supplied as a premise. -/
theorem dim_pos_of_one_or_univ (Z : IrreducibleCloseds X.toScheme)
    (hZ : topologicalKrullDim (Z : Set X.toScheme) = 1 ∨
      (Z : Set X.toScheme) = Set.univ) :
    0 < topologicalKrullDim (Z : Set X.toScheme) := by
  rcases hZ with hZ | hZ
  · rw [hZ]
    norm_num
  · rw [hZ, IsHomeomorph.topologicalKrullDim_eq
      (Homeomorph.Set.univ X.toScheme) (Homeomorph.Set.univ X.toScheme).isHomeomorph,
      X.dimension_two]
    norm_num

/-- Actual bigness transports to the original whole-surface subvariety
through its proved scheme isomorphism and original composite base map. -/
theorem whole_subvariety_isBig (L : InvertibleSheaf X.toScheme)
    (hbig : Positivity.IsBig X.structureMorphism L)
    (Z : IrreducibleCloseds X.toScheme) (hZ : (Z : Set X.toScheme) = Set.univ) :
    Positivity.IsBig (Positivity.inclusion Z ≫ X.structureMorphism)
      (pullbackInvertibleSheaf (Positivity.inclusion Z) L) := by
  letI := inclusion_isIso_of_eq_univ X Z hZ
  exact (BignessIsomorphism.isBig_pullback_iff
    (Positivity.inclusion Z) X.structureMorphism L).mpr hbig

section Smooth

variable [IsSmoothOfRelativeDimension 2 X.structureMorphism]

local instance source_isSmooth : IsSmooth X.structureMorphism :=
  IsSmoothOfRelativeDimension.isSmooth 2 X.structureMorphism

/-- For the original smooth projective surface and original nef line bundle
of positive square, the existing null locus is exactly the finite union
of its actual degree-zero prime curves. -/
theorem nullLocus_eq_union (L : InvertibleSheaf X.toScheme)
    (hnef : Positivity.IsNef X.structureMorphism L)
    (hpositive : 0 < X.selfIntersection X.regularPoints_of_isSmooth L) :
    Positivity.nullLocus X.structureMorphism L =
      ⋃ C ∈ {C : X.PrimeCurve | C.restrictionDegree L = 0}, (C : Set X.toScheme) := by
  have hbig := NefPositiveSelfIntersectionBig.isBig X L hnef hpositive
  have heq := X.nullLocus_eq_of_quantity L (X.selfIntersection X.regularPoints_of_isSmooth L)
    (fun Z hZ => X.irreducibleClosed_dim_eq_one_or_eq_univ Z hZ)
    (dim_pos_of_one_or_univ X)
    (PrimeCurveBigness.isBig_subvariety_iff_degree_pos X L hnef)
    (fun Z hZ => ⟨fun _ => hpositive, fun _ => whole_subvariety_isBig X L hbig Z hZ⟩)
    hnef hpositive.le
  have hempty :
      (⋃ (_ : X.selfIntersection X.regularPoints_of_isSmooth L = 0),
        (Set.univ : Set X.toScheme)) = ∅ := by
    simp only [ne_of_gt hpositive, Set.iUnion_of_empty]
  rw [hempty, Set.union_empty,
    PositiveSquareNullCurveLocus.closure_union X X.regularPoints_of_isSmooth L hpositive] at heq
  exact heq

end Smooth

end KltDP.Geometry.PositiveSquareNefNullLocus
