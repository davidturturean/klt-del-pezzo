import KltDP.Geometry.PrimeCurveBigness
import KltDP.Geometry.BignessIsomorphism
import KltDP.Geometry.SurfaceIrreducibleClosedDimension
import KltDP.Geometry.IntersectionPairingSymmetry

/-!
# The exceptional locus of an actual nef and big surface line bundle

The original reduced whole-surface subvariety is isomorphic to the surface,
so bigness excludes it from the exceptional subvarieties. Every other
positive-dimensional irreducible closed subset is an actual prime curve.
The proved curve bigness comparison therefore identifies the original
exceptional locus with the closure of the actual zero-degree curve union.
No finite-rank, Hodge, or null-curve finiteness premise is needed.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology
universe u

namespace KltDP.Geometry.NefBigNullLocus

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : NormalProjectiveSurface k) (L : InvertibleSheaf X.toScheme)

private theorem whole_subvariety_isBig (hbig : Positivity.IsBig X.structureMorphism L)
    (Z : IrreducibleCloseds X.toScheme) (hZ : (Z : Set X.toScheme) = Set.univ) :
    Positivity.IsBig (Positivity.inclusion Z ≫ X.structureMorphism)
      (pullbackInvertibleSheaf (Positivity.inclusion Z) L) := by
  letI : Surjective (Positivity.inclusion Z) :=
    ⟨Set.range_eq_univ.mp ((Positivity.range_inclusion Z).trans hZ)⟩
  letI : IsIso (Positivity.inclusion Z) :=
    isIso_of_isClosedImmersion_of_surjective (Positivity.inclusion Z)
  exact (BignessIsomorphism.isBig_pullback_iff
    (Positivity.inclusion Z) X.structureMorphism L).mpr hbig

/-- For the original nef and big line bundle, the exceptional locus is exactly
 the closure of the union of its original zero-degree prime curves. -/
theorem nullLocus_eq_closure_union (hnef : Positivity.IsNef X.structureMorphism L)
    (hbig : Positivity.IsBig X.structureMorphism L) :
    Positivity.nullLocus X.structureMorphism L =
      closure (⋃ C ∈ {C : X.PrimeCurve | C.restrictionDegree L = 0},
        (C : Set X.toScheme)) := by
  have hpos (Z : IrreducibleCloseds X.toScheme)
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
  have heq := X.nullLocus_eq_of_quantity L (1 : ℤ)
    (fun Z hZ => X.irreducibleClosed_dim_eq_one_or_eq_univ Z hZ) hpos
    (PrimeCurveBigness.isBig_subvariety_iff_degree_pos X L hnef)
    (fun Z hZ => ⟨fun _ => by decide, fun _ => whole_subvariety_isBig X L hbig Z hZ⟩)
    hnef (by decide)
  simpa only [one_ne_zero, Set.iUnion_of_empty, Set.union_empty] using heq

end KltDP.Geometry.NefBigNullLocus
