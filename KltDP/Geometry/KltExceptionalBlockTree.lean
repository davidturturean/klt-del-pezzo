import KltDP.Geometry.ExceptionalForestBlockCurves
import KltDP.Geometry.ComponentPointTreeOfIncidence
import KltDP.Geometry.PrimeCurvePairingOnePoint
import KltDP.Geometry.KltMinimalResolutionGeometry
import KltDP.Geometry.KltResolutionExceptionalProjectiveLine

/-!
# The intrinsic component-point graph of an original klt exceptional block

The original exceptional forest identifies the component graph of the
actual reduced block as a tree. The actual pairing bound gives at most one
original point in every pair of distinct curves. The generic subdivision
lemma then proves the intrinsic component-point incidence graph is a tree.
-/

set_option autoImplicit false

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.ExceptionalForestClosedBlocks

variable {k : Type u} [Field k] [IsAlgClosed k] {S X : NormalProjectiveSurface k}
  (π : S.toScheme ⟶ X.toScheme) [IsProper π] (hbir : IsBirationalScheme π)
  (b : (ActualExceptionalIncidence.graph π).ConnectedComponent)

/-- The actual components and actual double points of the original block form a tree. -/
theorem block_componentPointIncidenceGraph_isTree
    (hmin : IsMinimalResolution S X π) (hklt : IsKlt X) :
    (RationalTreePicard.componentPointIncidenceGraph (blockScheme π hbir b)).IsTree := by
  letI : IsSmoothOfRelativeDimension 2 S.structureMorphism :=
    S.isSmoothOfRelativeDimension_two_of_regularPoints hmin.regular
  have hrational := hmin.toIsResolution.exceptional_projectiveLine_iso_of_klt hklt
  have hgeometry := hmin.exceptional_forest_and_singular_count_of_klt hklt hrational
  apply RationalTreePicard.componentPointIncidenceGraph_isTree_of_incidence
    (blockScheme π hbir b) (blockComponentGraph_isTree π hbir b hgeometry.2.2.1)
  intro C D hCD
  obtain ⟨E, rfl⟩ := (blockComponentEquiv π hbir b).surjective C
  obtain ⟨F, rfl⟩ := (blockComponentEquiv π hbir b).surjective D
  have hEF : E ≠ F := fun h => hCD (congrArg (blockComponentEquiv π hbir b) h)
  have hvertices : E.val ≠ F.val := fun h => hEF (Subtype.ext h)
  have hprimes : E.val.val ≠ F.val.val := fun h => hvertices (Subtype.ext h)
  have hpoint := PrimeCurvePairingSupport.intersectionPairing_primeCurves_le_one_inter_subsingleton
    S hmin.regular E.val.val F.val.val hprimes (hgeometry.2.2.2 E.val F.val hvertices)
  rw [blockComponentEquiv_val, blockComponentEquiv_val, range_blockCurve,
    range_blockCurve, ← Set.preimage_inter]
  exact hpoint.preimage (blockInclusion π hbir b).isClosedEmbedding.injective

end KltDP.Geometry.ExceptionalForestClosedBlocks

#check @KltDP.Geometry.ExceptionalForestClosedBlocks.block_componentPointIncidenceGraph_isTree
#print axioms KltDP.Geometry.ExceptionalForestClosedBlocks.block_componentPointIncidenceGraph_isTree
