import KltDP.Geometry.KltExceptionalBlockTransversal
import KltDP.Geometry.ExceptionalForestBlockDimension
import KltDP.Geometry.RationalComponentPrimeCurves
import KltDP.Geometry.ProjectiveProper

/-!
# The original exceptional blocks as proper rational trees

These ordinary corollaries expose the actual block scheme's connectedness,
proper structure morphism, separatedness, and original reduced rational
components. Any component prime constructed from those schemes is proved
equal to the corresponding original exceptional prime.
-/

set_option autoImplicit false

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

namespace KltDP.Geometry.ExceptionalForestClosedBlocks

open RationalTreePicard

variable {k : Type u} [Field k] [IsAlgClosed k] {S X : NormalProjectiveSurface k}
  (π : S.toScheme ⟶ X.toScheme) [IsProper π] (hbir : IsBirationalScheme π)
  (b : (ActualExceptionalIncidence.graph π).ConnectedComponent)

instance blockScheme_connectedSpace : ConnectedSpace (blockScheme π hbir b) := by
  letI : ConnectedSpace (blockSupport π b) := Subtype.connectedSpace
    (KltDP.Topology.IncidenceGraphComponents.block_connected
      (fun E : ActualExceptionalIncidence.Vertices π => (E.val : Set S.toScheme))
      (fun E => E.val.isIrreducible.isConnected) b)
  exact (blockHomeomorph π hbir b).symm.surjective.connectedSpace
    (blockHomeomorph π hbir b).symm.continuous

instance blockToSpec_isProper :
    IsProper (blockInclusion π hbir b ≫ S.structureMorphism) := by infer_instance

instance blockScheme_isSeparated : (blockScheme π hbir b).IsSeparated := by
  constructor
  rw [← CategoryTheory.Limits.terminal.comp_from (blockInclusion π hbir b ≫ S.structureMorphism)]
  infer_instance

/-- The original reduced component scheme is the projective line over the same field. -/
def blockComponentProjectiveLineIso (hmin : IsMinimalResolution S X π) (hklt : IsKlt X)
    (D : ↥(irreducibleComponents (blockScheme π hbir b))) :
    componentUnionScheme (blockScheme π hbir b) {D} ≅ projectiveSpace k 1 := by
  letI : Finite (ActualExceptionalIncidence.Vertices π) :=
    ActualExceptionalIncidence.finite_vertices π hbir
  letI : Fintype b.supp := Fintype.ofFinite _
  let Cv : b.supp → Scheme.{u} := fun E => E.val.val.toScheme
  let hint : ∀ E, IsIntegral (Cv E) := fun _ => inferInstance
  let E := curveOf (blockScheme π hbir b) Cv (blockCurve π hbir b) hint
    (blockCurve_cover π hbir b) (blockCurve_incomparable π hbir b) D
  exact curveIdentification (blockScheme π hbir b) Cv (blockCurve π hbir b) hint
    (blockCurve_cover π hbir b) (blockCurve_incomparable π hbir b) D ≪≫
      (hmin.toIsResolution.exceptional_projectiveLine_iso_of_klt
        hklt E.val.val E.val.property).choose

/-- The actual transverse-branches interface follows from the original klt crossing proof. -/
theorem block_hasTransverseComponentBranches
    (hmin : IsMinimalResolution S X π) (hklt : IsKlt X) :
    HasTransverseComponentBranches (blockScheme π hbir b) :=
  hasTransverseComponentBranches_of_transversalConfiguration
    (blockInclusion π hbir b) (block_transversalConfiguration π hbir b hmin hklt)

/-- The component prime used by a cover is precisely the original exceptional prime.
This does not depend on which actual projective-line isomorphisms were chosen. -/
theorem block_componentPrime_eq_original
    (eC : ∀ D : ↥(irreducibleComponents (blockScheme π hbir b)),
      componentUnionScheme (blockScheme π hbir b) {D} ≅ projectiveSpace k 1)
    (D : ↥(irreducibleComponents (blockScheme π hbir b))) :
    RationalComponentPrimeCurves.curve S (blockInclusion π hbir b) eC D =
      ((blockComponentEquiv π hbir b).symm D).val.val := by
  apply NormalProjectiveSurface.PrimeCurve.ext
  have hD := congrArg Subtype.val ((blockComponentEquiv π hbir b).apply_symm_apply D)
  rw [blockComponentEquiv_val] at hD
  change Set.range ((blockInclusion π hbir b).base ∘
    (componentUnionInclusion (blockScheme π hbir b) {D}).base) = _
  rw [Set.range_comp, range_componentUnionInclusion, coe_componentClosedUnion_singleton,
    ← hD, ← Set.range_comp, ← TopCat.coe_comp, ← Scheme.comp_base,
    blockCurve_inclusion, NormalProjectiveSurface.PrimeCurve.range_inclusion]

end KltDP.Geometry.ExceptionalForestClosedBlocks

#check @KltDP.Geometry.ExceptionalForestClosedBlocks.blockComponentProjectiveLineIso
#print axioms KltDP.Geometry.ExceptionalForestClosedBlocks.blockScheme_connectedSpace
#print axioms KltDP.Geometry.ExceptionalForestClosedBlocks.block_componentPrime_eq_original
