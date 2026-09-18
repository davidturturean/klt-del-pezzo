import KltDP.Geometry.UnbranchedExceptionalBlockComponents
import KltDP.Geometry.KltExceptionalBlockTree
import KltDP.Geometry.OriginalUnbranchedRationalTreePrimeCurves

/-!
# The original cover contains both coherent copies of every unbranched block

The index contains all actual components of all original unbranched
exceptional blocks. Each copy is made by the checked whole-tree splitting
of the unchanged original ambient cover. Original component maps project
to their unchanged inclusions. Different original blocks have disjoint
lifted curves under any choices of sheet labels, by those projections.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace
universe u

namespace KltDP.Geometry.UnbranchedExceptionalBlocks

open NormalProjectiveSurface ActualExceptionalIncidence ExceptionalForestClosedBlocks RationalTreePicard

variable {k : Type u} [Field k] [IsAlgClosed k] {S X : NormalProjectiveSurface k}
    (π : S.toScheme ⟶ X.toScheme) (N : Finset S.PrimeCurve)
    [IsProper π] (hbir : IsBirationalScheme π)
    (hmin : IsMinimalResolution S X π) (hklt : IsKlt X)

local instance originalUnbranchedForestCopiesSeparated : S.toScheme.IsSeparated := surfaceSeparated S
local instance originalUnbranchedForestCopiesMonoidal : MonoidalCategory S.toScheme.Modules :=
  Scheme.Modules.monoidalCategory S.toScheme

variable (E : CartierDivisor S.toScheme) (hE : HasRegularCartierEquations S.toScheme E)
    (L : InvertibleSheaf S.toScheme)
    (e : L.obj ⊗ L.obj ≅ cartierDivisorModule S.toScheme E) (h2 : IsUnit (2 : k))
    (hred : IsReduced
      (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued)
    (hne : Nonempty
      (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued)
    (hIJ : effectiveCartierIdealDataOfRegularEquations S.toScheme E hE =
      Scheme.IdealSheafData.vanishingIdeal (S.selectedPrimeClosedUnion N))
    (hiso : IsolatedSelection π N)

local notation "CoverSurface" =>
  OriginalCartierQuadraticIntegral.normalProjectiveSurface S E hE L e h2 hred hne
local notation "CoverAtlas" => effectiveCartierQuadraticAtlas S.toScheme E hE L e

/-- The actual prime curve on the unchanged cover for a component in any retained block. -/
def forestCurve (ε : Bool) (i : Components π N hbir) : (CoverSurface).PrimeCurve :=
  OriginalUnbranchedRationalTreeGeometry.liftedCurve S
    (blockInclusion π hbir i.1.val ≫ S.structureMorphism)
    (blockScheme_dimension_le_one π hbir i.1.val)
    (block_componentPointIncidenceGraph_isTree π hbir i.1.val hmin hklt)
    (block_hasTransverseComponentBranches π hbir i.1.val hmin hklt)
    (blockComponentProjectiveLineIso π hbir i.1.val hmin hklt)
    E hE L e h2 hred hne (blockInclusion π hbir i.1.val)
    (blockInclusion_disjoint_canonicalBranch π N hiso hbir E hE hIJ i.1) ε i.2

/-- The original component-source map defining each actual coherent forest copy. -/
def forestPrimeLift (ε : Bool) (i : Components π N hbir) :
    (baseCurve π N hbir hmin hklt i).toScheme ⟶ (CoverAtlas).scheme :=
  OriginalUnbranchedRationalTreeGeometry.primeLift S
    (blockInclusion π hbir i.1.val ≫ S.structureMorphism)
    (blockScheme_dimension_le_one π hbir i.1.val)
    (block_componentPointIncidenceGraph_isTree π hbir i.1.val hmin hklt)
    (block_hasTransverseComponentBranches π hbir i.1.val hmin hklt)
    (blockComponentProjectiveLineIso π hbir i.1.val hmin hklt)
    E hE L e h2 (blockInclusion π hbir i.1.val)
    (blockInclusion_disjoint_canonicalBranch π N hiso hbir E hE hIJ i.1) ε i.2

instance forestPrimeLift_isClosedImmersion (ε : Bool) (i : Components π N hbir) :
    IsClosedImmersion (forestPrimeLift π N hbir hmin hklt E hE L e h2 hIJ hiso ε i) := by
  dsimp only [forestPrimeLift]
  infer_instance

@[reassoc]
theorem forestPrimeLift_projection (ε : Bool) (i : Components π N hbir) :
    forestPrimeLift π N hbir hmin hklt E hE L e h2 hIJ hiso ε i ≫ (CoverAtlas).morphism =
      (baseCurve π N hbir hmin hklt i).inclusion :=
  OriginalUnbranchedRationalTreeGeometry.primeLift_projection S
    (blockInclusion π hbir i.1.val ≫ S.structureMorphism)
    (blockScheme_dimension_le_one π hbir i.1.val)
    (block_componentPointIncidenceGraph_isTree π hbir i.1.val hmin hklt)
    (block_hasTransverseComponentBranches π hbir i.1.val hmin hklt)
    (blockComponentProjectiveLineIso π hbir i.1.val hmin hklt)
    E hE L e h2 (blockInclusion π hbir i.1.val)
    (blockInclusion_disjoint_canonicalBranch π N hiso hbir E hE hIJ i.1) ε i.2

/-- The retained actual forest prime is the closed image of its original component map. -/
theorem forestCurve_eq_closedImage (ε : Bool) (i : Components π N hbir) :
    (baseCurve π N hbir hmin hklt i).closedImage (T := CoverSurface)
      (forestPrimeLift π N hbir hmin hklt E hE L e h2 hIJ hiso ε i) =
        forestCurve π N hbir hmin hklt E hE L e h2 hred hne hIJ hiso ε i :=
  OriginalUnbranchedRationalTreeGeometry.closedImage_primeLift S
    (blockInclusion π hbir i.1.val ≫ S.structureMorphism)
    (blockScheme_dimension_le_one π hbir i.1.val)
    (block_componentPointIncidenceGraph_isTree π hbir i.1.val hmin hklt)
    (block_hasTransverseComponentBranches π hbir i.1.val hmin hklt)
    (blockComponentProjectiveLineIso π hbir i.1.val hmin hklt)
    E hE L e h2 hred hne (blockInclusion π hbir i.1.val)
    (blockInclusion_disjoint_canonicalBranch π N hiso hbir E hE hIJ i.1) ε i.2

/-- Each actual cover prime projects onto exactly its original exceptional prime. -/
theorem forestCurve_image_projection (ε : Bool) (i : Components π N hbir) :
    (CoverAtlas).morphism.base ''
      (forestCurve π N hbir hmin hklt E hE L e h2 hred hne hIJ hiso ε i : Set (CoverSurface).toScheme) =
        (baseCurve π N hbir hmin hklt i : Set S.toScheme) := by
  rw [← forestCurve_eq_closedImage π N hbir hmin hklt E hE L e h2 hred hne hIJ hiso ε i,
    PrimeCurve.coe_closedImage, ← Set.range_comp]
  change Set.range (forestPrimeLift π N hbir hmin hklt E hE L e h2 hIJ hiso ε i ≫
    (CoverAtlas).morphism).base = _
  rw [forestPrimeLift_projection, PrimeCurve.range_inclusion]

/-- Components from distinct original blocks are disjoint on the unchanged cover for all labels. -/
theorem forestCurve_disjoint_blocks (ε δ : Bool) (i j : Components π N hbir) (hij : i.1 ≠ j.1) :
    Disjoint
      (forestCurve π N hbir hmin hklt E hE L e h2 hred hne hIJ hiso ε i : Set (CoverSurface).toScheme)
      (forestCurve π N hbir hmin hklt E hE L e h2 hred hne hIJ hiso δ j : Set (CoverSurface).toScheme) := by
  apply Disjoint.of_image (f := (CoverAtlas).morphism.base)
  rw [forestCurve_image_projection, forestCurve_image_projection]
  exact baseCurve_disjoint_of_block_ne π N hbir hmin hklt i j hij

end KltDP.Geometry.UnbranchedExceptionalBlocks

#print axioms KltDP.Geometry.UnbranchedExceptionalBlocks.forestPrimeLift_projection
#print axioms KltDP.Geometry.UnbranchedExceptionalBlocks.forestCurve_disjoint_blocks
