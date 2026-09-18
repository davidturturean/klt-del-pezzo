import KltDP.Geometry.OriginalUnbranchedForestCopies
import KltDP.Geometry.OriginalUnbranchedTreeRamificationDisjoint

/-!
# Every component of the complete doubled forest survives ramification blowdown

The branch-disjointness proof is derived for every original retained block.
The checked actual tree-copy theorem then shows that every actual component
under both coherent labels misses every original ramification prime.
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

local instance originalUnbranchedForestAvoidanceSeparated : S.toScheme.IsSeparated := surfaceSeparated S
local instance originalUnbranchedForestAvoidanceMonoidal : MonoidalCategory S.toScheme.Modules :=
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

/-- Every actual component of every coherent retained forest sheet avoids all ramification primes. -/
theorem forestCurve_disjoint_ramification (ε : Bool) (i : Components π N hbir) :
    ∀ P ∈ S.selectedRamificationPrimeSet N E hE L e h2 hred hne hIJ,
      Disjoint
        (forestCurve π N hbir hmin hklt E hE L e h2 hred hne hIJ hiso ε i : Set (CoverSurface).toScheme)
        (P : Set (CoverSurface).toScheme) :=
  OriginalUnbranchedRationalTreeGeometry.liftedCurve_disjoint_selectedRamification S
    (blockInclusion π hbir i.1.val ≫ S.structureMorphism)
    (blockScheme_dimension_le_one π hbir i.1.val)
    (block_componentPointIncidenceGraph_isTree π hbir i.1.val hmin hklt)
    (block_hasTransverseComponentBranches π hbir i.1.val hmin hklt)
    (blockComponentProjectiveLineIso π hbir i.1.val hmin hklt)
    E hE L e h2 hred hne (blockInclusion π hbir i.1.val)
    (blockInclusion_disjoint_canonicalBranch π N hiso hbir E hE hIJ i.1) N hIJ ε i.2

end KltDP.Geometry.UnbranchedExceptionalBlocks

#print axioms KltDP.Geometry.UnbranchedExceptionalBlocks.forestCurve_disjoint_ramification
