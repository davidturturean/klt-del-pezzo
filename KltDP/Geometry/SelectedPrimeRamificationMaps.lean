import KltDP.Geometry.SelectedPrimeCanonicalBranchMap
import KltDP.Geometry.OriginalCartierRamificationCurveLift

/-!
# The selected original curves have actual ramification copies

The original selected-ideal equality constructs each map to the canonical
branch and derives its reducedness. The proved global ramification
isomorphism then supplies the actual closed immersion into the same
original quadratic cover. Its projection is the original curve inclusion.
Disjointness follows from the original selected curves themselves.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace
universe u

namespace KltDP.Geometry.NormalProjectiveSurface

open OriginalCartierRamificationSmooth

variable {k : Type u} [Field k] (S : NormalProjectiveSurface k)

local instance selectedPrimeRamificationMapsSeparated : S.toScheme.IsSeparated := surfaceSeparated S
local instance selectedPrimeRamificationMapsMonoidal : MonoidalCategory S.toScheme.Modules :=
  Scheme.Modules.monoidalCategory S.toScheme

variable (N : Finset S.PrimeCurve) (E : CartierDivisor S.toScheme)
    (hE : HasRegularCartierEquations S.toScheme E) (L : InvertibleSheaf S.toScheme)
    (e : L.obj ⊗ L.obj ≅ cartierDivisorModule S.toScheme E)
    (hIJ : effectiveCartierIdealDataOfRegularEquations S.toScheme E hE =
      Scheme.IdealSheafData.vanishingIdeal (S.selectedPrimeClosedUnion N))

/-- The selected original curve's actual ramification copy in the original cover. -/
def selectedPrimeRamificationMap (C : {C : S.PrimeCurve // C ∈ N}) :
    C.val.toScheme ⟶ (effectiveCartierQuadraticAtlas S.toScheme E hE L e).scheme :=
  ramificationCurveLift S.toScheme E hE L e
    (S.canonicalBranch_isReduced_of_selectedIdealEq N E hE hIJ)
    (S.selectedPrimeCanonicalBranchMap N E hE hIJ C)

@[reassoc]
theorem selectedPrimeRamificationMap_toBase (C : {C : S.PrimeCurve // C ∈ N}) :
    S.selectedPrimeRamificationMap N E hE L e hIJ C ≫
      (effectiveCartierQuadraticAtlas S.toScheme E hE L e).morphism = C.val.inclusion := by
  rw [selectedPrimeRamificationMap, ramificationCurveLift_toBase,
    selectedPrimeCanonicalBranchMap_toBase]

instance selectedPrimeRamificationMap_isClosedImmersion
    (C : {C : S.PrimeCurve // C ∈ N}) :
    IsClosedImmersion (S.selectedPrimeRamificationMap N E hE L e hIJ C) := by
  dsimp only [selectedPrimeRamificationMap]
  infer_instance

/-- The actual projected ramification image is the original selected curve. -/
theorem selectedPrimeRamificationMap_image_toBase (C : {C : S.PrimeCurve // C ∈ N}) :
    (effectiveCartierQuadraticAtlas S.toScheme E hE L e).morphism.base ''
      Set.range (S.selectedPrimeRamificationMap N E hE L e hIJ C).base =
      (C.val : Set S.toScheme) := by
  rw [← Set.range_comp, ← TopCat.coe_comp, ← Scheme.comp_base,
    selectedPrimeRamificationMap_toBase, C.val.range_inclusion]

/-- Original disjoint selected curves have disjoint actual ramification copies. -/
theorem selectedPrimeRamificationMaps_disjoint
    (hdisj : (N : Set S.PrimeCurve).Pairwise fun C D =>
      Disjoint (C : Set S.toScheme) (D : Set S.toScheme)) :
    Pairwise fun C D : {C : S.PrimeCurve // C ∈ N} =>
      Disjoint (Set.range (S.selectedPrimeRamificationMap N E hE L e hIJ C).base)
        (Set.range (S.selectedPrimeRamificationMap N E hE L e hIJ D).base) := by
  intro C D hCD
  apply disjoint_ramificationCurveLift_ranges
  rw [selectedPrimeCanonicalBranchMap_toBase, selectedPrimeCanonicalBranchMap_toBase,
    C.val.range_inclusion, D.val.range_inclusion]
  exact hdisj C.property D.property (fun h => hCD (Subtype.ext h))

end KltDP.Geometry.NormalProjectiveSurface

#print axioms KltDP.Geometry.NormalProjectiveSurface.selectedPrimeRamificationMap_toBase
#print axioms KltDP.Geometry.NormalProjectiveSurface.selectedPrimeRamificationMap_isClosedImmersion
#print axioms KltDP.Geometry.NormalProjectiveSurface.selectedPrimeRamificationMaps_disjoint
