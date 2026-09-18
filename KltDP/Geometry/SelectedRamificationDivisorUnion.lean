import KltDP.Geometry.SelectedRamificationPrimeSet
import KltDP.Geometry.SelectedPrimeCartierCanonicalIdeal
import KltDP.Geometry.OriginalCartierRamificationDivisor
import KltDP.Geometry.OriginalCartierQuadraticRegular

/-!
# The actual ramification divisor is the selected ramification curve divisor

The original ramification scheme is reduced by its proved isomorphism
with the original reduced branch. Its exact covered range identifies
its kernel with the vanishing ideal of the actual lifted-curve union.
Thus its actual Cartier divisor is the selected Cartier divisor of that
union. All local factoriality used for the selected Cartier construction
is derived from the proved regularity of this same original cover.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace
universe u

namespace KltDP.Geometry.NormalProjectiveSurface

open OriginalCartierRamificationSmooth

variable {k : Type u} [Field k] [IsAlgClosed k] (S : NormalProjectiveSurface k)

local instance selectedRamificationDivisorUnionSeparated : S.toScheme.IsSeparated := surfaceSeparated S
local instance selectedRamificationDivisorUnionMonoidal : MonoidalCategory S.toScheme.Modules :=
  Scheme.Modules.monoidalCategory S.toScheme

variable (N : Finset S.PrimeCurve) (E : CartierDivisor S.toScheme)
    (hE : HasRegularCartierEquations S.toScheme E) (L : InvertibleSheaf S.toScheme)
    (e : L.obj ⊗ L.obj ≅ cartierDivisorModule S.toScheme E) (h2 : IsUnit (2 : k))
    (hred : IsReduced
      (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued)
    (hne : Nonempty
      (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued)
    (hIJ : effectiveCartierIdealDataOfRegularEquations S.toScheme E hE =
      Scheme.IdealSheafData.vanishingIdeal (S.selectedPrimeClosedUnion N))

local notation "A" => effectiveCartierQuadraticAtlas S.toScheme E hE L e
local notation "T" => OriginalCartierQuadraticIntegral.normalProjectiveSurface S E hE L e h2 hred hne
local notation "M" => S.selectedRamificationPrimeSet N E hE L e h2 hred hne hIJ

local instance selectedRamificationDivisorUnionClosed : IsClosedImmersion (A).rootZeroGlobalι :=
  (A).rootZeroGlobalι_isClosedImmersion

/-- The canonical ideal of the actual ramification divisor is exactly the lifted union ideal. -/
theorem originalRamificationDivisor_selectedIdeal :
    effectiveCartierIdealDataOfRegularEquations (T).toScheme
      (originalRamificationDivisor S E hE L e h2 hred hne)
      (originalRamificationDivisor_hasRegularEquations S E hE L e h2 hred hne) =
        Scheme.IdealSheafData.vanishingIdeal ((T).selectedPrimeClosedUnion M) := by
  letI : IsReduced
      (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued := hred
  letI : IsReduced (A).rootZeroGlobalScheme :=
    isReduced_of_isOpenImmersion (rootZeroGlobalIsoCanonicalBranch S.toScheme E hE L e hred).hom
  rw [originalRamificationDivisor_ideal,
    ← SchematicImageDenseOpen.ker_radical (A).rootZeroGlobalι,
    ← Scheme.IdealSheafData.vanishingIdeal_support]
  apply congrArg Scheme.IdealSheafData.vanishingIdeal
  apply Closeds.ext
  rw [Scheme.Hom.support_ker, (A).rootZeroGlobalι.isClosedEmbedding.isClosed_range.closure_eq]
  exact (S.selectedRamificationPrimeSet_union N E hE L e h2 hred hne hIJ).symm

variable [IsSmooth S.structureMorphism]
    (hdisj : (N : Set S.PrimeCurve).Pairwise fun C D =>
      Disjoint (C : Set S.toScheme) (D : Set S.toScheme))
    (hcurves : ∀ C ∈ N, IsSmooth C.toSpec)

include hIJ hdisj hcurves in
/-- Original smooth selected curves give regular points on this same actual cover. -/
theorem selectedRamificationCover_regularPoints :
    ∀ y : (T).toScheme, RegularPoint (T).toScheme y := by
  apply regularPoints_of_smooth_base_and_branch S E hE L e h2 hred hne
  rw [hIJ]
  exact S.selectedPrimeUnion_isSmooth N hdisj hcurves

/-- The actual ramification divisor is exactly the Cartier divisor of its actual lifted curves. -/
theorem originalRamificationDivisor_eq_selectedCartier :
    letI := (T).stalks_uniqueFactorizationMonoid_of_regular
      (S.selectedRamificationCover_regularPoints N E hE L e h2 hred hne hIJ hdisj hcurves)
    originalRamificationDivisor S E hE L e h2 hred hne = (T).selectedPrimeCartier M := by
  letI := (T).stalks_uniqueFactorizationMonoid_of_regular
    (S.selectedRamificationCover_regularPoints N E hE L e h2 hred hne hIJ hdisj hcurves)
  apply cartierDivisor_eq_of_idealData (T).toScheme _ _
    (originalRamificationDivisor_hasRegularEquations S E hE L e h2 hred hne)
    ((T).hasRegularCartierEquations_of_effective_weil _ ((T).selectedPrimeCartier_effective M))
  rw [S.originalRamificationDivisor_selectedIdeal N E hE L e h2 hred hne hIJ,
    (T).selectedPrimeCartier_canonicalIdeal M]

end KltDP.Geometry.NormalProjectiveSurface

#print axioms KltDP.Geometry.NormalProjectiveSurface.originalRamificationDivisor_selectedIdeal
#print axioms KltDP.Geometry.NormalProjectiveSurface.originalRamificationDivisor_eq_selectedCartier
