import KltDP.Geometry.SelectedPrimeRamificationMaps

/-!
# The actual ramification copies exhaust the original ramification locus

The original canonical-ideal equality proves that the selected curve
maps cover the canonical branch scheme. The proved global isomorphism
then shows that their actual lifts exhaust the original global root-zero
image. No branch component or ramification point is discarded.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace
universe u

namespace KltDP.Geometry.NormalProjectiveSurface

open OriginalCartierRamificationSmooth

variable {k : Type u} [Field k] (S : NormalProjectiveSurface k)

local instance selectedPrimeRamificationCoverageSeparated : S.toScheme.IsSeparated := surfaceSeparated S
local instance selectedPrimeRamificationCoverageMonoidal : MonoidalCategory S.toScheme.Modules :=
  Scheme.Modules.monoidalCategory S.toScheme

variable (N : Finset S.PrimeCurve) (E : CartierDivisor S.toScheme)
    (hE : HasRegularCartierEquations S.toScheme E) (L : InvertibleSheaf S.toScheme)
    (e : L.obj ⊗ L.obj ≅ cartierDivisorModule S.toScheme E)
    (hIJ : effectiveCartierIdealDataOfRegularEquations S.toScheme E hE =
      Scheme.IdealSheafData.vanishingIdeal (S.selectedPrimeClosedUnion N))

/-- The actual selected maps exhaust the original canonical branch scheme. -/
theorem selectedPrimeCanonicalBranchMap_cover
    (z : (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued) :
    ∃ C : {C : S.PrimeCurve // C ∈ N},
      z ∈ Set.range (S.selectedPrimeCanonicalBranchMap N E hE hIJ C).base := by
  let I := effectiveCartierIdealDataOfRegularEquations S.toScheme E hE
  have hz : I.gluedTo.base z ∈ ⋃ C ∈ N, (C : Set S.toScheme) := by
    have hr := I.range_gluedTo.le ⟨z, rfl⟩
    change I.gluedTo.base z ∈ I.support at hr
    have hsupport : (I.support : Set S.toScheme) = ⋃ C ∈ N, (C : Set S.toScheme) := by
      rw [show I = S.selectedPrimeUnionIdeal N from hIJ]
      rfl
    exact hsupport.le hr
  obtain ⟨C, hz⟩ := Set.mem_iUnion.mp hz
  obtain ⟨hC, hz⟩ := Set.mem_iUnion.mp hz
  obtain ⟨y, hy⟩ := C.range_inclusion.ge hz
  refine ⟨⟨C, hC⟩, y, I.gluedTo_injective ?_⟩
  change (S.selectedPrimeCanonicalBranchMap N E hE hIJ ⟨C, hC⟩ ≫ I.gluedTo).base y =
    I.gluedTo.base z
  rwa [selectedPrimeCanonicalBranchMap_toBase]

private theorem range_eq_iUnion_through_iso {Z B Y : Scheme.{u}}
    {κ : Type u} (C : κ → Scheme.{u}) (η : Z ≅ B) (ι : Z ⟶ Y)
    (f : ∀ i, C i ⟶ B)
    (hcover : ∀ b : B, ∃ i, b ∈ Set.range (f i).base) :
    Set.range ι.base = ⋃ i, Set.range (f i ≫ η.inv ≫ ι).base := by
  apply Set.Subset.antisymm
  · rintro x ⟨z, rfl⟩
    obtain ⟨i, c, hc⟩ := hcover (η.hom.base z)
    apply Set.mem_iUnion.mpr
    refine ⟨i, c, ?_⟩
    change ι.base (η.inv.base ((f i).base c)) = ι.base z
    rw [hc]
    change (η.hom ≫ η.inv ≫ ι).base z = ι.base z
    rw [Iso.hom_inv_id_assoc]
  · intro x hx
    obtain ⟨i, c, rfl⟩ := Set.mem_iUnion.mp hx
    exact ⟨η.inv.base ((f i).base c), rfl⟩

/-- Every original ramification point lies on one of the actual selected copies. -/
theorem range_rootZeroGlobalι_eq_selected_ramification :
    Set.range (effectiveCartierQuadraticAtlas S.toScheme E hE L e).rootZeroGlobalι.base =
      ⋃ C : {C : S.PrimeCurve // C ∈ N},
        Set.range (S.selectedPrimeRamificationMap N E hE L e hIJ C).base := by
  exact range_eq_iUnion_through_iso
    (fun C : {C : S.PrimeCurve // C ∈ N} => C.val.toScheme)
    (rootZeroGlobalIsoCanonicalBranch S.toScheme E hE L e
      (S.canonicalBranch_isReduced_of_selectedIdealEq N E hE hIJ))
    (effectiveCartierQuadraticAtlas S.toScheme E hE L e).rootZeroGlobalι
    (S.selectedPrimeCanonicalBranchMap N E hE hIJ)
    (S.selectedPrimeCanonicalBranchMap_cover N E hE hIJ)

end KltDP.Geometry.NormalProjectiveSurface

#print axioms KltDP.Geometry.NormalProjectiveSurface.range_rootZeroGlobalι_eq_selected_ramification
