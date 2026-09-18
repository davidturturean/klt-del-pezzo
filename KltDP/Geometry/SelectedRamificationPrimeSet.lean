import KltDP.Geometry.SelectedRamificationPrimeCurves
import KltDP.Geometry.SelectedPrimeRamificationCoverage

/-!
# The finite set of actual ramification prime curves

Projection back to the original selected curves makes the image family
injective, hence preserves its exact cardinality. Original disjointness
gives disjoint actual images, and the proved original ramification
coverage identifies the selected closed union with the entire actual
ramification locus.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace
universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k] (S : NormalProjectiveSurface k)

local instance selectedRamificationPrimeSetSeparated : S.toScheme.IsSeparated := surfaceSeparated S
local instance selectedRamificationPrimeSetMonoidal : MonoidalCategory S.toScheme.Modules :=
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

/-- The actual finite set of ramification prime curves. -/
def selectedRamificationPrimeSet : Finset (T).PrimeCurve := by
  classical
  exact Finset.univ.image (S.selectedRamificationPrimeCurve N E hE L e h2 hred hne hIJ)

theorem mem_selectedRamificationPrimeSet (P : (T).PrimeCurve) :
    P ∈ S.selectedRamificationPrimeSet N E hE L e h2 hred hne hIJ ↔
      ∃ C, S.selectedRamificationPrimeCurve N E hE L e h2 hred hne hIJ C = P := by
  classical
  simp only [selectedRamificationPrimeSet, Finset.mem_image, Finset.mem_univ, true_and]

theorem selectedRamificationPrimeCurve_injective :
    Function.Injective (S.selectedRamificationPrimeCurve N E hE L e h2 hred hne hIJ) := by
  intro C D h
  apply Subtype.ext
  apply PrimeCurve.ext
  have hi := congrArg (fun P : (T).PrimeCurve => (A).morphism.base '' (P : Set (T).toScheme)) h
  simpa only [coe_selectedRamificationPrimeCurve, selectedPrimeRamificationMap_image_toBase] using hi

/-- The original number of selected curves is preserved exactly. -/
theorem card_selectedRamificationPrimeSet :
    (S.selectedRamificationPrimeSet N E hE L e h2 hred hne hIJ).card = N.card := by
  classical
  rw [selectedRamificationPrimeSet,
    Finset.card_image_of_injective _ (S.selectedRamificationPrimeCurve_injective N E hE L e h2 hred hne hIJ),
    Finset.card_univ, Fintype.card_coe]

/-- The finite ramification selection inherits actual geometric disjointness. -/
theorem selectedRamificationPrimeSet_pairwise
    (hdisj : (N : Set S.PrimeCurve).Pairwise fun C D =>
      Disjoint (C : Set S.toScheme) (D : Set S.toScheme)) :
    ((S.selectedRamificationPrimeSet N E hE L e h2 hred hne hIJ : Finset (T).PrimeCurve) :
      Set (T).PrimeCurve).Pairwise fun P Q => Disjoint (P : Set (T).toScheme) (Q : Set (T).toScheme) := by
  intro P hP Q hQ hPQ
  obtain ⟨C, rfl⟩ := (S.mem_selectedRamificationPrimeSet N E hE L e h2 hred hne hIJ P).mp hP
  obtain ⟨D, rfl⟩ := (S.mem_selectedRamificationPrimeSet N E hE L e h2 hred hne hIJ Q).mp hQ
  exact S.selectedPrimeRamificationMaps_disjoint N E hE L e hIJ hdisj
    (fun h => hPQ (congrArg _ h))

/-- The selected actual image curves exhaust exactly the original ramification locus. -/
theorem selectedRamificationPrimeSet_union :
    ((T).selectedPrimeClosedUnion
      (S.selectedRamificationPrimeSet N E hE L e h2 hred hne hIJ) : Set (T).toScheme) =
        Set.range (A).rootZeroGlobalι.base := by
  rw [S.range_rootZeroGlobalι_eq_selected_ramification N E hE L e hIJ]
  ext x
  change (x ∈ ⋃ P ∈ S.selectedRamificationPrimeSet N E hE L e h2 hred hne hIJ,
    (P : Set (T).toScheme)) ↔
      x ∈ ⋃ C, Set.range (S.selectedPrimeRamificationMap N E hE L e hIJ C).base
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨P, hP, hxP⟩
    obtain ⟨C, rfl⟩ := (S.mem_selectedRamificationPrimeSet N E hE L e h2 hred hne hIJ P).mp hP
    exact ⟨C, hxP⟩
  · rintro ⟨C, hxC⟩
    exact ⟨_, (S.mem_selectedRamificationPrimeSet N E hE L e h2 hred hne hIJ _).mpr ⟨C, rfl⟩, hxC⟩

end KltDP.Geometry.NormalProjectiveSurface

#print axioms KltDP.Geometry.NormalProjectiveSurface.card_selectedRamificationPrimeSet
#print axioms KltDP.Geometry.NormalProjectiveSurface.selectedRamificationPrimeSet_union
