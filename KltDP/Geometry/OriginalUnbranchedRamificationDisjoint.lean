import KltDP.Geometry.SelectedRamificationPrimeSet

/-!
# Original unbranched lifts avoid every actual ramification curve

Disjointness is checked on the original surface. The proved projection
of each actual ramification curve is its original selected curve, and
the original lift projects to the given branch-disjoint map. These
actual identities imply disjointness on the unchanged cover, including
for the coherent whole-tree component maps used before contraction.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace
universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] (S : NormalProjectiveSurface k)

local instance originalUnbranchedRamificationDisjointSeparated : S.toScheme.IsSeparated := surfaceSeparated S
local instance originalUnbranchedRamificationDisjointMonoidal : MonoidalCategory S.toScheme.Modules :=
  Scheme.Modules.monoidalCategory S.toScheme

variable (N : Finset S.PrimeCurve) (E : CartierDivisor S.toScheme)
    (hE : HasRegularCartierEquations S.toScheme E) (L : InvertibleSheaf S.toScheme)
    (e : L.obj ⊗ L.obj ≅ cartierDivisorModule S.toScheme E)
    (hIJ : effectiveCartierIdealDataOfRegularEquations S.toScheme E hE =
      Scheme.IdealSheafData.vanishingIdeal (S.selectedPrimeClosedUnion N))
    {C : Scheme.{u}} (f : C ⟶ S.toScheme)
    (g : C ⟶ (effectiveCartierQuadraticAtlas S.toScheme E hE L e).scheme)
    (hg : g ≫ (effectiveCartierQuadraticAtlas S.toScheme E hE L e).morphism = f)
    (hdisj : Disjoint (Set.range f.base) (S.selectedPrimeClosedUnion N : Set S.toScheme))

include hg hdisj in
/-- Each original unbranched lift is disjoint from every actual ramification map's image. -/
theorem lift_disjoint_selectedPrimeRamificationMap
    (D : {D : S.PrimeCurve // D ∈ N}) :
    Disjoint (Set.range g.base)
      (Set.range (S.selectedPrimeRamificationMap N E hE L e hIJ D).base) := by
  apply Disjoint.of_image (f := (effectiveCartierQuadraticAtlas S.toScheme E hE L e).morphism.base)
  rw [S.selectedPrimeRamificationMap_image_toBase N E hE L e hIJ D,
    ← Set.range_comp, ← TopCat.coe_comp, ← Scheme.comp_base, hg]
  apply hdisj.mono_right
  intro x hx
  exact Set.mem_iUnion.mpr ⟨D.val, Set.mem_iUnion.mpr ⟨D.property, hx⟩⟩

include hg hdisj in
/-- Every actual curve selected for ramification contraction avoids the original unbranched lift. -/
theorem lift_disjoint_selectedRamificationPrimeSet [IsAlgClosed k]
    (h2 : IsUnit (2 : k))
    (hred : IsReduced
      (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued)
    (hne : Nonempty
      (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued) :
    let T := OriginalCartierQuadraticIntegral.normalProjectiveSurface S E hE L e h2 hred hne
    ∀ P ∈ S.selectedRamificationPrimeSet N E hE L e h2 hred hne hIJ,
      Disjoint (Set.range g.base) (P : Set T.toScheme) := by
  dsimp only
  intro P hP
  obtain ⟨D, rfl⟩ := (S.mem_selectedRamificationPrimeSet N E hE L e h2 hred hne hIJ P).mp hP
  exact S.lift_disjoint_selectedPrimeRamificationMap N E hE L e hIJ f g hg hdisj D

end KltDP.Geometry.NormalProjectiveSurface

#print axioms KltDP.Geometry.NormalProjectiveSurface.lift_disjoint_selectedRamificationPrimeSet
