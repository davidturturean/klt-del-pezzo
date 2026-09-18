import KltDP.Geometry.SelectedRamificationSelfIntersection
import KltDP.Geometry.Resolution

/-!
# Actual minus-one curves from the original selected rational minus-two curves

The proved original source isomorphism transfers the original P¹
identification over k. Together with the computed self-intersection,
this gives the existing geometric predicate IsMinusOneCurve for each
actual ramification image. Their exact finite count and disjointness
are retained for the subsequent surface argument.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace
universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k] (S : NormalProjectiveSurface k)
    [IsSmooth S.structureMorphism]

local instance selectedRamificationMinusOneSeparated : S.toScheme.IsSeparated := surfaceSeparated S
local instance selectedRamificationMinusOneMonoidal : MonoidalCategory S.toScheme.Modules :=
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
    (hdisj : (N : Set S.PrimeCurve).Pairwise fun C D =>
      Disjoint (C : Set S.toScheme) (D : Set S.toScheme))
    (hcurves : ∀ C ∈ N, IsSmooth C.toSpec)
    (hweil : S.cartierToWeilHom E = S.selectedPrimeWeil N)

local notation "T" => OriginalCartierQuadraticIntegral.normalProjectiveSurface S E hE L e h2 hred hne
local notation "M" => S.selectedRamificationPrimeSet N E hE L e h2 hred hne hIJ
local notation "H" => S.selectedRamificationCover_regularPoints N E hE L e h2 hred hne hIJ hdisj hcurves

include hweil

/-- Each original rational minus-two curve has an actual minus-one ramification curve. -/
theorem selectedRamificationPrimeCurve_isMinusOne
    (C : {C : S.PrimeCurve // C ∈ N})
    (hP1 : ∃ η : C.val.toScheme ≅ projectiveSpace k 1,
      η.hom ≫ projectiveSpaceToSpec k 1 = C.val.toSpec)
    (hself : C.val.selfIntersectionNumber S.regularPoints_of_isSmooth = -2) :
    IsMinusOneCurve H (S.selectedRamificationPrimeCurve N E hE L e h2 hred hne hIJ C) := by
  refine ⟨?_, S.selectedRamificationPrimeCurve_selfIntersection_eq_neg_one
    N E hE L e h2 hred hne hIJ hdisj hcurves hweil C hself⟩
  obtain ⟨η, hη⟩ := hP1
  refine ⟨S.selectedRamificationPrimeCurveSourceIso N E hE L e h2 hred hne hIJ C ≪≫ η, ?_⟩
  rw [Iso.trans_hom, Category.assoc, hη,
    S.selectedRamificationPrimeCurveSourceIso_hom_toSpec N E hE L e h2 hred hne hIJ C]

/-- The unchanged cover contains exactly the selected number of pairwise disjoint minus-one copies. -/
theorem selectedRamificationPrimeSet_disjoint_minusOne
    (hP1 : ∀ C ∈ N, ∃ η : C.toScheme ≅ projectiveSpace k 1,
      η.hom ≫ projectiveSpaceToSpec k 1 = C.toSpec)
    (hself : ∀ C ∈ N, C.selfIntersectionNumber S.regularPoints_of_isSmooth = -2) :
    (M).card = N.card ∧
      ((M : Finset (T).PrimeCurve) : Set (T).PrimeCurve).Pairwise
        (fun P Q => Disjoint (P : Set (T).toScheme) (Q : Set (T).toScheme)) ∧
      ∀ P ∈ M, IsMinusOneCurve H P := by
  refine ⟨S.card_selectedRamificationPrimeSet N E hE L e h2 hred hne hIJ,
    S.selectedRamificationPrimeSet_pairwise N E hE L e h2 hred hne hIJ hdisj, ?_⟩
  intro P hP
  obtain ⟨C, rfl⟩ := (S.mem_selectedRamificationPrimeSet N E hE L e h2 hred hne hIJ P).mp hP
  exact S.selectedRamificationPrimeCurve_isMinusOne N E hE L e h2 hred hne hIJ hdisj hcurves
    hweil C (hP1 C.val C.property) (hself C.val C.property)

end KltDP.Geometry.NormalProjectiveSurface

#print axioms KltDP.Geometry.NormalProjectiveSurface.selectedRamificationPrimeSet_disjoint_minusOne
