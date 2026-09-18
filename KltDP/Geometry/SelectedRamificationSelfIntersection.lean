import KltDP.Geometry.SelectedRamificationDivisorUnion
import KltDP.Geometry.OriginalCartierRamificationMultiplicity
import KltDP.Geometry.SelectedPrimeCartierIntersection
import KltDP.Geometry.SmoothSurfaceRegularity

/-!
# The actual ramification copies of disjoint minus-two curves have square minus one

The actual divisor equality π*E = 2R and the proved original-curve
projection formula give twice the lifted curve's self-intersection.
The actual reduced ramification divisor is the selected disjoint Cartier
sum, so its restriction contributes only that curve's diagonal term.
All cover regularity, image identifications, and component multiplicities
come from the original construction.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace
universe u

namespace KltDP.Geometry.NormalProjectiveSurface

open OriginalCartierRamificationSmooth

variable {k : Type u} [Field k] [IsAlgClosed k] (S : NormalProjectiveSurface k)
    [IsSmooth S.structureMorphism]

local instance selectedRamificationSelfIntersectionSeparated : S.toScheme.IsSeparated := surfaceSeparated S
local instance selectedRamificationSelfIntersectionMonoidal : MonoidalCategory S.toScheme.Modules :=
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

local notation "A" => effectiveCartierQuadraticAtlas S.toScheme E hE L e
local notation "T" => OriginalCartierQuadraticIntegral.normalProjectiveSurface S E hE L e h2 hred hne
local notation "M" => S.selectedRamificationPrimeSet N E hE L e h2 hred hne hIJ
local notation "H" => S.selectedRamificationCover_regularPoints N E hE L e h2 hred hne hIJ hdisj hcurves

/-- The actual ramification divisor restricts to each lifted curve by its self-intersection. -/
theorem selectedRamificationPrimeCurve_intersection_ramification
    (C : {C : S.PrimeCurve // C ∈ N}) :
    (S.selectedRamificationPrimeCurve N E hE L e h2 hred hne hIJ C).intersectionNumber
      (originalRamificationDivisor S E hE L e h2 hred hne) =
        (S.selectedRamificationPrimeCurve N E hE L e h2 hred hne hIJ C).selfIntersectionNumber H := by
  letI := (T).stalks_uniqueFactorizationMonoid_of_regular H
  rw [S.originalRamificationDivisor_eq_selectedCartier N E hE L e h2 hred hne hIJ hdisj hcurves]
  exact (T).intersectionNumber_selected_disjoint_sum H M ((T).selectedPrimeCartier M)
    ((T).selectedPrimeCartier_weil M)
    (S.selectedRamificationPrimeSet_pairwise N E hE L e h2 hred hne hIJ hdisj) _
    ((S.mem_selectedRamificationPrimeSet N E hE L e h2 hred hne hIJ _).mpr ⟨C, rfl⟩)

/-- Twice the actual lifted curve's self-intersection is the original curve's self-intersection. -/
theorem two_mul_selectedRamificationPrimeCurve_selfIntersection
    (hweil : S.cartierToWeilHom E = S.selectedPrimeWeil N)
    (C : {C : S.PrimeCurve // C ∈ N}) :
    2 * (S.selectedRamificationPrimeCurve N E hE L e h2 hred hne hIJ C).selfIntersectionNumber H =
      C.val.selfIntersectionNumber S.regularPoints_of_isSmooth := by
  letI : IsIntegral (A).scheme := (T).integral
  letI : GenericPointPreserving (A).morphism := (A).morphism_genericPointPreserving
  have hproj := S.selectedRamificationPrimeCurve_intersection_pullback
    N E hE L e h2 hred hne hIJ C E hE
  change (S.selectedRamificationPrimeCurve N E hE L e h2 hred hne hIJ C).intersectionNumber
    (pullbackDivisor (A).morphism E hE) = C.val.intersectionNumber E at hproj
  rw [original_pullback_branch_eq_two_ramification S E hE L e h2 hred hne,
    two_nsmul, PrimeCurve.intersectionNumber_add,
    S.selectedRamificationPrimeCurve_intersection_ramification N E hE L e h2 hred hne hIJ hdisj hcurves C,
    S.intersectionNumber_selected_disjoint_sum S.regularPoints_of_isSmooth N E hweil hdisj C.val C.property] at hproj
  omega

/-- A selected original minus-two curve gives an actual minus-one ramification prime curve. -/
theorem selectedRamificationPrimeCurve_selfIntersection_eq_neg_one
    (hweil : S.cartierToWeilHom E = S.selectedPrimeWeil N)
    (C : {C : S.PrimeCurve // C ∈ N})
    (hself : C.val.selfIntersectionNumber S.regularPoints_of_isSmooth = -2) :
    (S.selectedRamificationPrimeCurve N E hE L e h2 hred hne hIJ C).selfIntersectionNumber H = -1 := by
  have h := S.two_mul_selectedRamificationPrimeCurve_selfIntersection
    N E hE L e h2 hred hne hIJ hdisj hcurves hweil C
  rw [hself] at h
  omega

end KltDP.Geometry.NormalProjectiveSurface

#print axioms KltDP.Geometry.NormalProjectiveSurface.selectedRamificationPrimeCurve_selfIntersection_eq_neg_one

