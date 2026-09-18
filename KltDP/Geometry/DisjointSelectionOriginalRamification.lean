import KltDP.Geometry.SmoothDisjointSelectionQuadraticRegular
import KltDP.Geometry.SelectedPrimeRamificationMaps

/-!
# A regular original double cover with the actual selected ramification curves

The manuscript's nonempty disjoint smooth even selection constructs the
Cartier divisor, half-line and square isomorphism on the original surface.
The same original cover has all the proved geometric properties and
contains a family of actual closed copies of the original selected
curves. Their projections are the original inclusions and their ranges
are pairwise disjoint. No branch ideal equality, branch map, cover
geometry, or projection compatibility is supplied in this endpoint.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace
universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k]
    (S : NormalProjectiveSurface k) [IsSmooth S.structureMorphism]

local instance disjointSelectionOriginalRamificationSeparated : S.toScheme.IsSeparated :=
  surfaceSeparated S
local instance disjointSelectionOriginalRamificationMonoidal : MonoidalCategory S.toScheme.Modules :=
  Scheme.Modules.monoidalCategory S.toScheme

/-- The actual selected geometry supplies its original regular cover and actual ramification copies. -/
theorem exists_regular_cover_with_original_ramification_curves
    (N : Finset S.PrimeCurve) (hN : N.Nonempty)
    (hdisj : (N : Set S.PrimeCurve).Pairwise fun C D =>
      Disjoint (C : Set S.toScheme) (D : Set S.toScheme))
    (hcurves : ∀ C ∈ N, IsSmooth C.toSpec)
    (m : Additive S.toScheme.Pic)
    (heven : S.smoothWeilClassPicardEquiv (S.weilClassMap (S.selectedPrimeWeil N)) =
      (2 : ℕ) • m) (h2 : IsUnit (2 : k)) :
    ∃ (E : CartierDivisor S.toScheme) (hE : HasRegularCartierEquations S.toScheme E)
      (L : InvertibleSheaf S.toScheme)
      (e : L.obj ⊗ L.obj ≅ cartierDivisorModule S.toScheme E),
      S.cartierToWeilHom E = S.selectedPrimeWeil N ∧ L.toPic = m.toMul ∧
      effectiveCartierIdealDataOfRegularEquations S.toScheme E hE =
        Scheme.IdealSheafData.vanishingIdeal (S.selectedPrimeClosedUnion N) ∧
      let A := InvertibleQuadraticAtlas.fromSquareRoot S.toScheme L
        (cartierDivisorModule S.toScheme E) e (effectiveCartierSection S.toScheme E hE)
      IsIntegral A.scheme ∧ IsNormalScheme A.scheme ∧
        IsProjectiveOverField (A.morphism ≫ S.structureMorphism) ∧
        topologicalKrullDim A.scheme = 2 ∧ IsFinite A.morphism ∧
        AlgebraicGeometry.Flat A.morphism ∧ AlgebraicGeometry.Surjective A.morphism ∧
        (∀ y : A.scheme, RegularPoint A.scheme y) ∧
        ∃ c : ∀ C : {C : S.PrimeCurve // C ∈ N}, C.val.toScheme ⟶ A.scheme,
          (∀ C, IsClosedImmersion (c C)) ∧
          (∀ C, c C ≫ A.morphism = C.val.inclusion) ∧
          Pairwise fun C D => Disjoint (Set.range (c C).base) (Set.range (c D).base) := by
  obtain ⟨E, hE, L, e, hweil, hL, hIJ, hint, hnormal, hproj, hdim, hfin, hflat, hsurj, hreg⟩ :=
    S.exists_regular_quadratic_surface_of_nonempty_disjoint_even_selection
      N hN hdisj hcurves m heven h2
  refine ⟨E, hE, L, e, hweil, hL, hIJ, hint, hnormal, hproj, hdim, hfin, hflat, hsurj, hreg,
    S.selectedPrimeRamificationMap N E hE L e hIJ, ?_, ?_, ?_⟩
  · intro C
    infer_instance
  · exact S.selectedPrimeRamificationMap_toBase N E hE L e hIJ
  · exact S.selectedPrimeRamificationMaps_disjoint N E hE L e hIJ hdisj

end KltDP.Geometry.NormalProjectiveSurface

#print axioms KltDP.Geometry.NormalProjectiveSurface.exists_regular_cover_with_original_ramification_curves
