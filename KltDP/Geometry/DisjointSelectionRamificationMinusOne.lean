import KltDP.Geometry.SelectedRamificationMinusOne
import KltDP.Geometry.SmoothDisjointSelectionQuadraticRegular

/-!
# The original even selection produces the actual disjoint minus-one ramification curves

A nonempty disjoint selection of original smooth rational minus-two
curves and its actual integral Picard half-class produce the original
Cartier branch, square-root line and unchanged quadratic surface.
The same constructed surface contains the actual ramification prime
curves, with the exact original count, pairwise disjointness and the
proved geometric minus-one predicate. No branch ideal identification,
cover geometry, local equation, ramification multiplicity or target
self-intersection is supplied.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace
universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k]
    (S : NormalProjectiveSurface k) [IsSmooth S.structureMorphism]

local instance disjointSelectionRamificationMinusOneSeparated : S.toScheme.IsSeparated :=
  surfaceSeparated S
local instance disjointSelectionRamificationMinusOneMonoidal : MonoidalCategory S.toScheme.Modules :=
  Scheme.Modules.monoidalCategory S.toScheme

/-- The actual even selection constructs its original cover and the expected actual minus-one curves. -/
theorem exists_original_cover_disjoint_ramification_minusOne
    (N : Finset S.PrimeCurve) (hN : N.Nonempty)
    (hdisj : (N : Set S.PrimeCurve).Pairwise fun C D =>
      Disjoint (C : Set S.toScheme) (D : Set S.toScheme))
    (hcurves : ∀ C ∈ N, IsSmooth C.toSpec)
    (hP1 : ∀ C ∈ N, ∃ η : C.toScheme ≅ projectiveSpace k 1,
      η.hom ≫ projectiveSpaceToSpec k 1 = C.toSpec)
    (hself : ∀ C ∈ N, C.selfIntersectionNumber S.regularPoints_of_isSmooth = -2)
    (m : Additive S.toScheme.Pic)
    (heven : S.smoothWeilClassPicardEquiv (S.weilClassMap (S.selectedPrimeWeil N)) =
      (2 : ℕ) • m) (h2 : IsUnit (2 : k)) :
    ∃ (E : CartierDivisor S.toScheme) (hE : HasRegularCartierEquations S.toScheme E)
      (L : InvertibleSheaf S.toScheme)
      (e : L.obj ⊗ L.obj ≅ cartierDivisorModule S.toScheme E)
      (hIJ : effectiveCartierIdealDataOfRegularEquations S.toScheme E hE =
        Scheme.IdealSheafData.vanishingIdeal (S.selectedPrimeClosedUnion N))
      (hred : IsReduced
        (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued)
      (hne : Nonempty
        (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued),
      S.cartierToWeilHom E = S.selectedPrimeWeil N ∧ L.toPic = m.toMul ∧
      let T := OriginalCartierQuadraticIntegral.normalProjectiveSurface S E hE L e h2 hred hne
      let M := S.selectedRamificationPrimeSet N E hE L e h2 hred hne hIJ
      let H := S.selectedRamificationCover_regularPoints N E hE L e h2 hred hne hIJ hdisj hcurves
      M.card = N.card ∧
        ((M : Finset T.PrimeCurve) : Set T.PrimeCurve).Pairwise
          (fun P Q => Disjoint (P : Set T.toScheme) (Q : Set T.toScheme)) ∧
        ∀ P ∈ M, IsMinusOneCurve H P := by
  obtain ⟨E, hE, L, e, hweil, hL, hIJ, hint, hnormal, hproj, hdim, hfin, hflat, hsurj, hreg⟩ :=
    S.exists_regular_quadratic_surface_of_nonempty_disjoint_even_selection
      N hN hdisj hcurves m heven h2
  let J := S.selectedPrimeUnionIdeal N
  have hred : IsReduced
      (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued :=
    S.canonicalBranch_isReduced_of_selectedIdealEq N E hE hIJ
  have hne : Nonempty
      (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued := by
    rw [hIJ]
    obtain ⟨x, hx⟩ := S.selectedPrimeClosedUnion_nonempty N hN
    exact ⟨J.gluedSupportHomeomorph.symm ⟨x, hx⟩⟩
  refine ⟨E, hE, L, e, hIJ, hred, hne, hweil, hL, ?_⟩
  exact S.selectedRamificationPrimeSet_disjoint_minusOne
    N E hE L e h2 hred hne hIJ hdisj hcurves hweil hP1 hself

end KltDP.Geometry.NormalProjectiveSurface

#print axioms KltDP.Geometry.NormalProjectiveSurface.exists_original_cover_disjoint_ramification_minusOne

