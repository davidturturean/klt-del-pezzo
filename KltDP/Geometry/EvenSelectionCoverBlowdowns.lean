import KltDP.Geometry.OriginalSelectedRamificationContractions
import KltDP.Geometry.DisjointSelectionRamificationMinusOne

/-!
# An original even selection constructs the cover and its blowdowns

Starting with actual disjoint smooth rational minus-two curves and an
integral Picard half-class, the existing cover producer supplies the
original effective Cartier branch and square-root line. The finite
blowdown producer then contracts the actual ramification family on
that unchanged surface, preserving every original disjoint curve.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace
universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k]
    (S : NormalProjectiveSurface k) [IsSmooth S.structureMorphism]

local instance evenSelectionBlowdownsSeparated : S.toScheme.IsSeparated := surfaceSeparated S
local instance evenSelectionBlowdownsMonoidal : MonoidalCategory S.toScheme.Modules :=
  Scheme.Modules.monoidalCategory S.toScheme

/-- The original even divisor class produces the original cover and its ramification blowdowns. -/
theorem exists_original_cover_ramification_blowdowns
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
      ∃ (V : NormalProjectiveSurface k)
        (hV : ∀ v : V.Point, RegularPoint V.toScheme v) (b : T.toScheme ⟶ V.toScheme),
        M.card = N.card ∧ IsPointBlowupSequence T V b ∧
        (∀ P ∈ M, IsExceptionalCurve b P) ∧
        ∀ D : T.PrimeCurve,
          (∀ P ∈ M, Disjoint (D : Set T.toScheme) (P : Set T.toScheme)) →
          ∃ D' : V.PrimeCurve, b.base '' (D : Set T.toScheme) = (D' : Set V.toScheme) ∧
            ∃ η : D'.toScheme ≅ D.toScheme,
              η.hom ≫ (D.inclusion ≫ b) = D'.inclusion ∧
              η.hom ≫ D.toSpec = D'.toSpec ∧
              D'.selfIntersectionNumber hV = D.selfIntersectionNumber H := by
  obtain ⟨E, hE, L, e, hIJ, hred, hne, hweil, hL, _⟩ :=
    S.exists_original_cover_disjoint_ramification_minusOne
      N hN hdisj hcurves hP1 hself m heven h2
  refine ⟨E, hE, L, e, hIJ, hred, hne, hweil, hL, ?_⟩
  exact S.exists_selectedRamification_blowdowns
    N E hE L e h2 hred hne hIJ hdisj hcurves hweil hP1 hself

end KltDP.Geometry.NormalProjectiveSurface

#print axioms KltDP.Geometry.NormalProjectiveSurface.exists_original_cover_ramification_blowdowns
