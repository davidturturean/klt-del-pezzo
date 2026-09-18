import KltDP.Geometry.OriginalUnbranchedForestBlowdownRankDrop
import KltDP.Geometry.DisjointSelectionRamificationMinusOne

/-!
# The original even isolated selection constructs one full forest blowdown with exact rank drop

The original Picard half-class constructs the Cartier branch and square-root
line on the original resolution. The same constructed quadratic cover and
one actual ramification blowdown retain every original unbranched exceptional
component twice. All curve maps, the full doubled matrix, exact 2(r-n) count
and span, the strict target Picard bound and exact Picard-rank drop are derived. No cover, branch
ideal, local frame, smoothness, target intersection, count, or rank data is
supplied to this final producer.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace
universe u

namespace KltDP.Geometry.UnbranchedExceptionalBlocks

open NormalProjectiveSurface ActualExceptionalIncidence DisjointNegativeCurvesRank

variable {k : Type u} [Field k] [IsAlgClosed k] {S X : NormalProjectiveSurface k}
    (π : S.toScheme ⟶ X.toScheme) (N : Finset S.PrimeCurve)
    [IsProper π] (hbir : IsBirationalScheme π)
    (hmin : IsMinimalResolution S X π) (hklt : IsKlt X)
    (hiso : IsolatedSelection π N) (hN : ∀ A ∈ N, IsExceptionalCurve π A)

local instance evenIsolatedSelectionForestRankDropSeparated : S.toScheme.IsSeparated := surfaceSeparated S
local instance evenIsolatedSelectionForestRankDropMonoidal : MonoidalCategory S.toScheme.Modules :=
  Scheme.Modules.monoidalCategory S.toScheme

/-- An actual even isolated selection produces one cover and one complete tree-preserving blowdown. -/
theorem exists_evenSelection_forest_blowdown_with_rank_drop
    (hneN : N.Nonempty)
    (hself : ∀ A ∈ N, A.selfIntersectionNumber hmin.regular = -2)
    (m : Additive S.toScheme.Pic)
    (heven : letI : IsSmooth S.structureMorphism :=
      MinimalResolutionQuadraticRegular.source_isSmooth π hmin;
      S.smoothWeilClassPicardEquiv (S.weilClassMap (S.selectedPrimeWeil N)) = (2 : ℕ) • m)
    (h2 : IsUnit (2 : k)) :
    ∃ (E : CartierDivisor S.toScheme) (hE : HasRegularCartierEquations S.toScheme E)
      (L : InvertibleSheaf S.toScheme)
      (e : L.obj ⊗ L.obj ≅ cartierDivisorModule S.toScheme E)
      (hIJ : effectiveCartierIdealDataOfRegularEquations S.toScheme E hE =
        Scheme.IdealSheafData.vanishingIdeal (S.selectedPrimeClosedUnion N))
      (hred : IsReduced (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued)
      (hne : Nonempty (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued),
      S.cartierToWeilHom E = S.selectedPrimeWeil N ∧ L.toPic = m.toMul ∧
      let T := OriginalCartierQuadraticIntegral.normalProjectiveSurface S E hE L e h2 hred hne
      let M := S.selectedRamificationPrimeSet N E hE L e h2 hred hne hIJ
      let H := MinimalResolutionQuadraticRegular.selectedCover_regularPoints
        π hmin E hE L e h2 hred hne N hIJ
        (isolatedSelection_pairwise π N hiso hN) (selectedExceptional_isSmooth π N hmin hklt hN)
      let C := forestCurve π N hbir hmin hklt E hE L e h2 hred hne hIJ hiso
      ∃ (V : NormalProjectiveSurface k)
        (hV : ∀ v : V.Point, RegularPoint V.toScheme v)
        (b : T.toScheme ⟶ V.toScheme) (Q : Bool × Components π N hbir → V.PrimeCurve),
        M.card = N.card ∧ T.picardRank = V.picardRank + N.card ∧ IsPointBlowupSequence T V b ∧
        (∀ P ∈ M, IsExceptionalCurve b P) ∧
        (∀ i, b.base '' (C i.1 i.2 : Set T.toScheme) = (Q i : Set V.toScheme) ∧
          ∃ η : (Q i).toScheme ≅ (C i.1 i.2).toScheme,
            η.hom ≫ ((C i.1 i.2).inclusion ≫ b) = (Q i).inclusion ∧
            η.hom ≫ (C i.1 i.2).toSpec = (Q i).toSpec ∧
            (Q i).selfIntersectionNumber hV = (C i.1 i.2).selfIntersectionNumber H) ∧
        (∀ i j, V.primeCurveMatrix hV (Q i) (Q j) =
          if i.1 = j.1 then S.primeCurveMatrix hmin.regular
            (baseCurve π N hbir hmin hklt i.2) (baseCurve π N hbir hmin hklt j.2) else 0) ∧
        Nat.card (Set.range Q) = 2 * (Nat.card (Vertices π) - N.card) ∧
        Module.finrank ℚ (Submodule.span ℚ (Set.range (fun i => curveClass V hV (Q i)))) =
          2 * (Nat.card (Vertices π) - N.card) ∧
        2 * (Nat.card (Vertices π) - N.card) < V.picardRank := by
  letI : IsSmooth S.structureMorphism := MinimalResolutionQuadraticRegular.source_isSmooth π hmin
  obtain ⟨E, hE, L, e, hIJ, hred, hne, hweil, hL, _⟩ :=
    S.exists_original_cover_disjoint_ramification_minusOne N hneN
      (isolatedSelection_pairwise π N hiso hN) (selectedExceptional_isSmooth π N hmin hklt hN)
      (selectedExceptional_projectiveLine π N hmin hklt hN) hself m heven h2
  refine ⟨E, hE, L, e, hIJ, hred, hne, hweil, hL, ?_⟩
  dsimp only
  obtain ⟨V, hV, b, Q, hcard, hdrop, hseq, hcontract, hQ, hmatrix, hpos, hLI, hcount, hspan, hbound⟩ :=
    exists_ramification_blowdowns_with_forest_rank_drop π N hbir hmin hklt
      E hE L e h2 hred hne hIJ hiso hN hweil hself
  exact ⟨V, hV, b, Q, hcard, hdrop, hseq, hcontract, hQ, hmatrix, hcount, hspan, hbound⟩

end KltDP.Geometry.UnbranchedExceptionalBlocks

#print axioms KltDP.Geometry.UnbranchedExceptionalBlocks.exists_evenSelection_forest_blowdown_with_rank_drop
