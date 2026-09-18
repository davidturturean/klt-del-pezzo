import KltDP.Geometry.EvenIsolatedSelectionForestBlowdowns
import KltDP.Geometry.IsolatedExceptionalSelectionGraph

/-!
# Isolated vertices in the original graph construct the complete forest blowdown

Original graph adjacency is actual carrier intersection. The selected
vertices' absence of edges supplies geometric branch isolation, and the
checked even-selection theorem then constructs the same cover, one blowdown,
and all retained doubled components with their original maps and strict rank.
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
    (hN : ∀ A ∈ N, IsExceptionalCurve π A)
    (hgraph : ∀ v : Vertices π, v.val ∈ N → ∀ w : Vertices π, ¬ (graph π).Adj v w)

local instance evenIsolatedGraphForestSeparated : S.toScheme.IsSeparated := surfaceSeparated S
local instance evenIsolatedGraphForestMonoidal : MonoidalCategory S.toScheme.Modules :=
  Scheme.Modules.monoidalCategory S.toScheme

/-- Original isolated graph vertices and an integral half-class give the same full forest endpoint. -/
theorem exists_evenIsolatedGraphSelection_forest_blowdown
    (hneN : N.Nonempty)
    (hself : ∀ A ∈ N, A.selfIntersectionNumber hmin.regular = -2)
    (m : Additive S.toScheme.Pic)
    (heven : letI : IsSmooth S.structureMorphism :=
      MinimalResolutionQuadraticRegular.source_isSmooth π hmin;
      S.smoothWeilClassPicardEquiv (S.weilClassMap (S.selectedPrimeWeil N)) = (2 : ℕ) • m)
    (h2 : IsUnit (2 : k)) :
    let hiso : IsolatedSelection π N := isolatedSelection_of_no_adj π N hN hgraph
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
        M.card = N.card ∧ IsPointBlowupSequence T V b ∧
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
  exact exists_evenSelection_forest_blowdown π N hbir hmin hklt
    (isolatedSelection_of_no_adj π N hN hgraph) hN hneN hself m heven h2

end KltDP.Geometry.UnbranchedExceptionalBlocks

#print axioms KltDP.Geometry.UnbranchedExceptionalBlocks.exists_evenIsolatedGraphSelection_forest_blowdown
