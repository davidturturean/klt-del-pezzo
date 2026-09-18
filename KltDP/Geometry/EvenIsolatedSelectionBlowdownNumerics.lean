import KltDP.Geometry.EvenIsolatedSelectionForestRankDrop
import KltDP.Geometry.SelectedCoverBlowdownEuler
import KltDP.Geometry.IsolatedQuadraticCanonicalSquare
import KltDP.Geometry.PointBlowupSequenceCanonicalRank

/-!
# One original selected cover and blowdown carry the full forest and numerical invariants

The checked even-selection construction supplies one original quadratic
cover, one ramification blowdown, all retained curves and their matrix,
and the exact rank drop. Cohomology invariance computes the target Euler
characteristic. The original canonical-cover square and exact sequence
rank change compute the square of an internally constructed target
canonical Cartier divisor. The full original source Euler characteristic
is retained, without a rationality or chi-equals-one premise.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace
universe u

namespace KltDP.Geometry.UnbranchedExceptionalBlocks

open NormalProjectiveSurface ActualExceptionalIncidence DisjointNegativeCurvesRank
open ModuleCohomology SmoothCanonicalCartierRepresentative SmoothCanonicalExteriorComparison
open OriginalCartierRamificationSmooth

variable {k : Type u} [Field k] [IsAlgClosed k] {S X : NormalProjectiveSurface k}
    (π : S.toScheme ⟶ X.toScheme) (N : Finset S.PrimeCurve)
    [IsProper π] (hbir : IsBirationalScheme π)
    (hmin : IsMinimalResolution S X π) (hklt : IsKlt X)
    (hiso : IsolatedSelection π N) (hN : ∀ A ∈ N, IsExceptionalCurve π A)

local instance selectedCoverBlowdownNumericsSeparated : S.toScheme.IsSeparated := surfaceSeparated S
local instance selectedCoverBlowdownNumericsMonoidal : MonoidalCategory S.toScheme.Modules :=
  Scheme.Modules.monoidalCategory S.toScheme

/-- The same constructed cover and blowdown have the full forest conclusions and derived invariants. -/
theorem exists_evenSelection_forest_blowdown_with_numerics
    (hneN : N.Nonempty)
    (hself : ∀ A ∈ N, A.selfIntersectionNumber hmin.regular = -2)
    (m : Additive S.toScheme.Pic)
    (heven : letI : IsSmooth S.structureMorphism :=
      MinimalResolutionQuadraticRegular.source_isSmooth π hmin;
      S.smoothWeilClassPicardEquiv (S.weilClassMap (S.selectedPrimeWeil N)) = (2 : ℕ) • m)
    (h2 : IsUnit (2 : k)) :
    letI : IsSmoothOfRelativeDimension 2 S.structureMorphism :=
      S.isSmoothOfRelativeDimension_two_of_regularPoints hmin.regular
    let KS := cartierRepresentative S.structureMorphism
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
        2 * (Nat.card (Vertices π) - N.card) < V.picardRank ∧
        (eulerCharacteristic V.structureMorphism
          (_root_.SheafOfModules.unit V.toScheme.ringCatSheaf) : ℚ) =
          2 * (eulerCharacteristic S.structureMorphism
            (_root_.SheafOfModules.unit S.toScheme.ringCatSheaf) : ℚ) - (N.card : ℚ) / 4 ∧
        ∃ KT : CartierDivisor V.toScheme,
          Nonempty (cartierDivisorModule V.toScheme KT ≅ relativeDifferentialExterior V.structureMorphism 2) ∧
          V.intersectionPairing hV KT KT = 2 * S.intersectionPairing hmin.regular KS KS := by
  letI : IsSmoothOfRelativeDimension 2 S.structureMorphism :=
    S.isSmoothOfRelativeDimension_two_of_regularPoints hmin.regular
  let KS := cartierRepresentative S.structureMorphism
  dsimp only
  obtain ⟨E, hE, L, e, hIJ, hred, hne, hweil, hL, hfamily⟩ :=
    exists_evenSelection_forest_blowdown_with_rank_drop π N hbir hmin hklt hiso hN hneN hself m heven h2
  obtain ⟨V, hV, b, Q, hcard, hdrop, hseq, hcontract, hQ, hmatrix, hcount, hspan, hbound⟩ := hfamily
  let Y := OriginalCartierQuadraticIntegral.normalProjectiveSurface S E hE L e h2 hred hne
  let H := MinimalResolutionQuadraticRegular.selectedCover_regularPoints
    π hmin E hE L e h2 hred hne N hIJ (isolatedSelection_pairwise π N hiso hN)
    (selectedExceptional_isSmooth π N hmin hklt hN)
  letI : IsSmoothOfRelativeDimension 1
      ((effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).gluedTo ≫ S.structureMorphism) :=
    isolatedSelection_canonicalBranch_isSmoothOne π N hmin hklt hiso hN E hE hIJ
  letI : IsIntegral Y.toScheme := Y.integral
  letI : IsSmoothOfRelativeDimension 2 Y.structureMorphism :=
    originalCover_smoothTwo S E hE L e h2 hred hne
  letI : IsSmoothOfRelativeDimension 2 V.structureMorphism :=
    V.isSmoothOfRelativeDimension_two_of_regularPoints hV
  let KY := cartierRepresentative Y.structureMorphism
  let KT := cartierRepresentative V.structureMorphism
  have eKY : cartierDivisorModule Y.toScheme KY ≅ relativeDifferentialExterior Y.structureMorphism 2 :=
    SmoothCanonicalCartierExterior.representativeIsoExterior Y.structureMorphism
  have eKT : cartierDivisorModule V.toScheme KT ≅ relativeDifferentialExterior V.structureMorphism 2 :=
    SmoothCanonicalCartierExterior.representativeIsoExterior V.structureMorphism
  have hYsquare : Y.intersectionPairing H KY KY =
      2 * S.intersectionPairing hmin.regular KS KS - (N.card : ℤ) :=
    OriginalQuadraticCanonicalIntersection.isolatedSelection_canonical_selfIntersection
      π N hmin hklt hiso hN E hE L e h2 hred hne hIJ hweil hself
  have hVsquare : V.intersectionPairing hV KT KT = 2 * S.intersectionPairing hmin.regular KS KS := by
    have hchange := hseq.canonical_square_eq_add_of_picardRank H hV KY KT eKY eKT N.card hdrop
    change V.intersectionPairing hV KT KT = Y.intersectionPairing H KY KY + (N.card : ℤ) at hchange
    rw [hYsquare] at hchange
    simpa only [sub_add_cancel] using hchange
  have hEuler := selectedCover_blowdown_euler π N hmin hklt hiso hN
    E hE L e h2 hred hne hweil hself V hV b hseq
  refine ⟨E, hE, L, e, hIJ, hred, hne, hweil, hL, ?_⟩
  dsimp only
  exact ⟨V, hV, b, Q, hcard, hdrop, hseq, hcontract, hQ, hmatrix, hcount, hspan, hbound,
    hEuler, KT, ⟨eKT⟩, hVsquare⟩

end KltDP.Geometry.UnbranchedExceptionalBlocks

#print axioms KltDP.Geometry.UnbranchedExceptionalBlocks.exists_evenSelection_forest_blowdown_with_numerics
