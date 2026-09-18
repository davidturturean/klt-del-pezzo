import KltDP.Geometry.OriginalUnbranchedForestGram
import KltDP.Geometry.OriginalUnbranchedForestRamificationDisjoint
import KltDP.Geometry.IsolatedExceptionalSelectionGeometry
import KltDP.Geometry.SelectedRamificationMinusOne
import KltDP.Geometry.BlowdownSurvivingCurveFamily
import KltDP.Geometry.PrimeCurveFamilyMatrixPairing
import KltDP.Geometry.NegativePrimeFamilyPicardRank

/-!
# One actual ramification blowdown retains the entire doubled exceptional forest

Every original unbranched exceptional block contributes both coherent sheets
to a single surviving family. Original klt geometry supplies branch smoothness
and rationality; the computed ramification self-intersections supply the actual
minus-one curves. One blowdown retains every lifted prime and its original maps.
The full matrix, negativity, independence, exact 2(r-n) count, and strict target
Picard bound are all derived on that same actual target surface.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace
universe u

namespace KltDP.Geometry.UnbranchedExceptionalBlocks

open NormalProjectiveSurface ActualExceptionalIncidence ExceptionalForestClosedBlocks RationalTreePicard
open DisjointNegativeCurvesRank KltDP.LinearAlgebra.CanonicalCorrection

variable {k : Type u} [Field k] [IsAlgClosed k] {S X : NormalProjectiveSurface k}
    (π : S.toScheme ⟶ X.toScheme) (N : Finset S.PrimeCurve)
    [IsProper π] (hbir : IsBirationalScheme π)
    (hmin : IsMinimalResolution S X π) (hklt : IsKlt X)

local instance originalUnbranchedForestBlowdownSeparated : S.toScheme.IsSeparated := surfaceSeparated S
local instance originalUnbranchedForestBlowdownMonoidal : MonoidalCategory S.toScheme.Modules :=
  Scheme.Modules.monoidalCategory S.toScheme

variable (E : CartierDivisor S.toScheme) (hE : HasRegularCartierEquations S.toScheme E)
    (L : InvertibleSheaf S.toScheme)
    (e : L.obj ⊗ L.obj ≅ cartierDivisorModule S.toScheme E) (h2 : IsUnit (2 : k))
    (hred : IsReduced
      (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued)
    (hne : Nonempty
      (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued)
    (hIJ : effectiveCartierIdealDataOfRegularEquations S.toScheme E hE =
      Scheme.IdealSheafData.vanishingIdeal (S.selectedPrimeClosedUnion N))
    (hiso : IsolatedSelection π N)

local notation "CoverSurface" =>
  OriginalCartierQuadraticIntegral.normalProjectiveSurface S E hE L e h2 hred hne
local notation "CoverAtlas" => effectiveCartierQuadraticAtlas S.toScheme E hE L e

local instance originalUnbranchedForestBlowdownComponentsFinite : Finite (Components π N hbir) := by
  letI : Finite (Vertices π) := finite_vertices π hbir
  exact Finite.of_injective (originalVertex π N hbir) (originalVertex_injective π N hbir)

local instance originalUnbranchedForestBlowdownComponentsFintype : Fintype (Components π N hbir) :=
  Fintype.ofFinite _

variable (hN : ∀ A ∈ N, IsExceptionalCurve π A)
    (hweil : S.cartierToWeilHom E = S.selectedPrimeWeil N)

local notation "Ramification" => S.selectedRamificationPrimeSet N E hE L e h2 hred hne hIJ
local notation "CoverRegular" =>
  MinimalResolutionQuadraticRegular.selectedCover_regularPoints π hmin E hE L e h2 hred hne N hIJ
    (isolatedSelection_pairwise π N hiso hN) (selectedExceptional_isSmooth π N hmin hklt hN)
local notation "copy" => forestCurve π N hbir hmin hklt E hE L e h2 hred hne hIJ hiso
local notation "base" => baseCurve π N hbir hmin hklt

include hweil

/-- The same actual blowdown retains all 2(r-n) original lifted primes and their derived rank. -/
theorem exists_ramification_blowdowns_with_forest_picard_bound
    (hself : ∀ A ∈ N, A.selfIntersectionNumber hmin.regular = -2) :
    ∃ (V : NormalProjectiveSurface k)
      (hV : ∀ v : V.Point, RegularPoint V.toScheme v)
      (b : (CoverSurface).toScheme ⟶ V.toScheme)
      (Q : Bool × Components π N hbir → V.PrimeCurve),
      (Ramification).card = N.card ∧ IsPointBlowupSequence CoverSurface V b ∧
      (∀ P ∈ Ramification, IsExceptionalCurve b P) ∧
      (∀ i, b.base '' (copy i.1 i.2 : Set (CoverSurface).toScheme) = (Q i : Set V.toScheme) ∧
        ∃ η : (Q i).toScheme ≅ (copy i.1 i.2).toScheme,
          η.hom ≫ ((copy i.1 i.2).inclusion ≫ b) = (Q i).inclusion ∧
          η.hom ≫ (copy i.1 i.2).toSpec = (Q i).toSpec ∧
          (Q i).selfIntersectionNumber hV = (copy i.1 i.2).selfIntersectionNumber CoverRegular) ∧
      (∀ i j, V.primeCurveMatrix hV (Q i) (Q j) =
        if i.1 = j.1 then S.primeCurveMatrix hmin.regular (base i.2) (base j.2) else 0) ∧
      (negativeGram (V.numericalIntersectionBilinForm hV)
        (fun i => curveClass V hV (Q i))).PosDef ∧
      LinearIndependent ℚ (fun i => curveClass V hV (Q i)) ∧
      Nat.card (Set.range Q) = 2 * (Nat.card (Vertices π) - N.card) ∧
      Module.finrank ℚ (Submodule.span ℚ (Set.range (fun i => curveClass V hV (Q i)))) =
        2 * (Nat.card (Vertices π) - N.card) ∧
      2 * (Nat.card (Vertices π) - N.card) < V.picardRank := by
  classical
  letI : IsSmooth S.structureMorphism := MinimalResolutionQuadraticRegular.source_isSmooth π hmin
  have hsm := isolatedSelection_canonicalBranch_isSmooth π N hmin hklt hiso hN E hE hIJ
  have hsource : (negativeGram ((CoverSurface).numericalIntersectionBilinForm CoverRegular)
      (fun i : Bool × Components π N hbir => curveClass CoverSurface CoverRegular (copy i.1 i.2))).PosDef :=
    forestClass_negativeGram_posDef π N hbir hmin hklt E hE L e h2 hred hne hIJ hiso hsm
  obtain ⟨hcard, hpair, hminus⟩ := S.selectedRamificationPrimeSet_disjoint_minusOne
    N E hE L e h2 hred hne hIJ (isolatedSelection_pairwise π N hiso hN)
    (selectedExceptional_isSmooth π N hmin hklt hN) hweil
    (selectedExceptional_projectiveLine π N hmin hklt hN) hself
  let P : {P : (CoverSurface).PrimeCurve // P ∈ Ramification} → (CoverSurface).PrimeCurve := Subtype.val
  have hm (j : {P : (CoverSurface).PrimeCurve // P ∈ Ramification}) :
      IsMinusOneCurve CoverRegular (P j) := hminus j.val j.property
  have hp : Pairwise (fun i j =>
      Disjoint (P i : Set (CoverSurface).toScheme) (P j : Set (CoverSurface).toScheme)) := by
    intro i j hij
    exact @hpair i.val i.property j.val j.property (fun h => hij (Subtype.ext h))
  have ha (i : Bool × Components π N hbir)
      (j : {P : (CoverSurface).PrimeCurve // P ∈ Ramification}) :
      Disjoint (copy i.1 i.2 : Set (CoverSurface).toScheme) (P j : Set (CoverSurface).toScheme) :=
    forestCurve_disjoint_ramification π N hbir hmin hklt E hE L e h2 hred hne hIJ hiso
      i.1 i.2 j.val j.property
  obtain ⟨V, hV, b, Q, hseq, hcontract, hQ, hmatrix⟩ :=
    KltDP.Geometry.exists_blowdowns_with_surviving_family CoverSurface CoverRegular P hm hp
      (fun i : Bool × Components π N hbir => copy i.1 i.2) ha
  have hpairing := PrimeCurveFamilyIntersectionGram.intersections_eq_of_matrix_eq
    CoverSurface V CoverRegular hV (fun i : Bool × Components π N hbir => copy i.1 i.2) Q hmatrix
  have hgram := PrimeCurveFamilyIntersectionGram.negativeGram_eq_of_matrix_eq
    CoverSurface V CoverRegular hV (fun i : Bool × Components π N hbir => copy i.1 i.2) Q hmatrix
  have hpos : (negativeGram (V.numericalIntersectionBilinForm hV)
      (fun i => curveClass V hV (Q i))).PosDef := by
    rw [hgram]
    exact hsource
  have hLI := KltDP.LinearAlgebra.negativeGram_posDef_linearIndependent
    (V.numericalIntersectionBilinForm hV) (fun i => curveClass V hV (Q i)) hpos
  have hinj : Function.Injective Q := by
    intro i j hij
    apply hLI.injective
    exact congrArg (curveClass V hV) hij
  have hcomponents : Fintype.card (Components π N hbir) = Nat.card (Vertices π) - N.card := by
    rw [← Nat.card_eq_fintype_card]
    exact card_components π N hbir hiso hN
  refine ⟨V, hV, b, Q, hcard, hseq, fun j hj => hcontract ⟨j, hj⟩, hQ, ?_, hpos, hLI, ?_, ?_, ?_⟩
  · intro i j
    calc
      V.primeCurveMatrix hV (Q i) (Q j) =
          (CoverSurface).primeCurveMatrix CoverRegular (copy i.1 i.2) (copy j.1 j.2) := hpairing i j
      _ = _ := forestCurve_actual_doubled_matrix π N hbir hmin hklt E hE L e h2 hred hne hIJ hiso hsm i j
  · rw [Nat.card_range_of_injective hinj, Nat.card_eq_fintype_card,
      Fintype.card_prod, Fintype.card_bool, hcomponents]
  · rw [finrank_span_eq_card hLI, Fintype.card_prod, Fintype.card_bool, hcomponents]
  · have h := V.primeFamily_card_lt_picardRank_of_negativeGram hV Q hpos
    simpa only [Fintype.card_prod, Fintype.card_bool, hcomponents] using h

end KltDP.Geometry.UnbranchedExceptionalBlocks

#print axioms KltDP.Geometry.UnbranchedExceptionalBlocks.exists_ramification_blowdowns_with_forest_picard_bound
