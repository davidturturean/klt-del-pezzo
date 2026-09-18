import KltDP.Geometry.OriginalUnbranchedTreeBlowdownFamily
import KltDP.Geometry.OriginalUnbranchedRationalTreeIndependence
import KltDP.Geometry.PrimeCurveFamilyMatrixPairing

/-!
# The actual doubled exceptional tree survives on the same blowdown surface

The same constructed ramification blowdown retains the original coherent
tree family. Its complete matrix gives the original matrix on each sheet
and zero between sheets. Negative definiteness comes from the original
proper birational contraction of the base tree. Thus the actual target
prime curves and numerical classes are distinct and independent, with
precisely twice the original component count and span dimension.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace
universe u

namespace KltDP.Geometry.OriginalUnbranchedRationalTreeGeometry

open NormalProjectiveSurface RationalTreePicard DisjointNegativeCurvesRank
open KltDP.LinearAlgebra.CanonicalCorrection

variable {k : Type u} [Field k] [IsAlgClosed k] (S : NormalProjectiveSurface k)
    [IsSmooth S.structureMorphism]

local instance originalUnbranchedTreeBlowdownRankSeparated : S.toScheme.IsSeparated := surfaceSeparated S
local instance originalUnbranchedTreeBlowdownRankMonoidal : MonoidalCategory S.toScheme.Modules :=
  Scheme.Modules.monoidalCategory S.toScheme

variable {C : Scheme.{u}} [NoetherianSpace C] [IsLocallyNoetherian C] [IsReduced C]
    [ConnectedSpace C] [C.IsSeparated]
    (sC : C ⟶ Spec (CommRingCat.of k)) [IsProper sC]
    (hdim : topologicalKrullDim C ≤ 1)
    (hTree : (componentPointIncidenceGraph C).IsTree)
    (htrans : HasTransverseComponentBranches C)
    (eC : ∀ D : ↥(irreducibleComponents C), componentUnionScheme C {D} ≅ projectiveSpace k 1)
    (E : CartierDivisor S.toScheme) (hE : HasRegularCartierEquations S.toScheme E)
    (L : InvertibleSheaf S.toScheme)
    (e : L.obj ⊗ L.obj ≅ cartierDivisorModule S.toScheme E) (h2 : IsUnit (2 : k))
    (hred : IsReduced
      (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued)
    (hne : Nonempty
      (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued)
    (f : C ⟶ S.toScheme) [IsClosedImmersion f]
    (hdisj : Disjoint (Set.range f.base)
      (Set.range (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).gluedTo.base))

variable (N : Finset S.PrimeCurve)
    (hIJ : effectiveCartierIdealDataOfRegularEquations S.toScheme E hE =
      Scheme.IdealSheafData.vanishingIdeal (S.selectedPrimeClosedUnion N))
    (hSelectedDisj : (N : Set S.PrimeCurve).Pairwise fun A B =>
      Disjoint (A : Set S.toScheme) (B : Set S.toScheme))
    (hcurves : ∀ A ∈ N, IsSmooth A.toSpec)
    (hweil : S.cartierToWeilHom E = S.selectedPrimeWeil N)

local notation "CoverSurface" =>
  OriginalCartierQuadraticIntegral.normalProjectiveSurface S E hE L e h2 hred hne
local notation "Ramification" => S.selectedRamificationPrimeSet N E hE L e h2 hred hne hIJ
local notation "CoverRegular" =>
  S.selectedRamificationCover_regularPoints N E hE L e h2 hred hne hIJ hSelectedDisj hcurves
local notation "copyCurve" =>
  liftedCurve S sC hdim hTree htrans eC E hE L e h2 hred hne f hdisj

local instance originalUnbranchedTreeBlowdownRankFintype : Fintype ↥(irreducibleComponents C) :=
  NoetherianSpace.finite_irreducibleComponents.fintype

local notation "baseCurve" => RationalComponentPrimeCurves.curve S f eC

variable {X : NormalProjectiveSurface k} (r : S.toScheme ⟶ X.toScheme) [IsProper r]
    (hr : r ≫ X.structureMorphism = S.structureMorphism) (hbir : IsBirationalScheme r)
    (hcontracted : ∀ D : ↥(irreducibleComponents C),
      IsExceptionalCurve r (RationalComponentPrimeCurves.curve S f eC D))

include hweil hr hbir hcontracted

/-- The same actual blowdown retains the doubled original matrix and its derived exact rank. -/
theorem exists_ramification_blowdowns_with_doubled_tree_rank
    (hP1 : ∀ A ∈ N, ∃ η : A.toScheme ≅ projectiveSpace k 1,
      η.hom ≫ projectiveSpaceToSpec k 1 = A.toSpec)
    (hself : ∀ A ∈ N, A.selfIntersectionNumber S.regularPoints_of_isSmooth = -2) :
    ∃ (V : NormalProjectiveSurface k)
      (hV : ∀ v : V.Point, RegularPoint V.toScheme v)
      (b : (CoverSurface).toScheme ⟶ V.toScheme)
      (Q : Bool × ↥(irreducibleComponents C) → V.PrimeCurve),
      (Ramification).card = N.card ∧ IsPointBlowupSequence CoverSurface V b ∧
      (∀ P ∈ Ramification, IsExceptionalCurve b P) ∧
      (∀ i, b.base '' (copyCurve i.1 i.2 : Set (CoverSurface).toScheme) =
          (Q i : Set V.toScheme) ∧
        ∃ η : (Q i).toScheme ≅ (copyCurve i.1 i.2).toScheme,
          η.hom ≫ ((copyCurve i.1 i.2).inclusion ≫ b) = (Q i).inclusion ∧
          η.hom ≫ (copyCurve i.1 i.2).toSpec = (Q i).toSpec ∧
          (Q i).selfIntersectionNumber hV = (copyCurve i.1 i.2).selfIntersectionNumber CoverRegular) ∧
      (∀ i j, V.primeCurveMatrix hV (Q i) (Q j) =
        if i.1 = j.1 then S.primeCurveMatrix S.regularPoints_of_isSmooth
          (baseCurve i.2) (baseCurve j.2) else 0) ∧
      (negativeGram (V.numericalIntersectionBilinForm hV)
        (fun i => curveClass V hV (Q i))).PosDef ∧
      LinearIndependent ℚ (fun i => curveClass V hV (Q i)) ∧
      Nat.card (Set.range Q) = 2 * Nat.card ↥(irreducibleComponents C) ∧
      Module.finrank ℚ (Submodule.span ℚ (Set.range (fun i => curveClass V hV (Q i)))) =
        2 * Nat.card ↥(irreducibleComponents C) := by
  have hsm : IsSmooth
      ((effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).gluedTo ≫ S.structureMorphism) := by
    rw [hIJ]
    exact S.selectedPrimeUnion_isSmooth N hSelectedDisj hcurves
  have hsource : (negativeGram ((CoverSurface).numericalIntersectionBilinForm CoverRegular)
      (fun i : Bool × ↥(irreducibleComponents C) =>
        curveClass CoverSurface CoverRegular (copyCurve i.1 i.2))).PosDef :=
    actual_doubled_negativeGram_posDef S sC hdim hTree htrans eC E hE L e h2 hred hne hsm
      f hdisj r hr hbir hcontracted
  obtain ⟨V, hV, b, Q, hcard, hseq, hcontract, hQ, hmatrix⟩ :=
    exists_ramification_blowdowns_with_tree_family S sC hdim hTree htrans eC E hE L e h2 hred hne
      f hdisj N hIJ hSelectedDisj hcurves hweil hP1 hself
  have hpair := PrimeCurveFamilyIntersectionGram.intersections_eq_of_matrix_eq
    CoverSurface V CoverRegular hV
    (fun i : Bool × ↥(irreducibleComponents C) => copyCurve i.1 i.2) Q hmatrix
  have hgram := PrimeCurveFamilyIntersectionGram.negativeGram_eq_of_matrix_eq
    CoverSurface V CoverRegular hV
    (fun i : Bool × ↥(irreducibleComponents C) => copyCurve i.1 i.2) Q hmatrix
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
  refine ⟨V, hV, b, Q, hcard, hseq, hcontract, hQ, ?_, hpos, hLI, ?_, ?_⟩
  · intro i j
    calc
      V.primeCurveMatrix hV (Q i) (Q j) =
          (CoverSurface).primeCurveMatrix CoverRegular (copyCurve i.1 i.2) (copyCurve j.1 j.2) :=
        hpair i j
      _ = _ := actual_doubled_intersectionMatrix S sC hdim hTree htrans eC E hE L e h2 hred hne hsm
        f hdisj i j
  · rw [Nat.card_range_of_injective hinj, Nat.card_prod]
    have hBool : Nat.card Bool = 2 := by simp only [Nat.card_eq_fintype_card, Fintype.card_bool]
    rw [hBool]
  · rw [finrank_span_eq_card hLI, Fintype.card_prod, Fintype.card_bool, Nat.card_eq_fintype_card]

end KltDP.Geometry.OriginalUnbranchedRationalTreeGeometry

#print axioms KltDP.Geometry.OriginalUnbranchedRationalTreeGeometry.exists_ramification_blowdowns_with_doubled_tree_rank
