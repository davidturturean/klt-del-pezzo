import KltDP.Geometry.OriginalUnbranchedTreeBlowdownRank
import KltDP.Geometry.NegativePrimeFamilyPicardRank

/-!
# Strict Picard rank on the same actual tree-preserving blowdown

The actual target family and all its maps are retained from the single
ramification blowdown. Its proved doubled negative Gram combines with
the target's actual projective Hodge direction, so twice the original
tree component count is strictly below the original target Picard rank.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace
universe u

namespace KltDP.Geometry.OriginalUnbranchedRationalTreeGeometry

open NormalProjectiveSurface RationalTreePicard DisjointNegativeCurvesRank
open KltDP.LinearAlgebra.CanonicalCorrection

variable {k : Type u} [Field k] [IsAlgClosed k] (S : NormalProjectiveSurface k)
    [IsSmooth S.structureMorphism]

local instance originalUnbranchedTreePicardBoundSeparated : S.toScheme.IsSeparated := surfaceSeparated S
local instance originalUnbranchedTreePicardBoundMonoidal : MonoidalCategory S.toScheme.Modules :=
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

local instance originalUnbranchedTreePicardBoundFintype : Fintype ↥(irreducibleComponents C) :=
  NoetherianSpace.finite_irreducibleComponents.fintype

local notation "baseCurve" => RationalComponentPrimeCurves.curve S f eC

variable {X : NormalProjectiveSurface k} (r : S.toScheme ⟶ X.toScheme) [IsProper r]
    (hr : r ≫ X.structureMorphism = S.structureMorphism) (hbir : IsBirationalScheme r)
    (hcontracted : ∀ D : ↥(irreducibleComponents C),
      IsExceptionalCurve r (RationalComponentPrimeCurves.curve S f eC D))

include hweil hr hbir hcontracted

/-- The actual target has room for both original tree sheets and a positive Picard direction. -/
theorem exists_ramification_blowdowns_with_tree_picard_bound
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
      Nat.card (Set.range Q) = 2 * Nat.card ↥(irreducibleComponents C) ∧
      2 * Nat.card ↥(irreducibleComponents C) < V.picardRank := by
  obtain ⟨V, hV, b, Q, hcard, hseq, hcontract, hQ, hmatrix, hpos, hLI, hcount, hspan⟩ :=
    exists_ramification_blowdowns_with_doubled_tree_rank S sC hdim hTree htrans eC E hE L e h2 hred hne
      f hdisj N hIJ hSelectedDisj hcurves hweil r hr hbir hcontracted hP1 hself
  refine ⟨V, hV, b, Q, hcard, hseq, hcontract, hQ, hmatrix, hcount, ?_⟩
  have h := V.primeFamily_card_lt_picardRank_of_negativeGram hV Q hpos
  simpa only [Fintype.card_prod, Fintype.card_bool, Nat.card_eq_fintype_card] using h

end KltDP.Geometry.OriginalUnbranchedRationalTreeGeometry

#print axioms KltDP.Geometry.OriginalUnbranchedRationalTreeGeometry.exists_ramification_blowdowns_with_tree_picard_bound
