import KltDP.Geometry.OriginalUnbranchedTreeRamificationDisjoint
import KltDP.Geometry.SelectedRamificationMinusOne
import KltDP.Geometry.BlowdownSurvivingCurveFamily

/-!
# One actual ramification blowdown retains the whole original doubled tree

The original disjoint rational minus-two branch selection gives the actual
ramification minus-one curves. Every coherent original tree component
avoids them by the proved original projection argument. A single produced
blowdown therefore retains every component under both labels, its original
curve scheme and maps, and the complete unchanged intersection matrix.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace
universe u

namespace KltDP.Geometry.OriginalUnbranchedRationalTreeGeometry

open NormalProjectiveSurface RationalTreePicard

variable {k : Type u} [Field k] [IsAlgClosed k] (S : NormalProjectiveSurface k)
    [IsSmooth S.structureMorphism]

local instance originalUnbranchedTreeBlowdownSeparated : S.toScheme.IsSeparated := surfaceSeparated S
local instance originalUnbranchedTreeBlowdownMonoidal : MonoidalCategory S.toScheme.Modules :=
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

include hweil

/-- The same actual blowdown and target family preserve all original maps and the full tree matrix. -/
theorem exists_ramification_blowdowns_with_tree_family
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
      NullCurveIntersectionMatrix.intersectionMatrix V hV Q =
        NullCurveIntersectionMatrix.intersectionMatrix CoverSurface CoverRegular
          (fun i : Bool × ↥(irreducibleComponents C) => copyCurve i.1 i.2) := by
  classical
  obtain ⟨hcard, hpair, hminus⟩ := S.selectedRamificationPrimeSet_disjoint_minusOne
    N E hE L e h2 hred hne hIJ hSelectedDisj hcurves hweil hP1 hself
  let P : {P : (CoverSurface).PrimeCurve // P ∈ Ramification} → (CoverSurface).PrimeCurve := Subtype.val
  have hm (j : {P : (CoverSurface).PrimeCurve // P ∈ Ramification}) :
      IsMinusOneCurve CoverRegular (P j) := hminus j.val j.property
  have hp : Pairwise (fun i j =>
      Disjoint (P i : Set (CoverSurface).toScheme) (P j : Set (CoverSurface).toScheme)) := by
    intro i j hij
    exact @hpair i.val i.property j.val j.property (fun h => hij (Subtype.ext h))
  have ha (i : Bool × ↥(irreducibleComponents C))
      (j : {P : (CoverSurface).PrimeCurve // P ∈ Ramification}) :
      Disjoint (copyCurve i.1 i.2 : Set (CoverSurface).toScheme) (P j : Set (CoverSurface).toScheme) :=
    liftedCurve_disjoint_selectedRamification S sC hdim hTree htrans eC E hE L e h2 hred hne
      f hdisj N hIJ i.1 i.2 j.val j.property
  obtain ⟨V, hV, b, Q, hseq, hcontract, hQ, hmatrix⟩ :=
    KltDP.Geometry.exists_blowdowns_with_surviving_family CoverSurface CoverRegular P hm hp
      (fun i : Bool × ↥(irreducibleComponents C) => copyCurve i.1 i.2) ha
  exact ⟨V, hV, b, Q, hcard, hseq, fun j hj => hcontract ⟨j, hj⟩, hQ, hmatrix⟩

end KltDP.Geometry.OriginalUnbranchedRationalTreeGeometry

#print axioms KltDP.Geometry.OriginalUnbranchedRationalTreeGeometry.exists_ramification_blowdowns_with_tree_family
