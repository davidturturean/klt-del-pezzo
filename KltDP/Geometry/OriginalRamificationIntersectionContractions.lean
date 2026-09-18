import KltDP.Geometry.SelectedRamificationMinusOne
import KltDP.Geometry.FiniteDisjointCurveIntersectionContractions
import KltDP.Geometry.GeneralMinimalResolutionExistence

/-!
# Original ramification blowdowns preserving the complete surviving pairing

The unchanged quadratic cover and its actual ramification images supply
all curves for the finite contraction theorem. Rationality, minus-one
self-intersection, pairwise disjointness, and the exact size of the family
are derived from the original selected rational minus-two curves.
Every original curve disjoint from that family keeps its curve scheme,
its map over the field, and its self-intersection on the final surface.
The same original blowdown morphism preserves every pairwise intersection
between surviving original curves, even when they meet each other.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace
universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k] (S : NormalProjectiveSurface k)
    [IsSmooth S.structureMorphism]

local instance selectedIntersectionContractionsSeparated : S.toScheme.IsSeparated := surfaceSeparated S
local instance selectedIntersectionContractionsMonoidal : MonoidalCategory S.toScheme.Modules :=
  Scheme.Modules.monoidalCategory S.toScheme

variable (N : Finset S.PrimeCurve) (E : CartierDivisor S.toScheme)
    (hE : HasRegularCartierEquations S.toScheme E) (L : InvertibleSheaf S.toScheme)
    (e : L.obj ⊗ L.obj ≅ cartierDivisorModule S.toScheme E) (h2 : IsUnit (2 : k))
    (hred : IsReduced
      (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued)
    (hne : Nonempty
      (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued)
    (hIJ : effectiveCartierIdealDataOfRegularEquations S.toScheme E hE =
      Scheme.IdealSheafData.vanishingIdeal (S.selectedPrimeClosedUnion N))
    (hdisj : (N : Set S.PrimeCurve).Pairwise fun C D =>
      Disjoint (C : Set S.toScheme) (D : Set S.toScheme))
    (hcurves : ∀ C ∈ N, IsSmooth C.toSpec)
    (hweil : S.cartierToWeilHom E = S.selectedPrimeWeil N)

local notation "T" => OriginalCartierQuadraticIntegral.normalProjectiveSurface S E hE L e h2 hred hne
local notation "M" => S.selectedRamificationPrimeSet N E hE L e h2 hred hne hIJ
local notation "H" => S.selectedRamificationCover_regularPoints N E hE L e h2 hred hne hIJ hdisj hcurves

include hweil

/-- Contract all actual selected ramification curves, preserving disjoint original curves. -/
theorem exists_selectedRamification_blowdowns_preserving_intersections
    (hP1 : ∀ C ∈ N, ∃ η : C.toScheme ≅ projectiveSpace k 1,
      η.hom ≫ projectiveSpaceToSpec k 1 = C.toSpec)
    (hself : ∀ C ∈ N, C.selfIntersectionNumber S.regularPoints_of_isSmooth = -2) :
    ∃ (V : NormalProjectiveSurface k)
      (hV : ∀ v : V.Point, RegularPoint V.toScheme v) (b : (T).toScheme ⟶ V.toScheme),
      (M).card = N.card ∧ IsPointBlowupSequence T V b ∧
      (∀ P ∈ M, IsExceptionalCurve b P) ∧
      (∀ D : (T).PrimeCurve,
        (∀ P ∈ M, Disjoint (D : Set (T).toScheme) (P : Set (T).toScheme)) →
        ∃ D' : V.PrimeCurve, b.base '' (D : Set (T).toScheme) = (D' : Set V.toScheme) ∧
          ∃ η : D'.toScheme ≅ D.toScheme,
            η.hom ≫ (D.inclusion ≫ b) = D'.inclusion ∧
            η.hom ≫ D.toSpec = D'.toSpec ∧
            D'.selfIntersectionNumber hV = D.selfIntersectionNumber H) ∧
      ∀ A B : (T).PrimeCurve,
        (∀ P ∈ M, Disjoint (A : Set (T).toScheme) (P : Set (T).toScheme)) →
        (∀ P ∈ M, Disjoint (B : Set (T).toScheme) (P : Set (T).toScheme)) →
        ∀ A' B' : V.PrimeCurve,
          b.base '' (A : Set (T).toScheme) = (A' : Set V.toScheme) →
          b.base '' (B : Set (T).toScheme) = (B' : Set V.toScheme) →
          A'.intersectionNumber (V.primeCurveCartier hV B') =
            A.intersectionNumber ((T).primeCurveCartier H B) := by
  classical
  obtain ⟨hcard, hpair, hminus⟩ := S.selectedRamificationPrimeSet_disjoint_minusOne
    N E hE L e h2 hred hne hIJ hdisj hcurves hweil hP1 hself
  let C : {P : (T).PrimeCurve // P ∈ M} → (T).PrimeCurve := Subtype.val
  have hm (P : {P : (T).PrimeCurve // P ∈ M}) : IsMinusOneCurve H (C P) :=
    hminus P.val P.property
  have hp : Pairwise (fun P Q =>
      Disjoint (C P : Set (T).toScheme) (C Q : Set (T).toScheme)) := by
    intro P Q hPQ
    exact @hpair P.val P.property Q.val Q.property (fun h => hPQ (Subtype.ext h))
  obtain ⟨V, hV, b, hseq, hcontract, hpreserve, hpairing⟩ :=
    KltDP.Geometry.exists_contract_disjoint_family_intersections
      (GeneralResolution.contraction k) T H C hm hp
  refine ⟨V, hV, b, hcard, hseq, ?_, ?_, ?_⟩
  · intro P hP
    exact hcontract ⟨P, hP⟩
  · intro D hD
    exact hpreserve D (fun P => hD P.val P.property)
  · intro A B hA hB A' B' himA himB
    exact hpairing A B (fun P => hA P.val P.property)
      (fun P => hB P.val P.property) A' B' himA himB

end KltDP.Geometry.NormalProjectiveSurface

#print axioms KltDP.Geometry.NormalProjectiveSurface.exists_selectedRamification_blowdowns_preserving_intersections
