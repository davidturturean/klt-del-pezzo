import KltDP.Geometry.OriginalUnbranchedForestCopies
import KltDP.Geometry.OriginalUnbranchedRationalTreeIntersectionMatrix
import KltDP.Geometry.DisjointNegativeCurvesRank
import KltDP.Geometry.MinimalResolutionQuadraticRegular

/-!
# The complete doubled matrix of all actual unbranched exceptional blocks

Within an original block, the checked coherent tree splitting preserves
all original intersections on each sheet. Distinct blocks are disjoint
by the actual original projections. Opposite sheets are disjoint in
every case. Thus the whole original forest, under both labels, has two
copies of the original exceptional submatrix on the unchanged cover.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace
universe u

namespace KltDP.Geometry.UnbranchedExceptionalBlocks

open NormalProjectiveSurface ActualExceptionalIncidence ExceptionalForestClosedBlocks RationalTreePicard

variable {k : Type u} [Field k] [IsAlgClosed k] {S X : NormalProjectiveSurface k}
    (π : S.toScheme ⟶ X.toScheme) (N : Finset S.PrimeCurve)
    [IsProper π] (hbir : IsBirationalScheme π)
    (hmin : IsMinimalResolution S X π) (hklt : IsKlt X)

local instance originalUnbranchedForestMatrixSeparated : S.toScheme.IsSeparated := surfaceSeparated S
local instance originalUnbranchedForestMatrixMonoidal : MonoidalCategory S.toScheme.Modules :=
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

variable (hsm : IsSmooth
  ((effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).gluedTo ≫ S.structureMorphism))

local notation "CoverRegular" =>
  MinimalResolutionQuadraticRegular.cover_regularPoints
    π hmin E hE L e h2 hred hne hsm
local notation "copy" => forestCurve π N hbir hmin hklt E hE L e h2 hred hne hIJ hiso
local notation "base" => baseCurve π N hbir hmin hklt

private theorem prime_intersection_zero_of_disjoint
    (Y : NormalProjectiveSurface k) (hY : ∀ y : Y.Point, RegularPoint Y.toScheme y)
    (A B : Y.PrimeCurve) (h : Disjoint (A : Set Y.toScheme) (B : Set Y.toScheme)) :
    A.intersectionNumber (Y.primeCurveCartier hY B) = 0 := by
  have hz := DisjointNegativeCurvesRank.curveClass_pairing_eq_zero_of_disjoint Y hY A B h
  rw [DisjointNegativeCurvesRank.curveClass_pairing,
    PrimeCurvePairingSupport.intersectionPairing_primeCurves_eq_intersectionNumber Y hY A B] at hz
  exact_mod_cast hz

/-- The same coherent label preserves all original intersections across the complete forest. -/
theorem forestCurve_intersection_same (ε : Bool) (i j : Components π N hbir) :
    (copy ε i).intersectionNumber ((CoverSurface).primeCurveCartier CoverRegular (copy ε j)) =
      (base i).intersectionNumber (S.primeCurveCartier hmin.regular (base j)) := by
  letI : IsSmooth S.structureMorphism := MinimalResolutionQuadraticRegular.source_isSmooth π hmin
  rcases i with ⟨b, D⟩
  rcases j with ⟨c, F⟩
  by_cases hbc : b = c
  · subst c
    exact OriginalUnbranchedRationalTreeGeometry.liftedCurve_intersection_same S
      (blockInclusion π hbir b.val ≫ S.structureMorphism)
      (blockScheme_dimension_le_one π hbir b.val)
      (block_componentPointIncidenceGraph_isTree π hbir b.val hmin hklt)
      (block_hasTransverseComponentBranches π hbir b.val hmin hklt)
      (blockComponentProjectiveLineIso π hbir b.val hmin hklt)
      E hE L e h2 hred hne hsm (blockInclusion π hbir b.val)
      (blockInclusion_disjoint_canonicalBranch π N hiso hbir E hE hIJ b) ε D F
  · rw [prime_intersection_zero_of_disjoint CoverSurface CoverRegular _ _
      (forestCurve_disjoint_blocks π N hbir hmin hklt E hE L e h2 hred hne hIJ hiso
        ε ε ⟨b, D⟩ ⟨c, F⟩ hbc),
      prime_intersection_zero_of_disjoint S hmin.regular _ _
        (baseCurve_disjoint_of_block_ne π N hbir hmin hklt ⟨b, D⟩ ⟨c, F⟩ hbc)]

/-- Opposite coherent labels are disjoint across the complete original forest. -/
theorem forestCurve_disjoint_opposite (ε : Bool) (i j : Components π N hbir) :
    Disjoint (copy ε i : Set (CoverSurface).toScheme) (copy (!ε) j : Set (CoverSurface).toScheme) := by
  letI : IsSmooth S.structureMorphism := MinimalResolutionQuadraticRegular.source_isSmooth π hmin
  rcases i with ⟨b, D⟩
  rcases j with ⟨c, F⟩
  by_cases hbc : b = c
  · subst c
    exact OriginalUnbranchedRationalTreeGeometry.liftedCurve_disjoint_opposite S
      (blockInclusion π hbir b.val ≫ S.structureMorphism)
      (blockScheme_dimension_le_one π hbir b.val)
      (block_componentPointIncidenceGraph_isTree π hbir b.val hmin hklt)
      (block_hasTransverseComponentBranches π hbir b.val hmin hklt)
      (blockComponentProjectiveLineIso π hbir b.val hmin hklt)
      E hE L e h2 hred hne (blockInclusion π hbir b.val)
      (blockInclusion_disjoint_canonicalBranch π N hiso hbir E hE hIJ b) ε D F
  · exact forestCurve_disjoint_blocks π N hbir hmin hklt E hE L e h2 hred hne hIJ hiso
      ε (!ε) ⟨b, D⟩ ⟨c, F⟩ hbc

/-- Every opposite-label entry is zero in the complete actual cover matrix. -/
theorem forestCurve_intersection_opposite (ε : Bool) (i j : Components π N hbir) :
    (copy ε i).intersectionNumber ((CoverSurface).primeCurveCartier CoverRegular (copy (!ε) j)) = 0 :=
  prime_intersection_zero_of_disjoint CoverSurface CoverRegular _ _
    (forestCurve_disjoint_opposite π N hbir hmin hklt E hE L e h2 hred hne hIJ hiso ε i j)

/-- The literal full doubled intersection matrix on all original unbranched blocks. -/
theorem forestCurve_actual_doubled_matrix (i j : Bool × Components π N hbir) :
    (CoverSurface).primeCurveMatrix CoverRegular (copy i.1 i.2) (copy j.1 j.2) =
      if i.1 = j.1 then S.primeCurveMatrix hmin.regular (base i.2) (base j.2) else 0 := by
  rcases i with ⟨ε, D⟩
  rcases j with ⟨δ, F⟩
  dsimp only
  by_cases h : ε = δ
  · subst δ
    rw [if_pos rfl]
    exact forestCurve_intersection_same π N hbir hmin hklt E hE L e h2 hred hne hIJ hiso hsm ε D F
  · rw [if_neg h]
    have hδ : δ = !ε := by
      cases ε <;> cases δ <;> first | rfl | exact False.elim (h rfl)
    subst δ
    exact forestCurve_intersection_opposite π N hbir hmin hklt E hE L e h2 hred hne hIJ hiso hsm ε D F

end KltDP.Geometry.UnbranchedExceptionalBlocks

#print axioms KltDP.Geometry.UnbranchedExceptionalBlocks.forestCurve_actual_doubled_matrix
#print axioms KltDP.Geometry.UnbranchedExceptionalBlocks.forestCurve_disjoint_opposite
