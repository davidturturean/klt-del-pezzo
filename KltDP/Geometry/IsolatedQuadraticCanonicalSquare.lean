import KltDP.Geometry.OriginalQuadraticCanonicalIntersections
import KltDP.Geometry.MinimalResolutionSelectedBranchSmoothOne
import KltDP.Geometry.MinimalResolutionQuadraticRegular
import KltDP.Geometry.RationalPrimeCurveAdjunction

/-!
# The original isolated klt branch supplies the canonical-square hypotheses

The actual minimal klt resolution supplies projective-line isomorphisms
of its selected exceptional primes. Their original minus-two squares give
canonical degree zero by adjunction. Geometric isolation supplies the
disjoint smooth branch, so the canonical-square formula applies to the
same original quadratic cover without extra canonical-degree or smoothness
hypotheses.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory
universe u

namespace KltDP.Geometry.OriginalQuadraticCanonicalIntersection

open UnbranchedExceptionalBlocks OriginalCartierRamificationSmooth
open SmoothCanonicalCartierRepresentative

local instance isolatedCanonicalSquareModules (Y : Scheme.{u}) : MonoidalCategory Y.Modules :=
  Scheme.Modules.monoidalCategory Y

variable {k : Type u} [Field k] [IsAlgClosed k] {S X : NormalProjectiveSurface k}
  (π : S.toScheme ⟶ X.toScheme) (N : Finset S.PrimeCurve)
  (hmin : IsMinimalResolution S X π) (hklt : IsKlt X)
  (hiso : IsolatedSelection π N) (hN : ∀ C ∈ N, IsExceptionalCurve π C)

include hmin hklt hN in
/-- Actual exceptional rationality and the actual minus-two squares give
zero degree for the original canonical Cartier representative. -/
theorem selectedExceptional_canonicalDegree_zero
    [IsSmoothOfRelativeDimension 2 S.structureMorphism]
    (hself : ∀ C ∈ N, C.selfIntersectionNumber hmin.regular = -2) :
    ∀ C ∈ N, C.intersectionNumber (cartierRepresentative S.structureMorphism) = 0 := by
  letI : IsSmooth S.structureMorphism := IsSmoothOfRelativeDimension.isSmooth 2 S.structureMorphism
  intro C hC
  obtain ⟨η, hη⟩ := selectedExceptional_projectiveLine π N hmin hklt hN C hC
  have hz := RationalPrimeCurveAdjunction.antiCanonical_degree_of_minus_two S C η hη (hself C hC)
  rw [C.intersectionNumber_neg] at hz
  omega

local instance isolatedCanonicalSquareSeparated : S.toScheme.IsSeparated :=
  NormalProjectiveSurface.surfaceSeparated S

/-- The same cover over an original minimal klt resolution has canonical
square twice the original base square minus the actual branch count. -/
theorem isolatedSelection_canonical_selfIntersection
    (E : CartierDivisor S.toScheme) (hE : HasRegularCartierEquations S.toScheme E)
    (L : InvertibleSheaf S.toScheme)
    (e : L.obj ⊗ L.obj ≅ cartierDivisorModule S.toScheme E) (h2 : IsUnit (2 : k))
    (hred : IsReduced (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued)
    (hne : Nonempty (effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).glueData.glued)
    (hIJ : effectiveCartierIdealDataOfRegularEquations S.toScheme E hE =
      Scheme.IdealSheafData.vanishingIdeal (S.selectedPrimeClosedUnion N))
    (hselected : S.cartierToWeilHom E = S.selectedPrimeWeil N)
    (hself : ∀ C ∈ N, C.selfIntersectionNumber hmin.regular = -2) :
    letI : IsSmoothOfRelativeDimension 2 S.structureMorphism :=
      S.isSmoothOfRelativeDimension_two_of_regularPoints hmin.regular
    letI : IsSmoothOfRelativeDimension 1
        ((effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).gluedTo ≫ S.structureMorphism) :=
      isolatedSelection_canonicalBranch_isSmoothOne π N hmin hklt hiso hN E hE hIJ
    let T := OriginalCartierQuadraticIntegral.normalProjectiveSurface S E hE L e h2 hred hne
    let H := MinimalResolutionQuadraticRegular.selectedCover_regularPoints
      π hmin E hE L e h2 hred hne N hIJ (isolatedSelection_pairwise π N hiso hN)
      (selectedExceptional_isSmooth π N hmin hklt hN)
    letI : IsIntegral T.toScheme := T.integral
    letI : IsSmoothOfRelativeDimension 2 T.structureMorphism :=
      originalCover_smoothTwo S E hE L e h2 hred hne
    T.intersectionPairing H (cartierRepresentative T.structureMorphism)
        (cartierRepresentative T.structureMorphism) =
      2 * S.intersectionPairing hmin.regular (cartierRepresentative S.structureMorphism)
        (cartierRepresentative S.structureMorphism) - (N.card : ℤ) := by
  letI : IsSmoothOfRelativeDimension 2 S.structureMorphism :=
    S.isSmoothOfRelativeDimension_two_of_regularPoints hmin.regular
  letI : IsSmoothOfRelativeDimension 1
      ((effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).gluedTo ≫ S.structureMorphism) :=
    isolatedSelection_canonicalBranch_isSmoothOne π N hmin hklt hiso hN E hE hIJ
  exact selected_canonical_selfIntersection S E hE L e h2 hred hne hmin.regular
    (MinimalResolutionQuadraticRegular.selectedCover_regularPoints
      π hmin E hE L e h2 hred hne N hIJ (isolatedSelection_pairwise π N hiso hN)
      (selectedExceptional_isSmooth π N hmin hklt hN)) N hselected
    (isolatedSelection_pairwise π N hiso hN) hself
    (selectedExceptional_canonicalDegree_zero π N hmin hklt hN hself)

end KltDP.Geometry.OriginalQuadraticCanonicalIntersection

#print axioms KltDP.Geometry.OriginalQuadraticCanonicalIntersection.isolatedSelection_canonical_selfIntersection
