import KltDP.Geometry.BirationalAnticanonicalPairingSign
import KltDP.Geometry.MinimalResolutionSelectedBranchSmoothOne
import KltDP.Geometry.MinimalResolutionQuadraticRegular
import KltDP.Geometry.OriginalQuadraticCanonicalIntersections
import KltDP.Geometry.SelectedExceptionalHalfLinePairing
import KltDP.Geometry.DelPezzoType

/-!
# Actual nef anticanonical pullbacks have negative original-cover canonical degree

The original klt del Pezzo predicate supplies a positive ample Cartier
numerator of the negative canonical class. Its actual pullback to the
minimal resolution is nef, and the compatible canonical pushforward gives
negative canonical pairing. The selected exceptional half-line has zero
pairing with that same pullback. The original quadratic canonical formula
then gives negative canonical pairing on the same original cover, against
an actual nef pulled invertible sheaf.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory
universe u

namespace KltDP.Geometry.UnbranchedExceptionalBlocks

open NormalProjectiveSurface SmoothCanonicalCartierRepresentative
open OriginalCartierRamificationSmooth OriginalQuadraticCanonicalIntersection

variable {k : Type u} [Field k] [IsAlgClosed k] {S X : NormalProjectiveSurface k}
    (π : S.toScheme ⟶ X.toScheme) (N : Finset S.PrimeCurve)
    [IsProper π] (hbir : IsBirationalScheme π)
    (hmin : IsMinimalResolution S X π) (hklt : IsKlt X)
    (hiso : IsolatedSelection π N) (hN : ∀ C ∈ N, IsExceptionalCurve π C)

local instance originalCoverAnticanonicalSignSeparated : S.toScheme.IsSeparated := surfaceSeparated S
local instance originalCoverAnticanonicalSignMonoidal : MonoidalCategory S.toScheme.Modules :=
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
    (hweil : S.cartierToWeilHom E = S.selectedPrimeWeil N)

local notation "CoverSurface" =>
  OriginalCartierQuadraticIntegral.normalProjectiveSurface S E hE L e h2 hred hne
local notation "CoverAtlas" => effectiveCartierQuadraticAtlas S.toScheme E hE L e
local notation "CoverRegular" =>
  MinimalResolutionQuadraticRegular.selectedCover_regularPoints π hmin E hE L e h2 hred hne N hIJ
    (isolatedSelection_pairwise π N hiso hN) (selectedExceptional_isSmooth π N hmin hklt hN)

include hbir hweil

/-- The actual del Pezzo class produces the nef test sheaves and both negative
canonical pairings on the unchanged minimal resolution and original cover. -/
theorem exists_anticanonical_nef_with_cover_canonical_negative (hDP : IsKltDelPezzo X) :
    letI : IsSmoothOfRelativeDimension 2 S.structureMorphism :=
      S.isSmoothOfRelativeDimension_two_of_regularPoints hmin.regular
    letI : IsSmoothOfRelativeDimension 1
        ((effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).gluedTo ≫ S.structureMorphism) :=
      isolatedSelection_canonicalBranch_isSmoothOne π N hmin hklt hiso hN E hE hIJ
    letI : IsIntegral (CoverSurface).toScheme := (CoverSurface).integral
    letI : IsSmoothOfRelativeDimension 2 (CoverSurface).structureMorphism :=
      originalCover_smoothTwo S E hE L e h2 hred hne
    ∃ KX : X.WeilDivisor, IsCanonicalWeilDivisor X KX ∧
      ∃ (n : ℕ) (A : CartierDivisor X.toScheme), 0 < n ∧
        X.cartierToWeilHom A = n • (-KX) ∧
        AmpleSerre.IsAmple (cartierDivisorInvertibleSheaf X.toScheme A) ∧
        let H := pullbackInvertibleSheaf π (cartierDivisorInvertibleSheaf X.toScheme A)
        Positivity.IsNef S.structureMorphism H ∧
        Positivity.IsNef (CoverSurface).structureMorphism (pullbackInvertibleSheaf (CoverAtlas).morphism H) ∧
        S.picardPairing hmin.regular
          (cartierPicardClass S.toScheme (cartierRepresentative S.structureMorphism) * L.toPic) H.toPic < 0 ∧
        (CoverSurface).picardPairing CoverRegular
          (cartierPicardClass (CoverSurface).toScheme (cartierRepresentative (CoverSurface).structureMorphism))
          (pullbackInvertibleSheaf (CoverAtlas).morphism H).toPic < 0 := by
  letI : IsSmoothOfRelativeDimension 2 S.structureMorphism :=
    S.isSmoothOfRelativeDimension_two_of_regularPoints hmin.regular
  letI : IsSmoothOfRelativeDimension 1
      ((effectiveCartierIdealDataOfRegularEquations S.toScheme E hE).gluedTo ≫ S.structureMorphism) :=
    isolatedSelection_canonicalBranch_isSmoothOne π N hmin hklt hiso hN E hE hIJ
  letI : IsIntegral (CoverSurface).toScheme := (CoverSurface).integral
  letI : IsSmoothOfRelativeDimension 2 (CoverSurface).structureMorphism :=
    originalCover_smoothTwo S E hE L e h2 hred hne
  letI : IsLocallyNoetherian X.toScheme := X.isLocallyNoetherian
  dsimp only
  obtain ⟨KX, hKX, n, hn, A, hA, hample⟩ := (isLogDelPezzoPair_zero_iff X).mp hDP
  have hAW : X.cartierToWeilHom A = n • (-KX) := by
    apply rationalizeWeilDivisor_injective
    simpa only [map_nsmul, map_neg] using hA
  let H := pullbackInvertibleSheaf π (cartierDivisorInvertibleSheaf X.toScheme A)
  have hclassPullback : schemePicardPullbackHom π (cartierPicardClass X.toScheme A) = H.toPic := by
    change schemePicardPullbackHom π (cartierDivisorInvertibleSheaf X.toScheme A).toPic =
      (pullbackInvertibleSheaf π (cartierDivisorInvertibleSheaf X.toScheme A)).toPic
    exact schemePicardPullbackHom_toPic π (cartierDivisorInvertibleSheaf X.toScheme A)
  have hnegative := BirationalAnticanonicalPairingSign.canonical_picardPairing_pullback_neg
    π hmin.toIsResolution.over_base hbir hmin.regular KX hKX.1 n hn A hAW hample
  rw [hclassPullback] at hnegative
  have hhalf := selectedExceptional_halfLinePairing_zero S X π hmin.toIsResolution.over_base
    hmin.regular N E hweil hN L e (cartierPicardClass X.toScheme A)
  rw [hclassPullback] at hhalf
  have htwisted : S.picardPairing hmin.regular
      (cartierPicardClass S.toScheme (cartierRepresentative S.structureMorphism) * L.toPic) H.toPic < 0 := by
    rw [S.picardPairing_mul_left_of_regular, hhalf, add_zero]
    exact hnegative
  have hcover : (CoverSurface).picardPairing CoverRegular
      (cartierPicardClass (CoverSurface).toScheme (cartierRepresentative (CoverSurface).structureMorphism))
      (pullbackInvertibleSheaf (CoverAtlas).morphism H).toPic < 0 := by
    calc
      _ = 2 * S.picardPairing hmin.regular
          (cartierPicardClass S.toScheme (cartierRepresentative S.structureMorphism) * L.toPic) H.toPic := by
        rw [← schemePicardPullbackHom_toPic]
        exact canonical_pairing_pullback S E hE L e h2 hred hne hmin.regular CoverRegular H.toPic
      _ < 0 := mul_neg_of_pos_of_neg (by norm_num) htwisted
  have hsemi : Positivity.IsSemiample H :=
    AmplePullbackNef.isSemiample_pullback_of_isAmple π (cartierDivisorInvertibleSheaf X.toScheme A) hample
  refine ⟨KX, hKX.1, n, A, hn, hAW, hample, ?_⟩
  exact ⟨AmpleNefUnconditional.isNef_of_isSemiample S H hsemi,
    AmpleNefUnconditional.isNef_of_isSemiample CoverSurface _
      (AmplePullbackNef.isSemiample_pullback (CoverAtlas).morphism H hsemi), htwisted, hcover⟩

end KltDP.Geometry.UnbranchedExceptionalBlocks

#print axioms KltDP.Geometry.UnbranchedExceptionalBlocks.exists_anticanonical_nef_with_cover_canonical_negative
