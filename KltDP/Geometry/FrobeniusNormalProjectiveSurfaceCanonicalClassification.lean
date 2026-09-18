import KltDP.Geometry.FrobeniusNormalProjectiveSurfaceKlt
import KltDP.Geometry.FrobeniusTargetAnticanonicalAmpleIff
import KltDP.Geometry.FrobeniusTargetCanonicalSignCases

/-!
# Actual KLT Frobenius targets in every canonical-sign case

The original contraction is constructed for every prime parameter and every
n > 2. The same target, canonical representative, ample line, exponent and
minimal resolution realize the complete canonical-sign classification.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction

open KltDP.Examples FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
open FrobeniusProjectivityProved InvertibleSheafSectionPowers NormalProjectiveSurface
open FrobeniusMultiCentreCanonicalWeilRepresentatives

local instance {k : Type u} [Field k] (T : NormalProjectiveSurface k) :
    IsLocallyNoetherian T.toScheme := T.isLocallyNoetherian

/-- The rank-one KLT examples exist in all three canonical-sign ranges.
The anticanonical ample cases are exact and use the same constructed target. -/
theorem exists_normal_projective_surface_canonical_classification
    {k : Type u} [Field k] [IsAlgClosed k]
    (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
    (a : Fin n → k) (ha : Function.Injective a) (hn : 2 < n) :
    letI : IsIntegral (multiSurface (q + 1) n a) :=
      multiSurface_isIntegral (q + 1) n a ha
    let source := sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)
    ∃ m : ℕ, 0 < m ∧ ∃ (S : NormalProjectiveSurface k)
      (π : source.toScheme ⟶ S.toScheme)
      (hπ : π ≫ S.structureMorphism = multiStructure (q + 1) n a)
      (hproper : IsProper π) (hsurj : Surjective π)
      (hbir : IsBirationalScheme π) (hc : IsIso π.c),
      letI : IsProper π := hproper
      letI : Surjective π := hsurj
      letI : IsIso π.c := hc
      (∀ (L : Type u) [Field L] (y : Spec (CommRingCat.of L) ⟶ S.toScheme),
        ConnectedSpace (pullback π y : Scheme.{u})) ∧
      ∃ (hpoints : ∀ y : S.toScheme, IsConnected (π.base ⁻¹' {y}))
        (hcriterion : ∀ C : source.PrimeCurve,
          (∃ p : Spec (CommRingCat.of k) ⟶ S.toScheme,
            C.inclusion ≫ π = C.toSpec ≫ p ∧ p ≫ S.structureMorphism = 𝟙 _) ↔
          C.restrictionDegree (originalLine q n a ha) = 0),
      ∃ A : InvertibleSheaf S.toScheme, AmpleSerre.IsAmple A ∧
        Nonempty ((pullbackInvertibleSheaf π A).obj ≅ (power (originalLine q n a ha) m).obj) ∧
        S.NumericalSpaceFiniteDimensional ∧ S.picardRank = 1 ∧
        IsMinimalResolution source S π ∧
        let KX := targetCanonicalWeil q n a ha hn S π hπ hbir hpoints hcriterion
        IsKltWithCanonicalDivisor S KX ∧ IsKlt S ∧
        (S.QAmple (-rationalizeWeilDivisor S KX) ↔
          q + 1 = 2 ∨ (q + 1 = 3 ∧ n = 3)) ∧
        (((q + 1 = 2 ∨ (q + 1 = 3 ∧ n = 3)) ∧
            S.QAmple (-rationalizeWeilDivisor S KX)) ∨
          ((q + 1 = 3 ∧ n = 4) ∧
            S.QLinearlyEquivalent (rationalizeWeilDivisor S KX) 0) ∨
          ((q + 1 ≠ 2 ∧ (q + 1 ≠ 3 ∨ 5 ≤ n)) ∧
            S.QAmple (rationalizeWeilDivisor S KX))) := by
  letI : IsIntegral (multiSurface (q + 1) n a) :=
    multiSurface_isIntegral (q + 1) n a ha
  obtain ⟨m, hm, S, π, hπ, hproper, hsurj, hbir, hc, hgeom,
      hpoints, hcriterion, A, hA, ⟨e⟩, hdim, hrank, hminimal, hKlt, hIsKlt⟩ :=
    exists_normal_projective_surface_rank_one_klt q n a ha hn
  letI : IsProper π := hproper
  letI : Surjective π := hsurj
  letI : IsIso π.c := hc
  refine ⟨m, hm, S, π, hπ, hproper, hsurj, hbir, hc, hgeom,
    hpoints, hcriterion, A, hA, ⟨e⟩, hdim, hrank, hminimal, hKlt, hIsKlt, ?_, ?_⟩
  · exact targetCanonicalWeil_neg_qAmple_iff_parameters
      q n a ha hn S π hπ hbir hpoints hcriterion A m hm e hA
  · exact targetCanonicalWeil_parameter_sign_cases
      q n a ha hn S π hπ hbir hpoints hcriterion A m hm e hA

end KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction

#check @KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction.exists_normal_projective_surface_canonical_classification
#print axioms KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction.exists_normal_projective_surface_canonical_classification
