import KltDP.Geometry.FrobeniusTargetDelPezzoType

/-!
# The actual positive Frobenius construction is of del Pezzo type

Choose the existing original rank-one KLT contraction once. Its target,
map, ample line, positive exponent and canonical representative are kept.
The exact positive coefficient then supplies Q-ampleness of the negative
canonical divisor on this same target, with boundary zero.
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

/-- In the positive-coefficient range the original rank-one contraction
is klt del Pezzo, retaining the actual minimal resolution and ample power. -/
theorem exists_normal_projective_surface_rank_one_delPezzoType
    {k : Type u} [Field k] [IsAlgClosed k]
    (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
    (a : Fin n → k) (ha : Function.Injective a) (hn : 2 < n)
    (hd : (0 : ℤ) < 2 - ((q + 1 : ℕ) - (2 : ℤ)) * ((n : ℤ) - 2)) :
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
        S.QAmple (-rationalizeWeilDivisor S KX) ∧ IsKltDelPezzo S ∧ IsDelPezzoType S := by
  letI : IsIntegral (multiSurface (q + 1) n a) :=
    multiSurface_isIntegral (q + 1) n a ha
  obtain ⟨m, hm, S, π, hπ, hproper, hsurj, hbir, hc, hgeom,
      hpoints, hcriterion, A, hA, ⟨e⟩, hdim, hrank, hminimal, hKlt, hIsKlt⟩ :=
    exists_normal_projective_surface_rank_one_klt q n a ha hn
  letI : IsProper π := hproper
  letI : Surjective π := hsurj
  letI : IsIso π.c := hc
  let KX := targetCanonicalWeil q n a ha hn S π hπ hbir hpoints hcriterion
  have hQAmple : S.QAmple (-rationalizeWeilDivisor S KX) :=
    targetCanonicalWeil_neg_qAmple
      q n a ha hn S π hπ hbir hpoints hcriterion A m hm e hA hd
  have hDelPezzo : IsKltDelPezzo S :=
    (isLogDelPezzoPair_zero_iff S).mpr ⟨KX, hKlt, hQAmple⟩
  exact ⟨m, hm, S, π, hπ, hproper, hsurj, hbir, hc, hgeom,
    hpoints, hcriterion, A, hA, ⟨e⟩, hdim, hrank, hminimal, hKlt, hIsKlt,
    hQAmple, hDelPezzo, isDelPezzoType_of_isKltDelPezzo S hDelPezzo⟩

end KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction
