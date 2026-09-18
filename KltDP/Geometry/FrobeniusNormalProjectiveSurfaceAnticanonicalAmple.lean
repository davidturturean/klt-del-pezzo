import KltDP.Examples.FrobeniusAnticanonicalParameterCases
import KltDP.Examples.FrobeniusMultiCentreTargetAnticanonicalAmple
import KltDP.Geometry.FrobeniusNormalProjectiveSurfaceMinimalQCartier

/-!
# Original minimal resolutions with an ample anticanonical multiple

For the explicit positive-coefficient parameter cases, choose the original
minimal-resolution witness once. The same target canonical Weil divisor has
an actual positive Cartier multiple whose original invertible sheaf is ample.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction

open KltDP.Examples FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
open FrobeniusProjectivityProved InvertibleSheafSectionPowers NormalProjectiveSurface
open FrobeniusMultiCentreCanonicalWeilRepresentatives

variable {k : Type u} [Field k] [IsAlgClosed k]
    (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
    (a : Fin n → k) (ha : Function.Injective a)

/-- In the exact positive-coefficient cases, the original constructed target
has a positive ample Cartier multiple of its actual anticanonical divisor. -/
theorem exists_minimal_resolution_ample_anticanonical_multiple (hn : 2 < n)
    (hcases : q = 1 ∨ (q = 2 ∧ n = 3)) :
    letI : IsIntegral (multiSurface (q + 1) n a) :=
      multiSurface_isIntegral (q + 1) n a ha
    ∃ m : ℕ, 0 < m ∧ ∃ (S : NormalProjectiveSurface k)
      (π : multiSurface (q + 1) n a ⟶ S.toScheme)
      (hπ : π ≫ S.structureMorphism = multiStructure (q + 1) n a)
      (hproper : IsProper π) (hsurj : Surjective π)
      (hbir : IsBirationalScheme π) (hc : IsIso π.c),
      letI : IsProper π := hproper
      letI : Surjective π := hsurj
      letI : IsIso π.c := hc
      ∃ (hpoints : ∀ y : S.toScheme, IsConnected (π.base ⁻¹' {y}))
        (hcriterion : ∀ C : (sourceSurface q n a ha
            (originalMultiStructureProjective k (q + 1) n a)).PrimeCurve,
          (∃ p : Spec (CommRingCat.of k) ⟶ S.toScheme,
            C.inclusion ≫ π = C.toSpec ≫ p ∧ p ≫ S.structureMorphism = 𝟙 _) ↔
          C.restrictionDegree (originalLine q n a ha) = 0),
      ∃ A : InvertibleSheaf S.toScheme, AmpleSerre.IsAmple A ∧
        Nonempty ((pullbackInvertibleSheaf π A).obj ≅ (power (originalLine q n a ha) m).obj) ∧
        IsMinimalResolution
          (sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)) S π ∧
        S.QCartier (rationalizeWeilDivisor S
          (targetCanonicalWeil q n a ha hn S π hπ hbir hpoints hcriterion)) ∧
        ∃ N : ℕ, 0 < N ∧ ∃ B : CartierDivisor S.toScheme,
          S.cartierToWeilHom B = N •
            (-(targetCanonicalWeil q n a ha hn S π hπ hbir hpoints hcriterion)) ∧
          AmpleSerre.IsAmple (cartierDivisorInvertibleSheaf S.toScheme B) := by
  letI : IsIntegral (multiSurface (q + 1) n a) :=
    multiSurface_isIntegral (q + 1) n a ha
  obtain ⟨m, hm, S, π, hπ, hproper, hsurj, hbir, hc, hgeom, hpoints,
      hcriterion, A, hA, ⟨e⟩, hlabels, hfinite, hcount, U, hU, hpre,
      hIso, hsupport, hbound, hqc, hminimal⟩ :=
    exists_normal_projective_surface_minimal_resolution_qCartier q n a ha hn
  letI : IsProper π := hproper
  letI : Surjective π := hsurj
  letI : IsIso π.c := hc
  have hd := (FrobeniusAnticanonicalParameterCases.coefficient_pos_iff q n hn).mpr hcases
  obtain ⟨N, hN, B, hB, hBample⟩ :=
    FrobeniusMultiCentreTargetAnticanonicalAmple.exists_ample_anticanonical_multiple
      q n a ha hn S π hπ hbir hpoints hcriterion A m hm e hA hd
  exact ⟨m, hm, S, π, hπ, hproper, hsurj, hbir, hc, hpoints, hcriterion,
    A, hA, ⟨e⟩, hminimal, hqc, N, hN, B, hB, hBample⟩

end KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction
