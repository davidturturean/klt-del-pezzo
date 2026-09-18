import KltDP.Geometry.FrobeniusNormalProjectiveSurfaceContraction
import KltDP.Geometry.FrobeniusNormalFactorIsomorphism

/-!
The compiled original normal projective surface contraction is retained
with its exponent, ample line, prime labels and exact null-image count.
The same map is now identified as an isomorphism on the actual complement
of that image, whose inverse image is the original null-locus complement.
No new factorization, singularity claim or additional premise is introduced.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

universe u

namespace KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction

open KltDP.Examples FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
open FrobeniusProjectivityProved InvertibleSheafSectionPowers
open FrobeniusMultiCentreContractingNef FrobeniusMultiCentreSpecialNullCurves
open FrobeniusMultiCentreExceptionalPrime

variable {k : Type u} [Field k] [IsAlgClosed k]
  (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
  (a : Fin n → k) (ha : Function.Injective a)

/-- The actual normal projective contraction, with its full previous
properties and an isomorphism on the exact null-locus complement. -/
theorem exists_normal_projective_surface_contraction_iso (hn : 2 < n) :
    letI : IsIntegral (multiSurface (q + 1) n a) :=
      multiSurface_isIntegral (q + 1) n a ha
    ∃ m : ℕ, 0 < m ∧ ∃ (S : NormalProjectiveSurface k)
      (π : multiSurface (q + 1) n a ⟶ S.toScheme),
      π ≫ S.structureMorphism = multiStructure (q + 1) n a ∧
      IsProper π ∧ Surjective π ∧ IsBirationalScheme π ∧ IsIso π.c ∧
      (∀ (K : Type u) [Field K] (y : Spec (CommRingCat.of K) ⟶ S.toScheme),
        ConnectedSpace (pullback π y : Scheme.{u})) ∧
      (∀ y : S.toScheme, IsConnected (π.base ⁻¹' {y})) ∧
      ∃ A : InvertibleSheaf S.toScheme, AmpleSerre.IsAmple A ∧
        Nonempty ((pullbackInvertibleSheaf π A).obj ≅ (power (originalLine q n a ha) m).obj) ∧
        (∀ C : (multiSurfaceSurface (q + 1) n a ha
            (originalMultiStructureProjective k (q + 1) n a)).PrimeCurve,
          (∃ p : Spec (CommRingCat.of k) ⟶ S.toScheme,
            C.inclusion ≫ π = C.toSpec ≫ p ∧ p ≫ S.structureMorphism = 𝟙 _) ↔
          C = graphPrimeCurve q n a ha (originalMultiStructureProjective k (q + 1) n a) ∨
          (∃ i : Fin n, C = fiberPrimeCurve q n a ha
            (originalMultiStructureProjective k (q + 1) n a) i) ∨
          ∃ (i : Fin n) (j : Fin q), C = exceptionalPrimeCurveSPn q n a ha i (.inl j)
            (originalMultiStructureProjective k (q + 1) n a)) ∧
        (π.base '' Positivity.nullLocus (multiStructure (q + 1) n a)
          (originalLine q n a ha)).Finite ∧
        Nat.card (π.base '' Positivity.nullLocus (multiStructure (q + 1) n a)
          (originalLine q n a ha)) = 2 * n + 1 ∧
        ∃ U : S.toScheme.Opens,
          (U : Set S.toScheme) = (π.base '' Positivity.nullLocus
            (multiStructure (q + 1) n a) (originalLine q n a ha))ᶜ ∧
          π ⁻¹ᵁ U = (Positivity.nullLocusClosed
            (multiStructure (q + 1) n a) (originalLine q n a ha)).compl ∧
          IsIso (π ∣_ U) := by
  letI : IsIntegral (multiSurface (q + 1) n a) :=
    multiSurface_isIntegral (q + 1) n a ha
  obtain ⟨m, hm, S, π, hπ, hproper, hsurj, hbir, hc, hgeom, hpoints,
      A, hA, hpower, hlabels, hfinite, hcount⟩ :=
    exists_normal_projective_surface_contraction q n a ha hn
  letI : IsProper π := hproper
  letI : Surjective π := hsurj
  letI : IsIso π.c := hc
  have hcriterion := fun C => (hlabels C).trans
    (originalLine_degree_zero_iff_labels q n a ha hn C).symm
  refine ⟨m, hm, S, π, hπ, hproper, hsurj, hbir, hc, hgeom, hpoints,
    A, hA, hpower, hlabels, hfinite, hcount,
    nullImageComplement q n a ha π, rfl, ?_, ?_⟩
  · exact preimage_nullImageComplement q n a ha hn S π hπ hbir hpoints hcriterion
  · exact isIso_restrict_nullImageComplement q n a ha hn S π hπ hbir hpoints hcriterion

end KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction
