import KltDP.Geometry.FrobeniusNormalProjectiveSurfaceMinimalQCartier
import KltDP.Geometry.FrobeniusNormalFactorExceptionalLocus

/-!
# The original minimal resolution and its exact exceptional locus

Retain the single original normal projective contraction, including its actual
canonical Q-Cartier property and minimality. Its accepted exceptional locus
is the original null locus, with precisely the already computed image points.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

universe u

namespace KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction

open KltDP.Examples FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
open FrobeniusProjectivityProved InvertibleSheafSectionPowers NormalProjectiveSurface
open FrobeniusMultiCentreContractingNef FrobeniusMultiCentreSpecialNullCurves
open FrobeniusMultiCentreExceptionalPrime FrobeniusMultiCentreGraphExceptionalPairing
open FrobeniusMultiCentreCanonicalWeilRepresentatives

variable {k : Type u} [Field k] [IsAlgClosed k]
    (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
    (a : Fin n → k) (ha : Function.Injective a)

/-- The same original minimal resolution has exactly the original null locus
as its accepted exceptional locus, whose image has cardinality `2*n+1`. -/
theorem exists_normal_projective_surface_exact_exceptional_locus (hn : 2 < n) :
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
      (∀ (K : Type u) [Field K] (y : Spec (CommRingCat.of K) ⟶ S.toScheme),
        ConnectedSpace (pullback π y : Scheme.{u})) ∧
      ∃ (hpoints : ∀ y : S.toScheme, IsConnected (π.base ⁻¹' {y}))
        (hcriterion : ∀ C : (multiSurfaceSurface (q + 1) n a ha
            (originalMultiStructureProjective k (q + 1) n a)).PrimeCurve,
          (∃ p : Spec (CommRingCat.of k) ⟶ S.toScheme,
            C.inclusion ≫ π = C.toSpec ≫ p ∧ p ≫ S.structureMorphism = 𝟙 _) ↔
          C.restrictionDegree (originalLine q n a ha) = 0),
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
          IsIso (π ∣_ U) ∧
          (S.singularPoints : Set S.Point) ⊆
            π.base '' Positivity.nullLocus (multiStructure (q + 1) n a) (originalLine q n a ha) ∧
          S.singularPoints.card ≤ 2 * n + 1 ∧
          S.QCartier (rationalizeWeilDivisor S
            (targetCanonicalWeil q n a ha hn S π hπ hbir hpoints hcriterion)) ∧
          IsMinimalResolution
            (sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)) S π ∧
          KltDP.Geometry.exceptionalLocus
              (S := sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a))
              (X := S) π =
            Positivity.nullLocus (multiStructure (q + 1) n a) (originalLine q n a ha) ∧
          (π.base '' KltDP.Geometry.exceptionalLocus
            (S := sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a))
            (X := S) π).Finite ∧
          Nat.card (π.base '' KltDP.Geometry.exceptionalLocus
            (S := sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a))
            (X := S) π) = 2 * n + 1 := by
  letI : IsIntegral (multiSurface (q + 1) n a) :=
    multiSurface_isIntegral (q + 1) n a ha
  obtain ⟨m, hm, S, π, hπ, hproper, hsurj, hbir, hc, hgeom, hpoints,
      hcriterion, A, hA, hpower, hlabels, hfinite, hcount, U, hU, hpre,
      hIso, hsupport, hbound, hqc, hminimal⟩ :=
    exists_normal_projective_surface_minimal_resolution_qCartier q n a ha hn
  letI : IsProper π := hproper
  letI : Surjective π := hsurj
  letI : IsIso π.c := hc
  have hEx := exceptionalLocus_eq_originalNullLocus
    q n a ha hn S π hπ hbir hpoints hcriterion
  refine ⟨m, hm, S, π, hπ, hproper, hsurj, hbir, hc, hgeom, hpoints,
    hcriterion, A, hA, hpower, hlabels, hfinite, hcount, U, hU, hpre, hIso,
    hsupport, hbound, hqc, hminimal, hEx, ?_, ?_⟩
  · rw [hEx]
    exact hfinite
  · rw [hEx]
    exact hcount

end KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction
