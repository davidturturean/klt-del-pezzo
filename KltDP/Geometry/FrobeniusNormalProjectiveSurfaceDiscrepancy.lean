import KltDP.Geometry.FrobeniusNormalProjectiveSurfacePicardRank
import KltDP.Examples.FrobeniusDiscrepancyWitness

/-!
The original rank-one normal projective Frobenius contraction supplies its
actual compatible canonical Cartier representative and discrepancy divisor.
Every prior existential output is retained. The canonical representative,
its exact pushforward, and all discrepancy coefficients are derived from
the original contraction; no choice of representative is assumed.
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

/-- The original full rank-one contraction has an actual compatible canonical
representative with the exact original discrepancy and strict coefficient bounds. -/
theorem exists_normal_projective_surface_rank_one_discrepancy
    {k : Type u} [Field k] [IsAlgClosed k]
    (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
    (a : Fin n → k) (ha : Function.Injective a) (hn : 2 < n) :
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
            (X := S) π) = 2 * n + 1 ∧
          S.NumericalSpaceFiniteDimensional ∧ S.picardRank = 1 ∧
          letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
          let source := sourceSurface q n a ha (originalMultiStructureProjective k (q + 1) n a)
          let K := targetCanonicalWeil q n a ha hn S π hπ hbir hpoints hcriterion
          ∃ (D : CartierDivisor source.toScheme)
            (hK : S.QCartier (rationalizeWeilDivisor S K)),
            Nonempty (cartierDivisorModule source.toScheme D ≅
              SmoothCanonicalExteriorComparison.relativeDifferentialExterior
                (multiStructure (q + 1) n a) 2) ∧
            BirationalWeilPushforward.pushforward (S := source) (X := S) π hbir
              (source.cartierToWeilHom D) = K ∧
            let Δ := source.rationalCartierToWeilHom D -
              QCartierPullback.pullback (X := source) (Y := S) π (rationalizeWeilDivisor S K) hK
            Δ = FrobeniusDiscrepancyBounds.candidate q n a ha
                (originalMultiStructureProjective k (q + 1) n a) ∧
            (∀ C : source.PrimeCurve, (-1 : ℚ) < Δ C) ∧
            (∀ (i : Fin n) (j : Fin q),
              Δ (exceptionalPrimeCurveSPn q n a ha i (.inl j)
                (originalMultiStructureProjective k (q + 1) n a)) = 0) := by
  letI : IsIntegral (multiSurface (q + 1) n a) :=
    multiSurface_isIntegral (q + 1) n a ha
  obtain ⟨m, hm, S, π, hπ, hproper, hsurj, hbir, hc, hgeom, hpoints,
      hcriterion, A, hA, ⟨e⟩, hlabels, hfinite, hcount, U, hU, hpre,
      hIso, hsupport, hbound, hqc, hminimal, hEx, hExfinite, hExcount,
      hdim, hrank⟩ := exists_normal_projective_surface_rank_one q n a ha hn
  letI : IsProper π := hproper
  letI : Surjective π := hsurj
  letI : IsIso π.c := hc
  letI : GenericPointPreserving π := ⟨hbir.map_genericPoint⟩
  obtain ⟨D, hK, heD, hpush, hformula, hcoeff, hold⟩ :=
    FrobeniusDiscrepancyWitness.exists_discrepancy_witness
      q n a ha hn S π hπ hbir hpoints hcriterion A m hm e
  exact ⟨m, hm, S, π, hπ, hproper, hsurj, hbir, hc, hgeom, hpoints,
    hcriterion, A, hA, ⟨e⟩, hlabels, hfinite, hcount, U, hU, hpre,
    hIso, hsupport, hbound, hqc, hminimal, hEx, hExfinite, hExcount,
    hdim, hrank, D, hK, heD, hpush, hformula, hcoeff, hold⟩

end KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction

#check @KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction.exists_normal_projective_surface_rank_one_discrepancy
#print axioms KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction.exists_normal_projective_surface_rank_one_discrepancy
