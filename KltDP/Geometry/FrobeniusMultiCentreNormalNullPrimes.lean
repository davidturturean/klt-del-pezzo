import KltDP.Geometry.FrobeniusMultiCentreNormalPrimeCriterion
import KltDP.Geometry.FrobeniusMultiCentreBirationalImageNullPrimes

/-!
The actual normal factor with geometrically connected fibers contracts
exactly the original graph, special strict fibers and old exceptional
primes. The existing original degree-zero classification is applied to
the same map as the new normal-factor criterion. This does not count
distinct image points or assert that the target is klt.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Limits
universe u

namespace KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction

open KltDP.Examples FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
open FrobeniusProjectivityProved InvertibleSheafSectionPowers
open FrobeniusMultiCentreContractingNef FrobeniusMultiCentreSpecialNullCurves
open FrobeniusMultiCentreExceptionalPrime

variable {k : Type u} [Field k] [IsAlgClosed k]
    (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
    (a : Fin n → k) (ha : Function.Injective a)

/-- The actual normal proper ample factor contracts precisely the original
labelled null primes, retaining both geometric and point-fiber connectedness. -/
theorem exists_normal_factor_with_label_criterion (hn : 2 < n) :
    letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
    ∃ m : ℕ, 0 < m ∧ ∃ (Y : Scheme.{u}) (σ : Y ⟶ Spec (CommRingCat.of k)),
      IsProper σ ∧ IsNormalScheme Y ∧ ∃ hY : IsIntegral Y,
        letI : IsIntegral Y := hY
        ∃ π : multiSurface (q + 1) n a ⟶ Y,
          π ≫ σ = multiStructure (q + 1) n a ∧ IsProper π ∧ Surjective π ∧
          IsBirationalScheme π ∧ IsIso π.c ∧
            (∀ (K : Type u) [Field K] (y : Spec (CommRingCat.of K) ⟶ Y),
              ConnectedSpace (pullback π y : Scheme.{u})) ∧
            (∀ y : Y, IsConnected (π.base ⁻¹' {y})) ∧
            ∃ A : InvertibleSheaf Y, AmpleSerre.IsAmple A ∧
              Nonempty ((pullbackInvertibleSheaf π A).obj ≅
                (power (originalLine q n a ha) m).obj) ∧
              ∀ C : (multiSurfaceSurface (q + 1) n a ha
                  (originalMultiStructureProjective k (q + 1) n a)).PrimeCurve,
                (∃ p : Spec (CommRingCat.of k) ⟶ Y,
                  C.inclusion ≫ π = C.toSpec ≫ p ∧ p ≫ σ = 𝟙 _) ↔
                C = graphPrimeCurve q n a ha
                    (originalMultiStructureProjective k (q + 1) n a) ∨
                (∃ i : Fin n, C = fiberPrimeCurve q n a ha
                  (originalMultiStructureProjective k (q + 1) n a) i) ∨
                ∃ (i : Fin n) (j : Fin q), C = exceptionalPrimeCurveSPn q n a ha i (.inl j)
                  (originalMultiStructureProjective k (q + 1) n a) := by
  letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
  obtain ⟨m, hm, Y, σ, hσ, hnormal, hY, π, hπ, hproper, hsurj, hbir, hc,
      hgeom, hpoints, A, hA, hpower, hC⟩ :=
    exists_normal_factor_with_prime_criterion q n a ha hn
  letI : IsIntegral Y := hY
  refine ⟨m, hm, Y, σ, hσ, hnormal, hY, π, hπ, hproper, hsurj, hbir, hc,
    hgeom, hpoints, A, hA, hpower, ?_⟩
  intro C
  exact (hC C).trans (originalLine_degree_zero_iff_labels q n a ha hn C)

end KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction
