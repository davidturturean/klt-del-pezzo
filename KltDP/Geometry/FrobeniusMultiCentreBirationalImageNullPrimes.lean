import KltDP.Geometry.FrobeniusMultiCentreBirationalImagePrimeCriterion
import KltDP.Examples.FrobeniusMultiCentreNullCurveClassification

/-!
# Exact original prime labels for the Frobenius birational image

The existing image and its original ample pullback line are retained.
The proved degree-zero criterion is composed with the original graph,
special-fiber and old-exceptional prime classification. Projectivity is
supplied by the original producer. No image-point count or Stein property
is inferred.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction

open KltDP.Examples FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
open FrobeniusProjectivityProved InvertibleSheafSectionPowers
open FrobeniusMultiCentreContractingNef FrobeniusMultiCentreSpecialNullCurves
open FrobeniusMultiCentreExceptionalPrime FrobeniusMultiCentreNullCurveClassification

variable {k : Type u} [Field k] [IsAlgClosed k]
  (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
  (a : Fin n → k) (ha : Function.Injective a)

/-- The original line with its derived projectivity has the same exact null-prime labels. -/
theorem originalLine_degree_zero_iff_labels (hn : 2 < n)
    (C : (multiSurfaceSurface (q + 1) n a ha
      (originalMultiStructureProjective k (q + 1) n a)).PrimeCurve) :
    C.restrictionDegree (originalLine q n a ha) = 0 ↔
      C = graphPrimeCurve q n a ha (originalMultiStructureProjective k (q + 1) n a) ∨
      (∃ i : Fin n, C = fiberPrimeCurve q n a ha
        (originalMultiStructureProjective k (q + 1) n a) i) ∨
      ∃ (i : Fin n) (j : Fin q), C = exceptionalPrimeCurveSPn q n a ha i (.inl j)
        (originalMultiStructureProjective k (q + 1) n a) :=
  restrictionDegree_eq_zero_iff q n a ha
    (originalMultiStructureProjective k (q + 1) n a) hn C

/-- The original proper surjective birational image contracts precisely the
original graph, selected strict fibers, and old exceptional prime components. -/
theorem exists_birational_image_with_label_criterion (hn : 2 < n) :
    letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
    ∃ m : ℕ, 0 < m ∧ ∃ (Y : Scheme.{u}) (σ : Y ⟶ Spec (CommRingCat.of k)),
      IsProjectiveOverField σ ∧ ∃ hY : IsIntegral Y,
        letI : IsIntegral Y := hY
        ∃ π : multiSurface (q + 1) n a ⟶ Y,
          π ≫ σ = multiStructure (q + 1) n a ∧ IsProper π ∧ Surjective π ∧
          IsBirationalScheme π ∧ ∃ A : InvertibleSheaf Y, AmpleSerre.IsAmple A ∧
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
  obtain ⟨m, hm, Y, σ, hσ, hY, π, hπ, hproper, hsurj, hbir, A, hA, hpower, hC⟩ :=
    exists_birational_image_with_prime_criterion q n a ha hn
  letI : IsIntegral Y := hY
  refine ⟨m, hm, Y, σ, hσ, hY, π, hπ, hproper, hsurj, hbir, A, hA, hpower, ?_⟩
  intro C
  exact (hC C).trans (originalLine_degree_zero_iff_labels q n a ha hn C)

end KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction
