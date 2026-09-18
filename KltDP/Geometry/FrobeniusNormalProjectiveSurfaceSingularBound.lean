import KltDP.Geometry.FrobeniusNormalProjectiveSurfaceContractionIso
import KltDP.Geometry.FrobeniusNormalFactorSingularSupport
import KltDP.Geometry.SurfaceSingularCountOnIsomorphismOpen

/-!
Retain the same original normal projective contraction and its exact
isomorphism complement. Its actual singular points lie in the computed
finite null-locus image, hence there are at most `2*n+1` of them.
No assertion that every contracted image is singular is made.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

universe u

namespace KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction

open KltDP.Examples FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
open FrobeniusProjectivityProved InvertibleSheafSectionPowers
open FrobeniusMultiCentreContractingNef FrobeniusMultiCentreSpecialNullCurves
open FrobeniusMultiCentreExceptionalPrime FrobeniusMultiCentreGraphExceptionalPairing

variable {k : Type u} [Field k] [IsAlgClosed k]
  (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
  (a : Fin n → k) (ha : Function.Injective a)

/-- The same actual target has at most `2*n+1` actual singular points,
all in the previously counted null-locus image. -/
theorem exists_normal_projective_surface_contraction_singular_bound (hn : 2 < n) :
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
          IsIso (π ∣_ U) ∧
          (S.singularPoints : Set S.Point) ⊆
            π.base '' Positivity.nullLocus (multiStructure (q + 1) n a) (originalLine q n a ha) ∧
          S.singularPoints.card ≤ 2 * n + 1 := by
  letI : IsIntegral (multiSurface (q + 1) n a) :=
    multiSurface_isIntegral (q + 1) n a ha
  obtain ⟨m, hm, S, π, hπ, hproper, hsurj, hbir, hc, hgeom, hpoints,
      A, hA, hpower, hlabels, hfinite, hcount, U, hU, hpre, hIso⟩ :=
    exists_normal_projective_surface_contraction_iso q n a ha hn
  letI : IsIso (π ∣_ U) := hIso
  have hfiniteCompl : ((U : Set S.Point)ᶜ).Finite := by
    simpa only [hU, compl_compl] using hfinite
  have hbound := RegularPointsOnIsomorphismOpen.singularPoints_card_le_natCard_compl
    S π U (multiSurfaceSurface_regularPoints (q + 1) n a ha
      (originalMultiStructureProjective k (q + 1) n a)) hfiniteCompl
  refine ⟨m, hm, S, π, hπ, hproper, hsurj, hbir, hc, hgeom, hpoints,
    A, hA, hpower, hlabels, hfinite, hcount, U, hU, hpre, hIso, ?_, ?_⟩
  · exact singularPoints_subset_nullImage q n a ha S π U hU
  · simpa only [hU, compl_compl, hcount] using hbound

end KltDP.Geometry.FrobeniusMultiCentreSemiampleConstruction
