import KltDP.Geometry.LinearSystemMapPullback
import KltDP.Geometry.ProjectiveCoordinateLinearSystem

/-!
# An original projective embedding is an original linear-system morphism

Pull the actual homogeneous sections of the actual degree-one invertible
sheaf through the original projective embedding. Their intrinsic
nonvanishing opens cover by the original pullback formula. Naturality and
the homogeneous-coordinate identity recover the original embedding itself.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry

open InvertibleSectionNonvanishingOpen LinearSystemNaturality
  ProjectiveSpaceDegreeOneSheaf ProjectiveCoordinateLinearSystem

namespace ProjectiveEmbeddingLinearSystem

/-- The original sections pulled through an original projective-space map
give that same map, with its original structure morphism. -/
theorem morphism_pullback_homogeneousSection
    (k : Type u) [Field k] (n : ℕ) {X : Scheme.{u}}
    (e : X ⟶ projectiveSpace k n) (f : X ⟶ Spec (CommRingCat.of k))
    (hfe : e ≫ projectiveSpaceToSpec k n = f) :
    LinearSystemMorphism.morphism (pullbackInvertibleSheaf e (degreeOne k n))
      (pullbackSections e (degreeOne k n) (homogeneousSection k n)) f
      (pullbackSections_cover e (degreeOne k n) (homogeneousSection k n)
        (homogeneousSection_cover k n)) = e := by
  rw [← hfe, morphism_pullback, morphism_homogeneousSection, Category.comp_id]

end ProjectiveEmbeddingLinearSystem

/-- Original projectivity supplies an actual invertible sheaf and finitely
many actual covering sections whose original linear-system map is a closed
immersion. The witnesses come from the original projective embedding. -/
theorem IsProjectiveOverField.exists_closedImmersion_linearSystem
    {k : Type u} [Field k] {X : Scheme.{u}}
    {f : X ⟶ Spec (CommRingCat.of k)} (hf : IsProjectiveOverField f) :
    ∃ (H : InvertibleSheaf X) (n : ℕ) (s : Fin (n + 1) → H.obj.sections)
      (hcover : (⨆ j, nonvanishingOpen X H (s j)) = ⊤),
      IsClosedImmersion (LinearSystemMorphism.morphism H s f hcover) := by
  obtain ⟨n, e, he, hfe⟩ := hf
  refine ⟨pullbackInvertibleSheaf e (degreeOne k n), n,
    pullbackSections e (degreeOne k n) (homogeneousSection k n),
    pullbackSections_cover e (degreeOne k n) (homogeneousSection k n)
      (homogeneousSection_cover k n), ?_⟩
  rw [ProjectiveEmbeddingLinearSystem.morphism_pullback_homogeneousSection k n e f hfe]
  exact he

end KltDP.Geometry
