import KltDP.Geometry.NefTwistedMaps
import KltDP.Geometry.CompleteLinearSystemBirational
import KltDP.Geometry.ProjectiveEmbeddingLinearSystem
import KltDP.Geometry.SubsystemPositiveDimension

/-!
# Eventual birationality of the original complete systems of a nef positive-square line

Original projectivity supplies an actual embedding tuple. The proved
eventual twisted-section theorem gives nonzero maps from that line bundle
to every sufficiently large actual power. Those maps give positive H0
dimension and make each original complete-system map birational onto its
actual schematic image. The RR dependencies remain private and unaccepted.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.NormalProjectiveSurface
open KltDP.Geometry.SurfaceRiemannRochSource
open KltDP.Geometry.InvertibleSheafSectionPowers
universe u

namespace KltDP.Geometry.NefCompleteSystemBirational

attribute [local instance] CompleteLinearSystemMap.subsystem_nonBaseOpen_integral
  CompleteLinearSystemMap.subsystem_image_integral

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)
  (hregular : ∀ x : X.Point, RegularPoint X.toScheme x)

local instance original_proper : IsProper X.structureMorphism := X.projective.isProper

/-- Every sufficiently large original complete system is birational onto its actual image. -/
theorem eventually_toImage_isBirationalScheme_of_isCanonical
    (K : X.WeilDivisor) (hK : IsCanonical X hregular K)
    (A : InvertibleSheaf X.toScheme) (hA : Positivity.IsNef X.structureMorphism A)
    (hpositive : 0 < X.selfIntersection hregular A) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      ∃ hpos : 0 < CompleteLinearSystemSections.dimension X.structureMorphism (power A n),
        IsBirationalScheme (SchematicImageGlued.toImage
          (CompleteLinearSystemMap.morphism X.structureMorphism (power A n) hpos)) := by
  letI : IsProper X.structureMorphism := X.projective.isProper
  obtain ⟨H, m, s, hcover, hclosed⟩ := X.projective.exists_closedImmersion_linearSystem
  obtain ⟨N, hN, hmaps⟩ := NefTwistedMaps.eventually_nonzero_map_of_isCanonical
    X hregular K hK A H hA hpositive
  refine ⟨N, hN, ?_⟩
  intro n hn
  obtain ⟨σ, hσ⟩ := hmaps n hn
  have hpos := SubsystemPositiveDimension.dimension_pos_of_nonzero_map
    X.structureMorphism H (power A n) s hcover σ hσ
  exact ⟨hpos, CompleteLinearSystemMap.toImage_isBirationalScheme_of_subsystem
    X.structureMorphism H (power A n) s hcover σ hσ hclosed hpos⟩

section Smooth

variable [IsSmoothOfRelativeDimension 2 X.structureMorphism]

local instance source_isSmooth : IsSmooth X.structureMorphism :=
  IsSmoothOfRelativeDimension.isSmooth 2 X.structureMorphism

/-- Smoothness supplies the original regularity and canonical divisor in the eventual result. -/
theorem eventually_toImage_isBirationalScheme
    (A : InvertibleSheaf X.toScheme) (hA : Positivity.IsNef X.structureMorphism A)
    (hpositive : 0 < X.selfIntersection X.regularPoints_of_isSmooth A) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      ∃ hpos : 0 < CompleteLinearSystemSections.dimension X.structureMorphism (power A n),
        IsBirationalScheme (SchematicImageGlued.toImage
          (CompleteLinearSystemMap.morphism X.structureMorphism (power A n) hpos)) :=
  eventually_toImage_isBirationalScheme_of_isCanonical X X.regularPoints_of_isSmooth
    (SmoothCanonicalCartierRepresentative.weilRepresentative X)
    (SurfaceRiemannRochSource.constructedCanonical_isCanonical X) A hA hpositive

end Smooth

end KltDP.Geometry.NefCompleteSystemBirational
