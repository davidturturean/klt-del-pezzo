import KltDP.Geometry.FrobeniusMultiCentreEmbeddingSubsystem
import KltDP.Geometry.CompleteLinearSystemBirational
import KltDP.Geometry.ProjectiveEmbeddingLinearSystem
import KltDP.Geometry.SubsystemPositiveDimension

/-!
# Eventual complete-system birationality for the original Frobenius contracting line

The already proved maps from every fixed original line into all sufficiently
large powers of M are applied to an actual projective embedding tuple.
Every resulting original complete-system factor is birational onto its
actual schematic image. The existing RR branch remains private and unaccepted.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.FrobeniusMultiCentreCompleteBirational

open InvertibleSheafSectionPowers
open KltDP.Examples.FrobeniusMultiCentreSurface
open KltDP.Examples.FrobeniusMultiCentreIntegral
open KltDP.Examples.FrobeniusMultiCentreContractingNef
open FrobeniusMultiCentreEmbeddingSubsystem

attribute [local instance] CompleteLinearSystemMap.subsystem_nonBaseOpen_integral
  CompleteLinearSystemMap.subsystem_image_integral

variable {k : Type u} [Field k] [IsAlgClosed k]
  (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
  (a : Fin n → k) (ha : Function.Injective a)
  (hproj : IsProjectiveOverField (multiStructure (q + 1) n a))

/-- For more than two centres, all sufficiently large original complete systems of M
are birational onto their actual schematic images. -/
theorem contractingLine_eventually_toImage_isBirationalScheme (hn : 2 < n) :
    letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
    letI : IsProper (multiStructure (q + 1) n a) := hproj.isProper
    ∃ N : ℕ, 0 < N ∧ ∀ m : ℕ, N ≤ m →
      ∃ hpos : 0 < CompleteLinearSystemSections.dimension (multiStructure (q + 1) n a)
          (power (contractingLine q n a ha hproj) m),
        IsBirationalScheme (SchematicImageGlued.toImage
          (CompleteLinearSystemMap.morphism (multiStructure (q + 1) n a)
            (power (contractingLine q n a ha hproj) m) hpos)) := by
  letI : IsIntegral (multiSurface (q + 1) n a) := multiSurface_isIntegral (q + 1) n a ha
  letI : IsProper (multiStructure (q + 1) n a) := hproj.isProper
  obtain ⟨H, t, s, hcover, hclosed⟩ := hproj.exists_closedImmersion_linearSystem
  obtain ⟨N, hN, hmaps⟩ := contractingLine_eventually_nonzero_map q n a ha hproj hn H
  refine ⟨N, hN, ?_⟩
  intro m hm
  obtain ⟨σ, hσ⟩ := hmaps m hm
  have hpos := SubsystemPositiveDimension.dimension_pos_of_nonzero_map
    (multiStructure (q + 1) n a) H (power (contractingLine q n a ha hproj) m) s hcover σ hσ
  exact ⟨hpos, CompleteLinearSystemMap.toImage_isBirationalScheme_of_subsystem
    (multiStructure (q + 1) n a) H (power (contractingLine q n a ha hproj) m)
    s hcover σ hσ hclosed hpos⟩

end KltDP.Geometry.FrobeniusMultiCentreCompleteBirational
