import KltDP.Geometry.FrobeniusBlockImageCount
import KltDP.Examples.FrobeniusNormalFactorBlockPoints
import KltDP.Geometry.FrobeniusNormalFactorNullLocusSaturation
import KltDP.Geometry.NormalFactorPrimeCurveCriterion
import KltDP.Geometry.ProperSteinConnected

/-!
Count distinct actual image points for the canonical normal factor of a
chosen generated birational power of the original Frobenius line. The
point factorizations, connected fibers and fiber exhaustion are derived
for this same original map before the finite block-count theorem is used.
This counts image points, without asserting that they are singular.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
universe u

namespace KltDP.Geometry.FrobeniusNormalFactorImageCount

open KltDP.Examples FrobeniusMultiCentreSurface FrobeniusMultiCentreIntegral
  FrobeniusProjectivityProved FrobeniusMultiCentreSemiampleConstruction
  FrobeniusNormalFactorBlockPoints FrobeniusContractingBlockSupports
  InvertibleSheafSectionPowers CompleteLinearSystemSections CompleteLinearSystemMap
  GeneratedCompleteSystemNormalFactor

variable {k : Type u} [Field k] [IsAlgClosed k]
  (q n : ℕ) [Fact (q + 1).Prime] [CharP k (q + 1)]
  (a : Fin n → k) (ha : Function.Injective a)

attribute [local instance] KeelCompleteSystem.completeSystemDomain_isIntegral
  KeelCompleteSystem.completeSystemImage_isIntegral

local instance source_isProper : IsProper (multiStructure (q + 1) n a) :=
  (originalMultiStructureProjective k (q + 1) n a).isProper

/-- The actual canonical normal map has exactly 2n+1 distinct null-locus
image points. Every geometric input to the finite count is proved here. -/
theorem generated_image_nullLocus_finite_card (hn : 2 < n) (m : ℕ) (hm : 0 < m)
    (hpos : 0 < dimension (multiStructure (q + 1) n a) (power (originalLine q n a ha) m))
    (hG : Positivity.IsGloballyGenerated (power (originalLine q n a ha) m).obj) :
    letI : IsIntegral (multiSurface (q + 1) n a) :=
      multiSurface_isIntegral (q + 1) n a ha
    ∀ hbir : IsBirationalScheme (SchematicImageGlued.toImage
      (morphism (multiStructure (q + 1) n a) (power (originalLine q n a ha) m) hpos)),
    let π := fromSource (multiStructure (q + 1) n a)
      (power (originalLine q n a ha) m) hpos hG
    (π.base '' Positivity.nullLocus (multiStructure (q + 1) n a)
      (originalLine q n a ha)).Finite ∧
    Nat.card (π.base '' Positivity.nullLocus (multiStructure (q + 1) n a)
      (originalLine q n a ha)) = 2 * n + 1 := by
  letI : IsIntegral (multiSurface (q + 1) n a) :=
    multiSurface_isIntegral (q + 1) n a ha
  intro hbir
  classical
  let π := fromSource (multiStructure (q + 1) n a)
    (power (originalLine q n a ha) m) hpos hG
  let σ := structureMorphism (multiStructure (q + 1) n a)
    (power (originalLine q n a ha) m) hpos hG
  let Y := target (multiStructure (q + 1) n a) (power (originalLine q n a ha) m) hpos hG
  letI : IsIntegral Y := target_isIntegral
    (multiStructure (q + 1) n a) (power (originalLine q n a ha) m) hpos hG
  letI : IsProper σ := structureMorphism_isProper
    (multiStructure (q + 1) n a) (power (originalLine q n a ha) m) hpos hG
  letI : IsLocallyNoetherian Y := isLocallyNoetherian_of_locallyOfFiniteType_spec σ
  letI : IsProper π := fromSource_isProper
    (multiStructure (q + 1) n a) (power (originalLine q n a ha) m) hpos hG
  letI : IsIso π.c := fromSource_c_isIso
    (multiStructure (q + 1) n a) (power (originalLine q n a ha) m) hpos hG
  have hconnected : ∀ y : Y, IsConnected (π.base ⁻¹' {y}) :=
    ProperSteinConnected.pointFibers_connected π
  have hcriterion := fun C => PrimeCurveImageContraction.generatedNormal_factors_iff
    (multiSurfaceSurface (q + 1) n a ha (originalMultiStructureProjective k (q + 1) n a))
    C (originalLine q n a ha) m hm hpos hG
  have hsaturated := nullLocus_preimage_image_of_prime_criterion q n a ha hn σ π
    (fromSource_isProper (multiStructure (q + 1) n a)
      (power (originalLine q n a ha) m) hpos hG)
    (fromSource_surjective (multiStructure (q + 1) n a)
      (power (originalLine q n a ha) m) hpos hG)
    (fromSource_structure (multiStructure (q + 1) n a)
      (power (originalLine q n a ha) m) hpos hG)
    (fromSource_isBirationalScheme (multiStructure (q + 1) n a)
      (power (originalLine q n a ha) m) hpos hG hbir)
    hconnected hcriterion
  choose point hpoint hfield using
    (fun r : BlockIndex n => exists_block_point q n a ha m hpos hG r)
  exact FrobeniusBlockImageCount.image_nullLocus_finite_card
    q n a ha hn π point hpoint hsaturated hconnected

end KltDP.Geometry.FrobeniusNormalFactorImageCount
