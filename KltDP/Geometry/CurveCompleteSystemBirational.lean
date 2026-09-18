import KltDP.Geometry.CurveEventualNonzeroMaps
import KltDP.Geometry.CompleteLinearSystemBirational
import KltDP.Geometry.SubsystemPositiveDimension
import KltDP.Geometry.ProjectiveEmbeddingLinearSystem
import KltDP.Geometry.ProjectiveProper

/-!
# Every sufficiently large complete system of a positive-degree curve line is birational

Original projectivity supplies an actual closed-immersion linear system.
The positive Euler degree supplies, for every sufficiently large power,
a nonzero original map from that fixed embedding line to the original power.
The subsystem theorem then proves birationality of the original
complete-system factor into its actual schematic image. Positivity of the
actual complete H0 dimension is derived. The field is arbitrary.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open KltDP.Geometry.ModuleCohomology

universe u

namespace KltDP.Geometry.CurveCompleteSystemBirational

open InvertibleSheafSectionPowers CompleteLinearSystemSections

attribute [local instance]
  CompleteLinearSystemMap.subsystem_nonBaseOpen_integral
  CompleteLinearSystemMap.subsystem_image_integral

/-- On the original integral projective curve, positive Euler degree makes every sufficiently
large original complete system birational onto its original schematic image. -/
theorem eventually_toImage_isBirationalScheme_of_degree_pos
    {k : Type u} [Field k] {Y : Scheme.{u}} [IsIntegral Y]
    (f : Y ⟶ Spec (CommRingCat.of k)) (hf : IsProjectiveOverField f)
    (hdim : topologicalKrullDim Y = 1) (L : InvertibleSheaf Y)
    (hdeg : 0 < eulerCharacteristic f L.obj -
      eulerCharacteristic f (_root_.SheafOfModules.unit Y.ringCatSheaf)) :
    letI : IsProper f := hf.isProper
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (0 < dimension f (power L n)) ∧
        ∀ hpos : 0 < dimension f (power L n),
          IsBirationalScheme (SchematicImageGlued.toImage
            (CompleteLinearSystemMap.morphism f (power L n) hpos)) := by
  letI : IsProper f := hf.isProper
  obtain ⟨H, m, s, hcover, hclosed⟩ := hf.exists_closedImmersion_linearSystem
  obtain ⟨N, hN⟩ := CurveEventualNonzeroMaps.eventually_exists_nonzero_map
    f (le_of_eq hdim) H L hdeg
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨σ, hσ⟩ := hN n hn
  refine ⟨SubsystemPositiveDimension.dimension_pos_of_nonzero_map
    f H (power L n) s hcover σ hσ, fun hpos => ?_⟩
  exact CompleteLinearSystemMap.toImage_isBirationalScheme_of_subsystem
    f H (power L n) s hcover σ hσ hclosed hpos

end KltDP.Geometry.CurveCompleteSystemBirational
