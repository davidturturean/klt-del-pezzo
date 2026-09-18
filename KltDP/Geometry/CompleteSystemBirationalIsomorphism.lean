import KltDP.Geometry.IsomorphismPullbackSubsystem
import KltDP.Geometry.CompleteLinearSystemBirational
import KltDP.Geometry.SubsystemPositiveDimension
import KltDP.Geometry.KeelCompleteSystemBirational

/-!
# Actual eventual complete-system birationality on an isomorphic source

An original embedded covering subsystem and actual eventual nonzero power
maps are pulled through the original scheme isomorphism. The resulting
maps give positive original H0 dimension and the proved birationality of
the actual complete-system factors. Source integrality and properness are
derived from the isomorphism, without transporting complete-system bases.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.CompleteSystemBirationalIsomorphism

open InvertibleSheafSectionPowers InvertibleSectionNonvanishingOpen
  LinearSystemNaturality IsomorphismPullbackSubsystem

attribute [local instance] CompleteLinearSystemMap.subsystem_nonBaseOpen_integral
  CompleteLinearSystemMap.subsystem_image_integral

/-- Pulling the original embedded subsystem and actual eventual maps along
an actual isomorphism proves the original eventual complete-system predicate. -/
theorem eventuallyBirational_of_nonzero_power_maps
    {k : Type u} [Field k] {X Y : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (H L : InvertibleSheaf X) {m : ℕ} (s : Fin (m + 1) → H.obj.sections)
    (hcover : (⨆ i, nonvanishingOpen X H (s i)) = ⊤)
    (hclosed : IsClosedImmersion (LinearSystemMorphism.morphism H s f hcover))
    (hmaps : ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      ∃ σ : H.obj ⟶ (power L n).obj, σ ≠ 0)
    (j : Y ⟶ X) [IsIso j] :
    letI : IsIntegral Y := source_isIntegral j
    letI : IsProper (j ≫ f) := inferInstance
    KeelCompleteSystem.EventuallyBirational (j ≫ f) (pullbackInvertibleSheaf j L) := by
  letI : IsIntegral Y := source_isIntegral j
  letI : IsProper (j ≫ f) := inferInstance
  let H' := pullbackInvertibleSheaf j H
  let s' := pullbackSections j H s
  let hc' := pullbackSections_cover j H s hcover
  have hclosed' := closedImmersion_morphism_pullback j H s f hcover hclosed
  obtain ⟨N, hN, hmaps⟩ := hmaps
  refine ⟨N, hN, ?_⟩
  intro n hn
  obtain ⟨σ, hσ⟩ := hmaps n hn
  let τ := powerMap j H L n σ
  have hτ : τ ≠ 0 := powerMap_ne_zero j H L n σ hσ
  have hpos := SubsystemPositiveDimension.dimension_pos_of_nonzero_map
    (j ≫ f) H' (power (pullbackInvertibleSheaf j L) n) s' hc' τ hτ
  exact ⟨hpos, CompleteLinearSystemMap.toImage_isBirationalScheme_of_subsystem
    (j ≫ f) H' (power (pullbackInvertibleSheaf j L) n) s' hc' τ hτ hclosed' hpos⟩

end KltDP.Geometry.CompleteSystemBirationalIsomorphism
