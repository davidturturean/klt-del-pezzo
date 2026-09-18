import KltDP.Geometry.RationalTreePicardPullbackEquivalence
import KltDP.Geometry.InvertibleSheafSectionPowersPullback
import KltDP.Geometry.LinearSystemMapPullback
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-!
# Actual embedding subsystems and nonzero power maps under a scheme isomorphism

The original pullback equivalence preserves nonzero morphisms. The original
power comparison then gives a nonzero map into the actual power of the
pulled line. The original pulled embedding sections define the original
composite embedding by the compiled linear-system naturality theorem.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace KltDP.Geometry.IsomorphismPullbackSubsystem

open InvertibleSheafSectionPowers InvertibleSheafSectionPowersPullback
  InvertibleSectionNonvanishingOpen LinearSystemNaturality

variable {X Y : Scheme.{u}}

/-- The actual nonempty source of a scheme isomorphism to an integral scheme is integral. -/
theorem source_isIntegral (j : Y ⟶ X) [IsIso j] [IsIntegral X] : IsIntegral Y := by
  letI : Nonempty Y := ⟨(inv j).base (Classical.choice (inferInstance : Nonempty X))⟩
  exact isIntegral_of_isOpenImmersion j

/-- Pull an original morphism back, then use the original power comparison. -/
def powerMap (j : Y ⟶ X) (H L : InvertibleSheaf X) (n : ℕ)
    (σ : H.obj ⟶ (power L n).obj) :
    (pullbackInvertibleSheaf j H).obj ⟶ (power (pullbackInvertibleSheaf j L) n).obj :=
  (schemeModulePullback j).map σ ≫ (powerPullbackIso j L n).hom

/-- Along the original scheme isomorphism, this actual power map remains nonzero. -/
theorem powerMap_ne_zero (j : Y ⟶ X) [IsIso j] (H L : InvertibleSheaf X) (n : ℕ)
    (σ : H.obj ⟶ (power L n).obj) (hσ : σ ≠ 0) : powerMap j H L n σ ≠ 0 := by
  letI : (schemeModulePullback j).IsLeftAdjoint :=
    (schemeModulePullbackPushforwardAdjunction j).isLeftAdjoint
  intro hz
  have hmap : (schemeModulePullback j).map σ = 0 := by
    have h := congrArg
      (fun τ : (pullbackInvertibleSheaf j H).obj ⟶
        (power (pullbackInvertibleSheaf j L) n).obj => τ ≫ (powerPullbackIso j L n).inv) hz
    simpa only [powerMap, Category.assoc, Iso.hom_inv_id, Category.comp_id, zero_comp] using h
  exact hσ ((schemeModulePullback j).map_eq_zero_iff.mp hmap)

/-- The actual pulled covering tuple still gives a closed immersion through the original map. -/
theorem closedImmersion_morphism_pullback {k : Type u} [Field k]
    (j : Y ⟶ X) [IsIso j] (H : InvertibleSheaf X) {n : ℕ}
    (s : Fin (n + 1) → H.obj.sections) (f : X ⟶ Spec (CommRingCat.of k))
    (hcover : (⨆ i, nonvanishingOpen X H (s i)) = ⊤)
    (hclosed : IsClosedImmersion (LinearSystemMorphism.morphism H s f hcover)) :
    IsClosedImmersion (LinearSystemMorphism.morphism (pullbackInvertibleSheaf j H)
      (pullbackSections j H s) (j ≫ f) (pullbackSections_cover j H s hcover)) := by
  rw [morphism_pullback]
  letI := hclosed
  infer_instance

end KltDP.Geometry.IsomorphismPullbackSubsystem
