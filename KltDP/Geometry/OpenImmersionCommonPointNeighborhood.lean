import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# A common actual neighborhood of two points over the same original point

The neighborhood is the original inverse image of the second open range.
The map to the second source is the original open-immersion lift; its
point equation follows from the original triangle and injectivity.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.OpenImmersionRational

/-- Original open immersions through the same point admit an actual common
open neighborhood through both given source points. -/
theorem exists_common_neighborhood_at_point
    {V W₁ W₂ : Scheme.{u}} (i₁ : W₁ ⟶ V) (i₂ : W₂ ⟶ V)
    [IsOpenImmersion i₁] [IsOpenImmersion i₂]
    (w₁ : W₁) (w₂ : W₂) (hpoint : i₁.base w₁ = i₂.base w₂) :
    ∃ (W : Scheme.{u}) (j₁ : W ⟶ W₁) (j₂ : W ⟶ W₂) (w : W),
      IsOpenImmersion j₁ ∧ IsOpenImmersion j₂ ∧
      j₁.base w = w₁ ∧ j₂.base w = w₂ ∧ j₁ ≫ i₁ = j₂ ≫ i₂ := by
  let U : W₁.Opens := i₁ ⁻¹ᵁ i₂.opensRange
  have hwU : w₁ ∈ U := by
    change i₁.base w₁ ∈ Set.range i₂.base
    exact ⟨w₂, hpoint.symm⟩
  have hrange : Set.range (U.ι ≫ i₁).base ⊆ Set.range i₂.base := by
    rintro _ ⟨y, rfl⟩
    exact y.property
  let j₂ : U.toScheme ⟶ W₂ := IsOpenImmersion.lift i₂ (U.ι ≫ i₁) hrange
  have htriangle : j₂ ≫ i₂ = U.ι ≫ i₁ :=
    IsOpenImmersion.lift_fac i₂ (U.ι ≫ i₁) hrange
  letI : IsOpenImmersion (j₂ ≫ i₂) := by
    rw [htriangle]
    infer_instance
  letI : IsOpenImmersion j₂ := IsOpenImmersion.of_comp j₂ i₂
  refine ⟨U.toScheme, U.ι, j₂, ⟨w₁, hwU⟩, inferInstance, inferInstance,
    rfl, ?_, htriangle.symm⟩
  apply i₂.isOpenEmbedding.injective
  have h := congrArg (fun g : U.toScheme ⟶ V => g.base ⟨w₁, hwU⟩) htriangle
  change i₂.base (j₂.base ⟨w₁, hwU⟩) = i₁.base w₁ at h
  exact h.trans hpoint

end KltDP.Geometry.OpenImmersionRational

#check @KltDP.Geometry.OpenImmersionRational.exists_common_neighborhood_at_point
#print axioms KltDP.Geometry.OpenImmersionRational.exists_common_neighborhood_at_point
