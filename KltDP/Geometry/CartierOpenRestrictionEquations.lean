import KltDP.Geometry.CartierOpenRestriction
import KltDP.Geometry.CartierDivisorTrivialization

/-!
# Local equations for actual Cartier restriction

Naturality of the constructed Cartier sheaf map transports an actual
global divisor equation to every nonempty inverse-image open. For an
image open, the pinned open-immersion identity identifies this inverse
image with the original source open.

The existing `CartierEquationChart` atlas pulls back to a covering
family on the source scheme. These are adapters of the actual quotient
map, its proved equation formula, and the existing covering theorem;
no global rational representative or additional geometric input is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.OpenImmersionRational

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable (f : Y ⟶ X) [IsOpenImmersion f]

/-- An actual equation for a global Cartier divisor transports to an
equation for its restriction on a nonempty inverse-image open. -/
theorem cartierRestriction_globalEquation_preimage (D : CartierDivisor X)
    (U : X.Opens) [Nonempty U] [Nonempty (f ⁻¹ᵁ U)] (g : X.functionFieldˣ)
    (hg : cartierEquationClassHom X U (Additive.ofMul g) =
      (cartierDivisorSheaf X).val.map (homOfLE (show U ≤ ⊤ from le_top)).op D) :
    cartierEquationClassHom Y (f ⁻¹ᵁ U)
        (Additive.ofMul (Units.map (functionFieldIso f).hom.hom.toMonoidHom g)) =
      (cartierDivisorSheaf Y).val.map
        (homOfLE (show f ⁻¹ᵁ U ≤ ⊤ from le_top)).op (cartierRestrictionHom f D) := by
  calc
    _ = (cartierPullback f).val.app (op U)
        (cartierEquationClassHom X U (Additive.ofMul g)) :=
      (cartierPullback_equation f U g).symm
    _ = (cartierPullback f).val.app (op U)
        ((cartierDivisorSheaf X).val.map
          (homOfLE (show U ≤ ⊤ from le_top)).op D) := congrArg _ hg
    _ = _ := NatTrans.naturality_apply (cartierPullback f).val
      (homOfLE (show U ≤ ⊤ from le_top)).op D

/-- An actual equation on the image of a nonempty source open gives
the transported equation on that source open. -/
theorem cartierRestriction_globalEquation_image (D : CartierDivisor X)
    (V : Y.Opens) [Nonempty V] (g : X.functionFieldˣ)
    (hg : letI := nonempty_image f V
      cartierEquationClassHom X (f ''ᵁ V) (Additive.ofMul g) =
        (cartierDivisorSheaf X).val.map
          (homOfLE (show f ''ᵁ V ≤ ⊤ from le_top)).op D) :
    cartierEquationClassHom Y V
        (Additive.ofMul (Units.map (functionFieldIso f).hom.hom.toMonoidHom g)) =
      (cartierDivisorSheaf Y).val.map
        (homOfLE (show V ≤ ⊤ from le_top)).op (cartierRestrictionHom f D) := by
  letI := nonempty_image f V
  letI : Nonempty (f ⁻¹ᵁ (f ''ᵁ V)) := by
    rw [Scheme.Hom.preimage_image_eq]
    infer_instance
  have h := cartierRestriction_globalEquation_preimage f D (f ''ᵁ V) g hg
  have transport (W : Y.Opens) [Nonempty W] (hWV : W = V)
      (hW : cartierEquationClassHom Y W
          (Additive.ofMul (Units.map (functionFieldIso f).hom.hom.toMonoidHom g)) =
        (cartierDivisorSheaf Y).val.map
          (homOfLE (show W ≤ ⊤ from le_top)).op (cartierRestrictionHom f D)) :
      cartierEquationClassHom Y V
          (Additive.ofMul (Units.map (functionFieldIso f).hom.hom.toMonoidHom g)) =
        (cartierDivisorSheaf Y).val.map
          (homOfLE (show V ≤ ⊤ from le_top)).op (cartierRestrictionHom f D) := by
    subst W
    exact hW
  exact transport (f ⁻¹ᵁ (f ''ᵁ V)) (f.preimage_image_eq V) h

/-- The inverse images of the existing actual equation charts cover
the source scheme, including after restriction to any source open. -/
theorem cartierPreimageEquationCharts_coversTop (D : CartierDivisor X) :
    (Opens.grothendieckTopology Y).CoversTop
      (fun c : CartierEquationChart X D => f ⁻¹ᵁ c.openSet) := by
  intro V y hy
  obtain ⟨W, i, hW, hyW⟩ := cartierEquationCharts_coversTop X D ⊤ (f.base y) trivial
  obtain ⟨c, ⟨j⟩⟩ := hW
  refine ⟨V ⊓ (f ⁻¹ᵁ c.openSet), homOfLE inf_le_left, ?_, ?_⟩
  · exact ⟨c, ⟨homOfLE inf_le_right⟩⟩
  · exact ⟨hy, j.le hyW⟩

end KltDP.Geometry.OpenImmersionRational
