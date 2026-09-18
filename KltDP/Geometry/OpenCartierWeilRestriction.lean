import KltDP.Geometry.OpenCartierWeil
import KltDP.Geometry.CartierOpenRestrictionEquations

/-!
# Extending the restriction of an actual global Cartier divisor

On an open containing every prime generic point, restriction followed by the
existing Cartier-to-Weil extension recovers the original Weil divisor. Local
equations and the original open-immersion field isomorphism give each coefficient.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace KltDP.Geometry.OpenCartierWeil

open OpenImmersionRational

variable {k : Type u} [Field k] {X : NormalProjectiveSurface k}
variable (V : X.toScheme.Opens) [Nonempty V.toScheme]

local instance : Nonempty V := ⟨Classical.choice inferInstance⟩
local instance : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι

/-- The coefficient of a restricted global divisor is its original coefficient
at every prime generic point belonging to the actual open. -/
theorem restrictedCoefficient_restriction
    (D : CartierDivisor X.toScheme) (C : X.PrimeCurve) (hCV : C.genericPoint ∈ V) :
    restrictedCoefficient V (cartierRestrictionHom V.ι D) C = X.cartierToWeilHom D C := by
  obtain ⟨f, W, hCW, hf⟩ := exists_cartierOrderEquation X.toScheme D C.genericPoint
  letI : Nonempty W := ⟨⟨C.genericPoint, hCW⟩⟩
  have hy : (⟨C.genericPoint, hCV⟩ : V.toScheme) ∈ V.ι ⁻¹ᵁ W := hCW
  letI : Nonempty (V.ι ⁻¹ᵁ W) := ⟨⟨⟨C.genericPoint, hCV⟩, hy⟩⟩
  have himage : C.genericPoint ∈ V.ι ''ᵁ (V.ι ⁻¹ᵁ W) :=
    (Scheme.Hom.map_mem_image_iff V.ι).mpr hy
  have hEq := cartierRestriction_globalEquation_preimage V.ι D W f hf
  have hcancel : transportUnit V
      (Units.map (functionFieldIso V.ι).hom.hom.toMonoidHom f) = f := by
    apply Units.ext
    exact Iso.hom_inv_id_apply (functionFieldIso V.ι) (f : X.toScheme.functionField)
  rw [restrictedCoefficient_eq_of_equation V (cartierRestrictionHom V.ι D) C
    (V.ι ⁻¹ᵁ W) himage _ hEq, hcancel]
  exact (X.cartierToWeilHom_apply_of_equation D C W hCW f hf).symm

/-- Restricting a global Cartier divisor to a large open and extending its
Weil coefficients recovers the original global Cartier-to-Weil image. -/
theorem restrictedWeilHom_restriction
    (hV : ∀ C : X.PrimeCurve, C.genericPoint ∈ V)
    (D : CartierDivisor X.toScheme) :
    restrictedWeilHom V (cartierRestrictionHom V.ι D) = X.cartierToWeilHom D := by
  apply Finsupp.ext
  intro C
  exact restrictedCoefficient_restriction V D C (hV C)

end KltDP.Geometry.OpenCartierWeil
