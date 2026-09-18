import KltDP.Geometry.NormalCartierWeilInjective
import KltDP.Geometry.OpenCartierWeil

/-!
# Injectivity of the actual open Cartier-to-Weil extension

Transport an original local equation of the open subscheme to the surface
function field. Zero extended Weil coefficients give zero orders through
the original point. The proved normal-stalk unit criterion makes this
equation a regular unit nearby on the surface. The original Cartier
pullback sends that zero class back to the open, and sheaf separatedness
finishes. No factoriality or smoothness hypothesis is used.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
universe u

namespace KltDP.Geometry.OpenCartierWeil

open OpenImmersionRational

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] [IsAlgClosed k] {X : NormalProjectiveSurface k}
    (U : X.toScheme.Opens) [Nonempty U.toScheme]

local instance : Nonempty U := ⟨Classical.choice inferInstance⟩
local instance : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι

/-- A zero extended Weil divisor forces the original open Cartier divisor
to be zero, using the actual normal surface stalks. -/
theorem restrictedWeilHom_eq_zero_iff (D : CartierDivisor U.toScheme) :
    restrictedWeilHom U D = 0 ↔ D = 0 := by
  constructor
  · intro hD
    apply TopCat.Presheaf.section_ext (cartierDivisorSheaf U.toScheme) ⊤
    intro y _
    obtain ⟨f, W, hyW, hf⟩ := exists_cartierOrderEquation U.toScheme D y
    letI : Nonempty W := ⟨⟨y, hyW⟩⟩
    have hyImage : U.ι.base y ∈ U.ι ''ᵁ W :=
      (Scheme.Hom.map_mem_image_iff U.ι).mpr hyW
    have horders : ∀ C : X.PrimeCurve, U.ι.base y ∈ C →
        C.order (transportUnit U f) = 0 := by
      intro C hyC
      have hzero : restrictedWeilHom U D C = 0 :=
        congrArg (fun E : X.WeilDivisor => E C) hD
      have hC : C.genericPoint ∈ U.ι ''ᵁ W :=
        C.genericPoint_mem_of_mem ⟨U.ι.base y, hyImage⟩ hyC
      exact (restrictedCoefficient_eq_of_equation U D C W hC f hf).symm.trans hzero
    obtain ⟨V, hVW, hyV, b, hb⟩ :=
      X.exists_regular_unit_near_of_curve_orders_eq_zero (U.ι.base y)
        (U.ι ''ᵁ W) hyImage (transportUnit U f) horders
    letI : Nonempty V := ⟨⟨U.ι.base y, hyV⟩⟩
    have hyPre : y ∈ U.ι ⁻¹ᵁ V := hyV
    letI : Nonempty (U.ι ⁻¹ᵁ V) := ⟨⟨y, hyPre⟩⟩
    have hPreW : U.ι ⁻¹ᵁ V ≤ W := by
      intro z hz
      exact (Scheme.Hom.map_mem_image_iff U.ι).mp (hVW hz)
    have hlocalX : cartierEquationClassHom X.toScheme V
        (Additive.ofMul (transportUnit U f)) = 0 :=
      (cartierEquationClassHom_eq_zero_iff X.toScheme V (transportUnit U f)).mpr ⟨b, hb⟩
    have hlocalU : cartierEquationClassHom U.toScheme (U.ι ⁻¹ᵁ V)
        (Additive.ofMul f) = 0 := by
      have hpull := cartierPullback_equation U.ι V (transportUnit U f)
      rw [hlocalX] at hpull
      simpa only [map_zero, transportUnit_hom] using hpull.symm
    have hres : (cartierDivisorSheaf U.toScheme).val.map
        (homOfLE (show U.ι ⁻¹ᵁ V ≤ ⊤ from le_top)).op D =
      (cartierDivisorSheaf U.toScheme).val.map
        (homOfLE (show U.ι ⁻¹ᵁ V ≤ ⊤ from le_top)).op 0 :=
      (cartierGlobalEquation_restrict U.toScheme D (homOfLE hPreW) f hf).symm.trans
        (hlocalU.trans ((cartierDivisorSheaf U.toScheme).val.map
          (homOfLE (show U.ι ⁻¹ᵁ V ≤ ⊤ from le_top)).op).hom.map_zero.symm)
    exact (TopCat.Presheaf.germ_res_apply (cartierDivisorSheaf U.toScheme).val
      (homOfLE (show U.ι ⁻¹ᵁ V ≤ ⊤ from le_top)) y hyPre D).symm.trans
        ((congrArg (TopCat.Presheaf.germ (cartierDivisorSheaf U.toScheme).val
          (U.ι ⁻¹ᵁ V) y hyPre) hres).trans
          (TopCat.Presheaf.germ_res_apply (cartierDivisorSheaf U.toScheme).val
            (homOfLE (show U.ι ⁻¹ᵁ V ≤ ⊤ from le_top)) y hyPre 0))
  · rintro rfl
    exact (restrictedWeilHom U).map_zero

/-- The original Cartier-to-Weil extension on every nonempty open of the
normal projective surface is injective. -/
theorem restrictedWeilHom_injective : Function.Injective (restrictedWeilHom U) := by
  intro D E hDE
  apply sub_eq_zero.mp
  apply (restrictedWeilHom_eq_zero_iff U (D - E)).mp
  rw [map_sub, hDE, sub_self]

/-- Equality of the literal extended Weil divisors gives equality of the
original Cartier divisors, with no supplied injectivity witness. -/
theorem eq_of_restrictedWeilHom_eq {D E : CartierDivisor U.toScheme}
    (hDE : restrictedWeilHom U D = restrictedWeilHom U E) : D = E :=
  restrictedWeilHom_injective U hDE

end KltDP.Geometry.OpenCartierWeil
