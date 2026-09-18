import KltDP.Geometry.NormalStalkCurveUnits
import KltDP.Geometry.CartierWeilMap
import KltDP.Geometry.CartierDivisorModule

/-!
# Injectivity of the original Cartier-to-Weil map on a normal surface

A zero Weil image makes each actual local equation a unit in every
relevant normal stalk. On a smaller original neighborhood it is an
actual regular unit, so its original quotient-sheaf class is zero.
Sheaf separatedness gives equality of the original global Cartier
sections. The accepted curve-to-stalk-prime correspondence retains its
algebraically closed ground-field hypothesis; factoriality is not used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

attribute [local instance] Types.instFunLike Types.instConcreteCategory

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)

/-- A zero original Weil image forces the actual Cartier divisor to be zero. -/
theorem cartierToWeilHom_eq_zero_iff (D : CartierDivisor X.toScheme) :
    X.cartierToWeilHom D = 0 ↔ D = 0 := by
  constructor
  · intro hD
    apply TopCat.Presheaf.section_ext (cartierDivisorSheaf X.toScheme) ⊤
    intro x _
    obtain ⟨f, U, hxU, hf⟩ := exists_cartierOrderEquation X.toScheme D x
    letI : Nonempty U := ⟨⟨x, hxU⟩⟩
    have horders : ∀ C : X.PrimeCurve, x ∈ C → C.order f = 0 := by
      intro C hxC
      have hzero : X.cartierToWeilHom D C = 0 :=
        congrArg (fun E : X.WeilDivisor => E C) hD
      exact (X.cartierToWeilHom_apply_of_equation D C U
        (C.genericPoint_mem_of_mem ⟨x, hxU⟩ hxC) f hf).symm.trans hzero
    obtain ⟨V, hVU, hxV, b, hb⟩ :=
      X.exists_regular_unit_near_of_curve_orders_eq_zero x U hxU f horders
    letI : Nonempty V := ⟨⟨x, hxV⟩⟩
    have hlocal : cartierEquationClassHom X.toScheme V (Additive.ofMul f) = 0 :=
      (cartierEquationClassHom_eq_zero_iff X.toScheme V f).mpr ⟨b, hb⟩
    have hres : (cartierDivisorSheaf X.toScheme).val.map
        (homOfLE (show V ≤ ⊤ from le_top)).op D =
      (cartierDivisorSheaf X.toScheme).val.map
        (homOfLE (show V ≤ ⊤ from le_top)).op 0 :=
      (cartierGlobalEquation_restrict X.toScheme D (homOfLE hVU) f hf).symm.trans
        (hlocal.trans ((cartierDivisorSheaf X.toScheme).val.map
          (homOfLE (show V ≤ ⊤ from le_top)).op).hom.map_zero.symm)
    exact (TopCat.Presheaf.germ_res_apply (cartierDivisorSheaf X.toScheme).val
      (homOfLE (show V ≤ ⊤ from le_top)) x hxV D).symm.trans
        ((congrArg (TopCat.Presheaf.germ (cartierDivisorSheaf X.toScheme).val V x hxV) hres).trans
          (TopCat.Presheaf.germ_res_apply (cartierDivisorSheaf X.toScheme).val
            (homOfLE (show V ≤ ⊤ from le_top)) x hxV 0))
  · rintro rfl
    exact X.cartierToWeilHom.map_zero

/-- The original Cartier-to-Weil homomorphism is injective on the normal surface. -/
theorem cartierToWeilHom_injective : Function.Injective X.cartierToWeilHom := by
  intro D E hDE
  apply sub_eq_zero.mp
  apply (X.cartierToWeilHom_eq_zero_iff (D - E)).mp
  rw [map_sub, hDE, sub_self]

end KltDP.Geometry.NormalProjectiveSurface
