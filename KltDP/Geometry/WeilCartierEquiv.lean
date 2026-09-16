import KltDP.Geometry.WeilCartierConstruction

/-!
# The actual Cartier–Weil equivalence on a locally factorial surface

If a Cartier divisor has zero Weil image, each of its actual local
equations has zero order on every curve meeting its chart. The proved
local unit criterion identifies its Cartier equation class with zero.
The sheaf's separatedness then makes the global Cartier divisor zero.
This gives injectivity of the actual Cartier-to-Weil homomorphism.
Combining it with the constructed surjectivity gives an additive
equivalence of the original divisor groups.

The hypothesis that every actual stalk is a UFD is explicit. No regular
local ring theorem or Cartier–Weil theorem is admitted or assumed here.
The additive-equivalence packaging uses pinned `AddEquiv.ofBijective`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace KltDP.Geometry.NormalProjectiveSurface

variable {k : Type u} [Field k] [IsAlgClosed k] (X : NormalProjectiveSurface k)
variable [∀ x : X.toScheme, UniqueFactorizationMonoid (X.stalk x)]

/-- A zero Weil image forces the actual Cartier divisor to be zero. -/
theorem cartierToWeilHom_eq_zero_iff_of_stalks_ufd
    (D : CartierDivisor X.toScheme) : X.cartierToWeilHom D = 0 ↔ D = 0 := by
  constructor
  · intro hD
    apply TopCat.Presheaf.section_ext (cartierDivisorSheaf X.toScheme) ⊤
    intro x _
    obtain ⟨f, U, hxU, hf⟩ := exists_cartierOrderEquation X.toScheme D x
    letI : Nonempty U := ⟨⟨x, hxU⟩⟩
    have heq : cartierEquationClassHom X.toScheme U (Additive.ofMul f) =
        cartierEquationClassHom X.toScheme U (Additive.ofMul 1) := by
      apply X.cartierEquationClass_eq_of_equal_curve_orders U f 1
      intro C hC
      have hzero : X.cartierToWeilHom D C = 0 :=
        congrArg (fun E : X.WeilDivisor => E C) hD
      have horder := X.cartierToWeilHom_apply_of_equation D C U hC f hf
      simpa only [PrimeCurve.order_one] using horder.symm.trans hzero
    have hres : (cartierDivisorSheaf X.toScheme).val.map
        (homOfLE (show U ≤ ⊤ from le_top)).op D =
      (cartierDivisorSheaf X.toScheme).val.map
        (homOfLE (show U ≤ ⊤ from le_top)).op 0 := by
      rw [← hf, heq]
      exact (cartierEquationClassHom X.toScheme U).map_zero.trans
        ((cartierDivisorSheaf X.toScheme).val.map
          (homOfLE (show U ≤ ⊤ from le_top)).op).hom.map_zero.symm
    exact (TopCat.Presheaf.germ_res_apply (cartierDivisorSheaf X.toScheme).val
      (homOfLE (show U ≤ ⊤ from le_top)) x hxU D).symm.trans
        ((congrArg (TopCat.Presheaf.germ (cartierDivisorSheaf X.toScheme).val U x hxU) hres).trans
          (TopCat.Presheaf.germ_res_apply (cartierDivisorSheaf X.toScheme).val
            (homOfLE (show U ≤ ⊤ from le_top)) x hxU 0))
  · rintro rfl
    exact X.cartierToWeilHom.map_zero

/-- The actual Cartier-to-Weil homomorphism is injective on the
locally factorial surface. -/
theorem cartierToWeilHom_injective_of_stalks_ufd :
    Function.Injective X.cartierToWeilHom := by
  intro D E hDE
  apply sub_eq_zero.mp
  apply (X.cartierToWeilHom_eq_zero_iff_of_stalks_ufd (D - E)).mp
  rw [map_sub, hDE, sub_self]

/-- The actual Cartier and Weil divisor groups are additively
equivalent when all actual surface stalks are factorial. -/
def cartierWeilEquiv : CartierDivisor X.toScheme ≃+ X.WeilDivisor :=
  AddEquiv.ofBijective X.cartierToWeilHom
    ⟨X.cartierToWeilHom_injective_of_stalks_ufd,
      X.cartierToWeilHom_surjective_of_stalks_ufd⟩

theorem cartierWeilEquiv_apply (D : CartierDivisor X.toScheme) :
    X.cartierWeilEquiv D = X.cartierToWeilHom D := rfl

/-- The equivalence sends the original principal Cartier divisor to
the original principal Weil divisor of the same rational function. -/
theorem cartierWeilEquiv_principal (f : X.toScheme.functionFieldˣ) :
    X.cartierWeilEquiv
        (principalCartierDivisorHom X.toScheme (Additive.ofMul f)) =
      X.principalDivisor f :=
  X.cartierToWeilHom_principal f

end KltDP.Geometry.NormalProjectiveSurface
