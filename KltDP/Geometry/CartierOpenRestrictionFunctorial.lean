import KltDP.Geometry.CartierOpenRestrictionEquations
import KltDP.Geometry.OpenImmersionFunctionFieldFunctorial

/-!
# Identity and composition of actual Cartier restriction

Global Cartier sections agree when their actual germs agree. Around
each point, the existing quotient-sheaf theorem supplies a genuine local
rational equation. The proved equation transport and actual function-field
identity/composition laws identify the restricted equations, hence the
actual Cartier sections. No global equation is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.OpenImmersionRational

variable {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]

/-- Identity restriction on the actual Cartier divisor group. -/
theorem cartierRestrictionHom_id :
    cartierRestrictionHom (𝟙 X) = AddMonoidHom.id (CartierDivisor X) := by
  apply AddMonoidHom.ext
  intro D
  change cartierRestrictionHom (𝟙 X) D = D
  apply TopCat.Presheaf.section_ext (cartierDivisorSheaf X) ⊤
  intro x _
  obtain ⟨U, i, hxU, a, ha⟩ := exists_local_cartier_equation X ⊤ D x trivial
  letI : Nonempty U := ⟨⟨x, hxU⟩⟩
  have hi : i = homOfLE (show U ≤ ⊤ from le_top) := Subsingleton.elim _ _
  have ha' : cartierEquationClassHom X U (Additive.ofMul a) =
      (cartierDivisorSheaf X).val.map (homOfLE (show U ≤ ⊤ from le_top)).op D := by
    simpa only [hi] using ha
  letI : Nonempty ((𝟙 X) ⁻¹ᵁ U) := ⟨⟨x, hxU⟩⟩
  have hr := cartierRestriction_globalEquation_preimage (𝟙 X) D U a ha'
  rw [functionFieldUnitMap_id] at hr
  have heq : (cartierDivisorSheaf X).val.map
      (homOfLE (show U ≤ ⊤ from le_top)).op (cartierRestrictionHom (𝟙 X) D) =
    (cartierDivisorSheaf X).val.map
      (homOfLE (show U ≤ ⊤ from le_top)).op D := hr.symm.trans ha'
  exact (TopCat.Presheaf.germ_res_apply (cartierDivisorSheaf X).val
    (homOfLE (show U ≤ ⊤ from le_top)) x hxU (cartierRestrictionHom (𝟙 X) D)).symm.trans
      ((congrArg (TopCat.Presheaf.germ (cartierDivisorSheaf X).val U x hxU) heq).trans
        (TopCat.Presheaf.germ_res_apply (cartierDivisorSheaf X).val
          (homOfLE (show U ≤ ⊤ from le_top)) x hxU D))

/-- Actual Cartier restriction is contravariantly compatible with
composition of open immersions. -/
theorem cartierRestrictionHom_comp (f : Y ⟶ X) (g : Z ⟶ Y)
    [IsOpenImmersion f] [IsOpenImmersion g] :
    cartierRestrictionHom (g ≫ f) =
      (cartierRestrictionHom g).comp (cartierRestrictionHom f) := by
  apply AddMonoidHom.ext
  intro D
  change cartierRestrictionHom (g ≫ f) D =
    cartierRestrictionHom g (cartierRestrictionHom f D)
  apply TopCat.Presheaf.section_ext (cartierDivisorSheaf Z) ⊤
  intro z _
  obtain ⟨U, i, hzU, a, ha⟩ :=
    exists_local_cartier_equation X ⊤ D ((g ≫ f).base z) trivial
  letI : Nonempty U := ⟨⟨(g ≫ f).base z, hzU⟩⟩
  letI := preimage_nonempty f U
  letI := preimage_nonempty g (f ⁻¹ᵁ U)
  letI : Nonempty ((g ≫ f) ⁻¹ᵁ U) := ⟨⟨z, hzU⟩⟩
  have hi : i = homOfLE (show U ≤ ⊤ from le_top) := Subsingleton.elim _ _
  have ha' : cartierEquationClassHom X U (Additive.ofMul a) =
      (cartierDivisorSheaf X).val.map (homOfLE (show U ≤ ⊤ from le_top)).op D := by
    simpa only [hi] using ha
  have hf := cartierRestriction_globalEquation_preimage f D U a ha'
  have hg := cartierRestriction_globalEquation_preimage g (cartierRestrictionHom f D)
    (f ⁻¹ᵁ U) (Units.map (functionFieldIso f).hom.hom.toMonoidHom a) hf
  have hgf := cartierRestriction_globalEquation_preimage (g ≫ f) D U a ha'
  rw [functionFieldUnitMap_comp] at hgf
  let W : Z.Opens := (g ≫ f) ⁻¹ᵁ U
  have hzW : z ∈ W := hzU
  have heq : (cartierDivisorSheaf Z).val.map
      (homOfLE (show W ≤ ⊤ from le_top)).op (cartierRestrictionHom (g ≫ f) D) =
    (cartierDivisorSheaf Z).val.map (homOfLE (show W ≤ ⊤ from le_top)).op
      (cartierRestrictionHom g (cartierRestrictionHom f D)) := hgf.symm.trans hg
  exact (TopCat.Presheaf.germ_res_apply (cartierDivisorSheaf Z).val
    (homOfLE (show W ≤ ⊤ from le_top)) z hzW (cartierRestrictionHom (g ≫ f) D)).symm.trans
      ((congrArg (TopCat.Presheaf.germ (cartierDivisorSheaf Z).val W z hzW) heq).trans
        (TopCat.Presheaf.germ_res_apply (cartierDivisorSheaf Z).val
          (homOfLE (show W ≤ ⊤ from le_top)) z hzW
            (cartierRestrictionHom g (cartierRestrictionHom f D))))

end KltDP.Geometry.OpenImmersionRational
