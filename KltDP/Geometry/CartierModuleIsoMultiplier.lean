import KltDP.Geometry.CartierModuleIsoRationalInclusion

/-!
# The actual rational multiplier and principal divisor of a given isomorphism

The multiplier is constructed from the given isomorphism in original equation
frames. On every common equation chart it differs from f/g by an actual regular
unit. Original Cartier-sheaf separatedness therefore identifies its principal
divisor with D - E, while retaining the literal fractional-module inclusion square.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry.CartierModuleIsoMultiplier

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (X : Scheme.{u}) [IsIntegral X] (D E : CartierDivisor X)
    (e : cartierDivisorModule X D ≅ cartierDivisorModule X E)

section Chart

variable (U : X.Opens) [Nonempty U] (f g : X.functionFieldˣ)
    (hf : cartierEquationClassHom X U (Additive.ofMul f) =
      (cartierDivisorSheaf X).val.map (homOfLE (le_top : U ≤ ⊤)).op D)
    (hg : cartierEquationClassHom X U (Additive.ofMul g) =
      (cartierDivisorSheaf X).val.map (homOfLE (le_top : U ≤ ⊤)).op E)

/-- The sign is fixed by the original frames 1/f and 1/g. -/
theorem equation_mul_chartMultiplierUnit :
    g * chartMultiplierUnit X D E e U f g hf hg =
      f * Units.map (X.germToFunctionField U).hom.toMonoidHom
        (chartCoordinateUnit X D E e U f g hf hg) := by
  unfold chartMultiplierUnit
  calc
    _ = (g * g⁻¹) *
        (f * Units.map (X.germToFunctionField U).hom.toMonoidHom
          (chartCoordinateUnit X D E e U f g hf hg)) := by ac_rfl
    _ = _ := by rw [mul_inv_cancel, one_mul]

/-- The principal divisor belongs to the multiplier of this given map. -/
theorem sub_eq_principal_chartMultiplierUnit :
    D - E = principalCartierDivisorHom X
      (Additive.ofMul (chartMultiplierUnit X D E e U f g hf hg)) := by
  have hsum : D = E + principalCartierDivisorHom X
      (Additive.ofMul (chartMultiplierUnit X D E e U f g hf hg)) := by
    apply TopCat.Presheaf.IsSheaf.section_ext (cartierDivisorSheaf X).cond
    intro x hx
    obtain ⟨V, i, hxV, f', g', hf', hg'⟩ :=
      exists_common_cartier_equations X D E ⊤ x trivial
    letI : Nonempty V := ⟨⟨x, hxV⟩⟩
    have hmul : g' * chartMultiplierUnit X D E e U f g hf hg =
        f' * Units.map (X.germToFunctionField V).hom.toMonoidHom
          (chartCoordinateUnit X D E e V f' g' hf' hg') :=
      (congrArg (fun q : X.functionFieldˣ => g' * q)
        (chartMultiplierUnit_eq X D E e U f g hf hg V f' g' hf' hg')).trans
        (equation_mul_chartMultiplierUnit X D E e V f' g' hf' hg')
    refine ⟨V, le_top, hxV, ?_⟩
    change (cartierDivisorSheaf X).val.map (homOfLE (le_top : V ≤ ⊤)).op D =
      (cartierDivisorSheaf X).val.map (homOfLE (le_top : V ≤ ⊤)).op
        (E + principalCartierDivisorHom X
          (Additive.ofMul (chartMultiplierUnit X D E e U f g hf hg)))
    calc
      _ = cartierEquationClassHom X V (Additive.ofMul f') := hf'.symm
      _ = cartierEquationClassHom X V
          (Additive.ofMul (f' * Units.map (X.germToFunctionField V).hom.toMonoidHom
            (chartCoordinateUnit X D E e V f' g' hf' hg'))) :=
        (cartierEquationClassHom_mul_regular_unit X V f'
          (chartCoordinateUnit X D E e V f' g' hf' hg')).symm
      _ = cartierEquationClassHom X V
          (Additive.ofMul (g' * chartMultiplierUnit X D E e U f g hf hg)) :=
        congrArg (fun q : X.functionFieldˣ =>
          cartierEquationClassHom X V (Additive.ofMul q)) hmul.symm
      _ = _ := cartierGlobalEquation_mul X E
        (principalCartierDivisorHom X
          (Additive.ofMul (chartMultiplierUnit X D E e U f g hf hg))) V g'
        (chartMultiplierUnit X D E e U f g hf hg) hg'
        (principalCartierDivisor_equation X
          (chartMultiplierUnit X D E e U f g hf hg) V)
  simpa only [add_sub_cancel_left] using congrArg (fun A : CartierDivisor X => A - E) hsum

end Chart

/-- Every given actual Cartier-module isomorphism has one original rational
unit which both represents D - E and gives its literal inclusion square. -/
theorem exists_multiplier :
    ∃ q : X.functionFieldˣ,
      D - E = principalCartierDivisorHom X (Additive.ofMul q) ∧
      e.hom ≫ cartierDivisorModuleInclusion X E =
        cartierDivisorModuleInclusion X D ≫ (rationalFunctionMulIso X q).hom := by
  obtain ⟨U, i, hxU, f, g, hf, hg⟩ :=
    exists_common_cartier_equations X D E ⊤ (genericPoint X) trivial
  letI : Nonempty U := ⟨⟨genericPoint X, hxU⟩⟩
  exact ⟨chartMultiplierUnit X D E e U f g hf hg,
    sub_eq_principal_chartMultiplierUnit X D E e U f g hf hg,
    hom_inclusion_eq_chartMultiplierUnit X D E e U f g hf hg⟩

end KltDP.Geometry.CartierModuleIsoMultiplier

#check @KltDP.Geometry.CartierModuleIsoMultiplier.sub_eq_principal_chartMultiplierUnit
#print axioms KltDP.Geometry.CartierModuleIsoMultiplier.sub_eq_principal_chartMultiplierUnit
#check @KltDP.Geometry.CartierModuleIsoMultiplier.exists_multiplier
#print axioms KltDP.Geometry.CartierModuleIsoMultiplier.exists_multiplier
