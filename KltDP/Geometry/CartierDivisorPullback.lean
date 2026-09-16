import KltDP.Geometry.CartierDivisorOfEquations
import KltDP.Geometry.EffectiveCartierIdeal

/-!
# Pullback of an effective Cartier divisor along a morphism preserving the generic point

For a morphism `π : X ⟶ Y` of integral schemes sending the generic point of `X` to the generic
point of `Y` (`GenericPointPreserving π`; every dominant morphism), the stalk map at the generic
point is a map of function fields `functionFieldMap π : K(Y) ⟶ K(X)` compatible with germs
(`functionFieldMap_germ`). An effective Cartier divisor `D` on `Y` with regular equations
(`HasRegularCartierEquations`) is pulled back to `pullbackDivisor π D hD : CartierDivisor X`,
glued (BRIEF8 `cartierDivisorOfEquations`) from the equations `π^*f` on the preimages `π ⁻¹ᵁ U` of
the regular charts `(U, f, c)` of `D`; the pulled-back divisor has the regular charts
`(π ⁻¹ᵁ U, π^*f, π.app U c)` (`pullbackDivisor_regularChart`, `pullbackDivisor_hasRegularEquations`)
and its accepted ideal-sheaf data on an affine open `W ≤ π ⁻¹ᵁ U` is the principal ideal generated
by `π.appLE U W c` (`pullbackIdealData_ideal`).

Not proved here: the compatibility of `cartierPicardHom` with the Picard pullback, and the
identification with the base change of the zero scheme.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry

/-- A morphism of integral schemes sending the generic point to the generic point. -/
class GenericPointPreserving {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (π : X ⟶ Y) :
    Prop where
  base_genericPoint : π.base (genericPoint X) = genericPoint Y

section FunctionFieldMap

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (π : X ⟶ Y) [hπ : GenericPointPreserving π]

theorem genericPoint_mem_preimage (U : Y.Opens) [Nonempty U] : genericPoint X ∈ π ⁻¹ᵁ U := by
  show π.base (genericPoint X) ∈ U
  rw [hπ.base_genericPoint]
  exact genericPoint_mem_nonempty_open Y U

/-- Preimages of nonempty opens are nonempty. -/
instance preimage_nonempty (U : Y.Opens) [Nonempty U] : Nonempty (π ⁻¹ᵁ U) :=
  ⟨⟨genericPoint X, genericPoint_mem_preimage π U⟩⟩

theorem base_genericPoint_specializes : π.base (genericPoint X) ⤳ genericPoint Y := by
  rw [hπ.base_genericPoint]

/-- The function-field map `K(Y) ⟶ K(X)`: the stalk map of `π` at the generic point. -/
def functionFieldMap : Y.functionField ⟶ X.functionField :=
  Y.presheaf.stalkSpecializes (base_genericPoint_specializes π) ≫ π.stalkMap (genericPoint X)

theorem functionFieldMap_germ (U : Y.Opens) [Nonempty U] (s : Γ(Y, U)) :
    functionFieldMap π (Y.germToFunctionField U s) =
      X.germToFunctionField (π ⁻¹ᵁ U) (π.app U s) := by
  simp only [functionFieldMap, Scheme.germToFunctionField, CommRingCat.comp_apply,
    TopCat.Presheaf.germ_stalkSpecializes_apply, Scheme.stalkMap_germ_apply]

theorem functionFieldMap_germ_appLE (U : Y.Opens) [Nonempty U] (W : X.Opens) [Nonempty W]
    (hW : W ≤ π ⁻¹ᵁ U) (s : Γ(Y, U)) :
    functionFieldMap π (Y.germToFunctionField U s) = X.germToFunctionField W (π.appLE U W hW s) := by
  rw [functionFieldMap_germ, Scheme.Hom.appLE, CommRingCat.comp_apply]
  exact (TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hW) (genericPoint X) _ _).symm

end FunctionFieldMap

section Pullback

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (π : X ⟶ Y) [GenericPointPreserving π]
  (D : CartierDivisor Y) (hD : HasRegularCartierEquations Y D)

/-- The pulled-back rational equation of a regular chart of `D`. -/
def pulledEquation (c : RegularCartierEquationChart Y D) : X.functionFieldˣ :=
  Units.map (functionFieldMap π).hom.toMonoidHom c.chart.equation

theorem pulledEquation_val (c : RegularCartierEquationChart Y D) :
    (pulledEquation π D c : X.functionField) = functionFieldMap π c.chart.equation := rfl

/-- The pulled-back regular coefficient of a regular chart of `D`. -/
def pulledCoefficient (c : RegularCartierEquationChart Y D) : Γ(X, π ⁻¹ᵁ c.chart.openSet) :=
  π.app c.chart.openSet c.coefficient

theorem germ_pulledCoefficient (c : RegularCartierEquationChart Y D) :
    X.germToFunctionField (π ⁻¹ᵁ c.chart.openSet) (pulledCoefficient π D c) =
      (pulledEquation π D c : X.functionField) := by
  rw [pulledEquation_val, pulledCoefficient, ← functionFieldMap_germ, c.germ_eq]

omit [IsIntegral X] [GenericPointPreserving π] in
theorem preimage_inf_le (U V : Y.Opens) : π ⁻¹ᵁ U ⊓ π ⁻¹ᵁ V ≤ π ⁻¹ᵁ (U ⊓ V) :=
  fun _ hx => hx

/-- The pulled-back equations of two charts agree on the overlap. -/
theorem pulledEquation_compat (c d : RegularCartierEquationChart Y D) :
    cartierEquationClassHom X (π ⁻¹ᵁ c.chart.openSet ⊓ π ⁻¹ᵁ d.chart.openSet)
        (Additive.ofMul (pulledEquation π D c)) =
      cartierEquationClassHom X (π ⁻¹ᵁ c.chart.openSet ⊓ π ⁻¹ᵁ d.chart.openSet)
        (Additive.ofMul (pulledEquation π D d)) := by
  have hcd : cartierEquationClassHom Y (c.chart.openSet ⊓ d.chart.openSet)
        (Additive.ofMul c.chart.equation) =
      cartierEquationClassHom Y (c.chart.openSet ⊓ d.chart.openSet)
        (Additive.ofMul d.chart.equation) := by
    rw [cartierGlobalEquation_restrict Y D (homOfLE inf_le_left) c.chart.equation
      c.chart.represents, cartierGlobalEquation_restrict Y D (homOfLE inf_le_right)
      d.chart.equation d.chart.represents]
  obtain ⟨a, ha⟩ := (cartierEquationClassHom_eq_iff Y _ _ _).mp hcd
  have ha' : (Y.germToFunctionField (c.chart.openSet ⊓ d.chart.openSet)) (a : Γ(Y, _)) =
      (c.chart.equation : Y.functionField) / d.chart.equation := by
    have := congrArg Units.val ha
    rwa [Units.val_div_eq_div_val] at this
  rw [cartierEquationClassHom_eq_iff]
  refine ⟨Units.map (π.appLE (c.chart.openSet ⊓ d.chart.openSet) _
    (preimage_inf_le π _ _)).hom.toMonoidHom a, ?_⟩
  apply Units.ext
  rw [Units.val_div_eq_div_val, pulledEquation_val, pulledEquation_val]
  change (X.germToFunctionField (π ⁻¹ᵁ c.chart.openSet ⊓ π ⁻¹ᵁ d.chart.openSet))
      (π.appLE (c.chart.openSet ⊓ d.chart.openSet) _ (preimage_inf_le π _ _) (a : Γ(Y, _))) =
    (functionFieldMap π).hom c.chart.equation / (functionFieldMap π).hom d.chart.equation
  rw [← map_div₀, ← ha', ← functionFieldMap_germ_appLE]

include hD in
theorem pulled_cover :
    (⊤ : X.Opens) ≤ iSup (fun c : RegularCartierEquationChart Y D => π ⁻¹ᵁ c.chart.openSet) := by
  intro x _
  obtain ⟨c, hc⟩ := hD (π.base x)
  exact Opens.mem_iSup.mpr ⟨c, hc⟩

/-- The pullback of `D` along `π`: glued from the pulled-back equations of all regular charts. -/
def pullbackDivisor : CartierDivisor X :=
  cartierDivisorOfEquations X (fun c : RegularCartierEquationChart Y D => π ⁻¹ᵁ c.chart.openSet)
    (pulled_cover π D hD) (fun c => pulledEquation π D c)
    (fun c d => pulledEquation_compat π D c d)

theorem pullbackDivisor_restrict (c : RegularCartierEquationChart Y D) :
    (cartierDivisorSheaf X).val.map (homOfLE (show π ⁻¹ᵁ c.chart.openSet ≤ ⊤ from le_top)).op
        (pullbackDivisor π D hD) =
      cartierEquationClassHom X (π ⁻¹ᵁ c.chart.openSet) (Additive.ofMul (pulledEquation π D c)) :=
  cartierDivisorOfEquations_restrict X
    (fun c : RegularCartierEquationChart Y D => π ⁻¹ᵁ c.chart.openSet) (pulled_cover π D hD)
    (fun c => pulledEquation π D c) (fun c d => pulledEquation_compat π D c d) c

/-- The preimage of a regular chart of `D` is a regular chart of the pullback. -/
def pullbackDivisor_regularChart (c : RegularCartierEquationChart Y D) :
    RegularCartierEquationChart X (pullbackDivisor π D hD) :=
  cartierDivisorOfEquations_regularChart X
    (fun c : RegularCartierEquationChart Y D => π ⁻¹ᵁ c.chart.openSet) (pulled_cover π D hD)
    (fun c => pulledEquation π D c) (fun c d => pulledEquation_compat π D c d)
    (fun c => pulledCoefficient π D c) (fun c => germ_pulledCoefficient π D c) c

theorem pullbackDivisor_regularChart_openSet (c : RegularCartierEquationChart Y D) :
    (pullbackDivisor_regularChart π D hD c).chart.openSet = π ⁻¹ᵁ c.chart.openSet := rfl

theorem pullbackDivisor_regularChart_coefficient (c : RegularCartierEquationChart Y D) :
    (pullbackDivisor_regularChart π D hD c).coefficient = π.app c.chart.openSet c.coefficient := rfl

theorem pullbackDivisor_hasRegularEquations :
    HasRegularCartierEquations X (pullbackDivisor π D hD) :=
  cartierDivisorOfEquations_hasRegularEquations X
    (fun c : RegularCartierEquationChart Y D => π ⁻¹ᵁ c.chart.openSet) (pulled_cover π D hD)
    (fun c => pulledEquation π D c) (fun c d => pulledEquation_compat π D c d)
    (fun c => pulledCoefficient π D c) (fun c => germ_pulledCoefficient π D c)

/-- The accepted ideal-sheaf data of the pulled-back divisor. -/
def pullbackIdealData : X.IdealSheafData :=
  effectiveCartierIdealDataOfRegularEquations X (pullbackDivisor π D hD)
    (pullbackDivisor_hasRegularEquations π D hD)

/-- On an affine open inside the preimage of a regular chart `(U, f, c)` of `D`, the ideal of the
pulled-back divisor is generated by `π.appLE U W c`. -/
theorem pullbackIdealData_ideal (c : RegularCartierEquationChart Y D) (W : X.affineOpens)
    [Nonempty W.1] (hW : W.1 ≤ π ⁻¹ᵁ c.chart.openSet) :
    (pullbackIdealData π D hD).ideal W =
      Ideal.span {π.appLE c.chart.openSet W.1 hW c.coefficient} :=
  effectiveCartierIdealDataOfRegularEquations_ideal_chart X (pullbackDivisor π D hD)
    (pullbackDivisor_hasRegularEquations π D hD)
    (RegularCartierEquationChart.restrict X _ (pullbackDivisor_regularChart π D hD c) W.1 hW) W.2

end Pullback

end KltDP.Geometry
