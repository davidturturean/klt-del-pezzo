import KltDP.Geometry.PrimeCurveRestrictCartierUnique
import KltDP.Geometry.CurveEffectiveCartierDegree

/-!
# Additivity of the prime-curve intersection number in the divisor

Regular equation charts of two Cartier divisors multiply to a regular chart of their sum on the
common open (`RegularCartierEquationChart.mul`), so effectivity (`hasRegularCartierEquations_add`)
and the non-containment of the curve (`notInSupport_add`) are closed under sums. The restricted
equation of the product chart is the product of the restricted equations, and by the
characterisation of `restrictCartier` through chart equations the restriction is additive
(`restrictCartier_add`). With the admitted 0AYX additivity of the degree and the identification
`C·D = deg O_C(D|_C)` (task 12) this gives **`intersectionDegree_add : C·(D₁ + D₂) = C·D₁ + C·D₂`**.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

section MulChart

variable {X : Scheme.{u}} [IsIntegral X] {D₁ D₂ : CartierDivisor X}

/-- The product of two regular equation charts, a regular chart of the sum on the common open. -/
def RegularCartierEquationChart.mul (c₁ : RegularCartierEquationChart X D₁)
    (c₂ : RegularCartierEquationChart X D₂)
    [hne : Nonempty (c₁.chart.openSet ⊓ c₂.chart.openSet : X.Opens)] :
    RegularCartierEquationChart X (D₁ + D₂) where
  chart :=
    { openSet := c₁.chart.openSet ⊓ c₂.chart.openSet
      nonempty := hne
      equation := c₁.chart.equation * c₂.chart.equation
      represents := by
        letI := hne
        have h₁ := cartierGlobalEquation_restrict X D₁
          (homOfLE (inf_le_left : c₁.chart.openSet ⊓ c₂.chart.openSet ≤ c₁.chart.openSet))
          c₁.chart.equation c₁.chart.represents
        have h₂ := cartierGlobalEquation_restrict X D₂
          (homOfLE (inf_le_right : c₁.chart.openSet ⊓ c₂.chart.openSet ≤ c₂.chart.openSet))
          c₂.chart.equation c₂.chart.represents
        rw [ofMul_mul, map_add, h₁, h₂]
        exact (map_add ((cartierDivisorSheaf X).val.map
          (homOfLE (show c₁.chart.openSet ⊓ c₂.chart.openSet ≤ ⊤ from le_top)).op).hom D₁ D₂).symm }
  coefficient :=
    X.presheaf.map (homOfLE (inf_le_left : c₁.chart.openSet ⊓ c₂.chart.openSet ≤
      c₁.chart.openSet)).op c₁.coefficient *
    X.presheaf.map (homOfLE (inf_le_right : c₁.chart.openSet ⊓ c₂.chart.openSet ≤
      c₂.chart.openSet)).op c₂.coefficient
  germ_eq := by
    letI := hne
    have e₁ : X.germToFunctionField (c₁.chart.openSet ⊓ c₂.chart.openSet)
        (X.presheaf.map (homOfLE (inf_le_left : c₁.chart.openSet ⊓ c₂.chart.openSet ≤
          c₁.chart.openSet)).op c₁.coefficient) =
        X.germToFunctionField c₁.chart.openSet c₁.coefficient :=
      X.presheaf.germ_res_apply _ _ _ c₁.coefficient
    have e₂ : X.germToFunctionField (c₁.chart.openSet ⊓ c₂.chart.openSet)
        (X.presheaf.map (homOfLE (inf_le_right : c₁.chart.openSet ⊓ c₂.chart.openSet ≤
          c₂.chart.openSet)).op c₂.coefficient) =
        X.germToFunctionField c₂.chart.openSet c₂.coefficient :=
      X.presheaf.germ_res_apply _ _ _ c₂.coefficient
    rw [map_mul, e₁, e₂, c₁.germ_eq, c₂.germ_eq, Units.val_mul]

/-- Regular equations are closed under sums of divisors. -/
theorem hasRegularCartierEquations_add (hD₁ : HasRegularCartierEquations X D₁)
    (hD₂ : HasRegularCartierEquations X D₂) : HasRegularCartierEquations X (D₁ + D₂) := by
  intro x
  obtain ⟨c₁, h₁⟩ := hD₁ x
  obtain ⟨c₂, h₂⟩ := hD₂ x
  haveI : Nonempty (c₁.chart.openSet ⊓ c₂.chart.openSet : X.Opens) := ⟨⟨x, h₁, h₂⟩⟩
  exact ⟨c₁.mul c₂, ⟨h₁, h₂⟩⟩

end MulChart

end KltDP.Geometry

namespace KltDP.Geometry.NormalProjectiveSurface.PrimeCurve

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {k : Type u} [Field k] {X : NormalProjectiveSurface k} (C : X.PrimeCurve)
  (D₁ D₂ : CartierDivisor X.toScheme) (hD₁ : HasRegularCartierEquations X.toScheme D₁)
  (hD₂ : HasRegularCartierEquations X.toScheme D₂)

/-- `C ⊄ Supp (D₁ + D₂)` when `C ⊄ Supp D₁` and `C ⊄ Supp D₂`. -/
theorem notInSupport_add (hC₁ : C.NotInSupport D₁ hD₁) (hC₂ : C.NotInSupport D₂ hD₂) :
    C.NotInSupport (D₁ + D₂) (hasRegularCartierEquations_add hD₁ hD₂) := by
  intro hmem
  obtain ⟨c₁, h₁⟩ := hD₁ C.genericPoint
  obtain ⟨c₂, h₂⟩ := hD₂ C.genericPoint
  haveI : Nonempty (c₁.chart.openSet ⊓ c₂.chart.openSet : X.toScheme.Opens) :=
    ⟨⟨C.genericPoint, h₁, h₂⟩⟩
  rw [mem_support_iff_not_isUnit_germ (D₁ + D₂) (hasRegularCartierEquations_add hD₁ hD₂)
    (c₁.mul c₂) C.genericPoint ⟨h₁, h₂⟩] at hmem
  apply hmem
  change IsUnit (X.toScheme.presheaf.germ (c₁.chart.openSet ⊓ c₂.chart.openSet) C.genericPoint
    ⟨h₁, h₂⟩ (X.toScheme.presheaf.map (homOfLE (inf_le_left : c₁.chart.openSet ⊓ c₂.chart.openSet ≤
      c₁.chart.openSet)).op c₁.coefficient *
     X.toScheme.presheaf.map (homOfLE (inf_le_right : c₁.chart.openSet ⊓ c₂.chart.openSet ≤
      c₂.chart.openSet)).op c₂.coefficient))
  rw [map_mul, X.toScheme.presheaf.germ_res_apply, X.toScheme.presheaf.germ_res_apply]
  exact (germ_isUnit_of_not_mem_support D₁ hD₁ c₁ C.genericPoint h₁ hC₁).mul
    (germ_isUnit_of_not_mem_support D₂ hD₂ c₂ C.genericPoint h₂ hC₂)

variable (hC₁ : C.NotInSupport D₁ hD₁) (hC₂ : C.NotInSupport D₂ hD₂)
  (hD₁₂ : HasRegularCartierEquations X.toScheme (D₁ + D₂)) (hC₁₂ : C.NotInSupport (D₁ + D₂) hD₁₂)

/-- The restricted equation of a product chart is the product of the restricted equations. -/
theorem restrictedEquation_mul (c₁ : C.GenericChart D₁) (c₂ : C.GenericChart D₂) :
    letI : Nonempty (c₁.1.chart.openSet ⊓ c₂.1.chart.openSet : X.toScheme.Opens) :=
      ⟨⟨C.genericPoint, c₁.2, c₂.2⟩⟩
    C.restrictedEquation (D₁ + D₂) hD₁₂ (c₁.1.mul c₂.1) ⟨c₁.2, c₂.2⟩ hC₁₂ =
      C.restrictedEquation D₁ hD₁ c₁.1 c₁.2 hC₁ * C.restrictedEquation D₂ hD₂ c₂.1 c₂.2 hC₂ := by
  letI : Nonempty (c₁.1.chart.openSet ⊓ c₂.1.chart.openSet : X.toScheme.Opens) :=
    ⟨⟨C.genericPoint, c₁.2, c₂.2⟩⟩
  letI : Nonempty (C.chartPreimage D₁ c₁.1) :=
    ⟨⟨C.genericLift, C.genericLift_mem_chartPreimage D₁ c₁.1 c₁.2⟩⟩
  letI : Nonempty (C.chartPreimage D₂ c₂.1) :=
    ⟨⟨C.genericLift, C.genericLift_mem_chartPreimage D₂ c₂.1 c₂.2⟩⟩
  letI : Nonempty (C.chartPreimage (D₁ + D₂) (c₁.1.mul c₂.1)) :=
    ⟨⟨C.genericLift, C.genericLift_mem_chartPreimage (D₁ + D₂) (c₁.1.mul c₂.1) ⟨c₁.2, c₂.2⟩⟩⟩
  have hn₁ : C.inclusion.app (c₁.1.chart.openSet ⊓ c₂.1.chart.openSet)
      (X.toScheme.presheaf.map (homOfLE (inf_le_left : c₁.1.chart.openSet ⊓ c₂.1.chart.openSet ≤
        c₁.1.chart.openSet)).op c₁.1.coefficient) =
      C.toScheme.presheaf.map ((Opens.map C.inclusion.base).map
        (homOfLE (inf_le_left : c₁.1.chart.openSet ⊓ c₂.1.chart.openSet ≤ c₁.1.chart.openSet))).op
        (C.inclusion.app c₁.1.chart.openSet c₁.1.coefficient) :=
    ConcreteCategory.congr_hom (C.inclusion.naturality
      (homOfLE (inf_le_left : c₁.1.chart.openSet ⊓ c₂.1.chart.openSet ≤ c₁.1.chart.openSet)).op)
      c₁.1.coefficient
  have hn₂ : C.inclusion.app (c₁.1.chart.openSet ⊓ c₂.1.chart.openSet)
      (X.toScheme.presheaf.map (homOfLE (inf_le_right : c₁.1.chart.openSet ⊓ c₂.1.chart.openSet ≤
        c₂.1.chart.openSet)).op c₂.1.coefficient) =
      C.toScheme.presheaf.map ((Opens.map C.inclusion.base).map
        (homOfLE (inf_le_right : c₁.1.chart.openSet ⊓ c₂.1.chart.openSet ≤ c₂.1.chart.openSet))).op
        (C.inclusion.app c₂.1.chart.openSet c₂.1.coefficient) :=
    ConcreteCategory.congr_hom (C.inclusion.naturality
      (homOfLE (inf_le_right : c₁.1.chart.openSet ⊓ c₂.1.chart.openSet ≤ c₂.1.chart.openSet)).op)
      c₂.1.coefficient
  have hcoef : C.restrictedCoefficient (D₁ + D₂) (c₁.1.mul c₂.1) =
      C.toScheme.presheaf.map ((Opens.map C.inclusion.base).map
        (homOfLE (inf_le_left : c₁.1.chart.openSet ⊓ c₂.1.chart.openSet ≤ c₁.1.chart.openSet))).op
        (C.restrictedCoefficient D₁ c₁.1) *
      C.toScheme.presheaf.map ((Opens.map C.inclusion.base).map
        (homOfLE (inf_le_right : c₁.1.chart.openSet ⊓ c₂.1.chart.openSet ≤ c₂.1.chart.openSet))).op
        (C.restrictedCoefficient D₂ c₂.1) := by
    change C.inclusion.app (c₁.1.chart.openSet ⊓ c₂.1.chart.openSet)
      (X.toScheme.presheaf.map (homOfLE (inf_le_left : c₁.1.chart.openSet ⊓ c₂.1.chart.openSet ≤
        c₁.1.chart.openSet)).op c₁.1.coefficient *
       X.toScheme.presheaf.map (homOfLE (inf_le_right : c₁.1.chart.openSet ⊓ c₂.1.chart.openSet ≤
        c₂.1.chart.openSet)).op c₂.1.coefficient) = _
    rw [map_mul, hn₁, hn₂]
    rfl
  have e₁ : C.toScheme.germToFunctionField (C.chartPreimage (D₁ + D₂) (c₁.1.mul c₂.1))
      (C.toScheme.presheaf.map ((Opens.map C.inclusion.base).map
        (homOfLE (inf_le_left : c₁.1.chart.openSet ⊓ c₂.1.chart.openSet ≤ c₁.1.chart.openSet))).op
        (C.restrictedCoefficient D₁ c₁.1)) =
      C.toScheme.germToFunctionField (C.chartPreimage D₁ c₁.1) (C.restrictedCoefficient D₁ c₁.1) :=
    C.toScheme.presheaf.germ_res_apply _ _ _ (C.restrictedCoefficient D₁ c₁.1)
  have e₂ : C.toScheme.germToFunctionField (C.chartPreimage (D₁ + D₂) (c₁.1.mul c₂.1))
      (C.toScheme.presheaf.map ((Opens.map C.inclusion.base).map
        (homOfLE (inf_le_right : c₁.1.chart.openSet ⊓ c₂.1.chart.openSet ≤ c₂.1.chart.openSet))).op
        (C.restrictedCoefficient D₂ c₂.1)) =
      C.toScheme.germToFunctionField (C.chartPreimage D₂ c₂.1) (C.restrictedCoefficient D₂ c₂.1) :=
    C.toScheme.presheaf.germ_res_apply _ _ _ (C.restrictedCoefficient D₂ c₂.1)
  apply Units.ext
  rw [Units.val_mul]
  change C.toScheme.germToFunctionField (C.chartPreimage (D₁ + D₂) (c₁.1.mul c₂.1))
      (C.restrictedCoefficient (D₁ + D₂) (c₁.1.mul c₂.1)) =
    C.toScheme.germToFunctionField (C.chartPreimage D₁ c₁.1) (C.restrictedCoefficient D₁ c₁.1) *
      C.toScheme.germToFunctionField (C.chartPreimage D₂ c₂.1) (C.restrictedCoefficient D₂ c₂.1)
  rw [hcoef, map_mul, e₁, e₂]

/-- **Additivity of the restriction**: `(D₁ + D₂)|_C = D₁|_C + D₂|_C`. -/
theorem restrictCartier_add :
    C.restrictCartier (D₁ + D₂) hD₁₂ hC₁₂ = C.restrictCartier D₁ hD₁ hC₁ + C.restrictCartier D₂ hD₂ hC₂ := by
  refine (cartierDivisorSheaf C.toScheme).eq_of_locally_eq'
    (fun p : C.GenericChart D₁ × C.GenericChart D₂ =>
      (C.chartPreimage D₁ p.1.1 ⊓ C.chartPreimage D₂ p.2.1 : C.toScheme.Opens)) ⊤
    (fun p => homOfLE (show C.chartPreimage D₁ p.1.1 ⊓ C.chartPreimage D₂ p.2.1 ≤ ⊤ from le_top))
    ?_ _ _ ?_
  · intro y _
    obtain ⟨c₁, h₁⟩ := C.exists_genericChart D₁ hD₁ y
    obtain ⟨c₂, h₂⟩ := C.exists_genericChart D₂ hD₂ y
    exact Opens.mem_iSup.mpr ⟨(c₁, c₂), ⟨h₁, h₂⟩⟩
  · rintro ⟨c₁, c₂⟩
    letI : Nonempty (c₁.1.chart.openSet ⊓ c₂.1.chart.openSet : X.toScheme.Opens) :=
      ⟨⟨C.genericPoint, c₁.2, c₂.2⟩⟩
    letI : Nonempty (C.chartPreimage D₁ c₁.1) :=
      ⟨⟨C.genericLift, C.genericLift_mem_chartPreimage D₁ c₁.1 c₁.2⟩⟩
    letI : Nonempty (C.chartPreimage D₂ c₂.1) :=
      ⟨⟨C.genericLift, C.genericLift_mem_chartPreimage D₂ c₂.1 c₂.2⟩⟩
    letI : Nonempty ((C.chartPreimage D₁ c₁.1 ⊓ C.chartPreimage D₂ c₂.1 : C.toScheme.Opens)) :=
      ⟨⟨C.genericLift, C.genericLift_mem_chartPreimage D₁ c₁.1 c₁.2,
        C.genericLift_mem_chartPreimage D₂ c₂.1 c₂.2⟩⟩
    have hL : (cartierDivisorSheaf C.toScheme).val.map
        (homOfLE (show C.chartPreimage D₁ c₁.1 ⊓ C.chartPreimage D₂ c₂.1 ≤ ⊤ from le_top)).op
        (C.restrictCartier (D₁ + D₂) hD₁₂ hC₁₂) =
        cartierEquationClassHom C.toScheme (C.chartPreimage D₁ c₁.1 ⊓ C.chartPreimage D₂ c₂.1)
          (Additive.ofMul (C.restrictedEquation D₁ hD₁ c₁.1 c₁.2 hC₁ *
            C.restrictedEquation D₂ hD₂ c₂.1 c₂.2 hC₂)) := by
      have hs := C.restrictCartier_spec (D₁ + D₂) hD₁₂ hC₁₂ ⟨c₁.1.mul c₂.1, ⟨c₁.2, c₂.2⟩⟩
      rw [C.restrictedEquation_mul D₁ D₂ hD₁ hD₂ hC₁ hC₂ hD₁₂ hC₁₂ c₁ c₂] at hs
      exact hs
    have hcomp₁ : (homOfLE (show C.chartPreimage D₁ c₁.1 ≤ ⊤ from le_top)).op ≫
        (homOfLE (inf_le_left : C.chartPreimage D₁ c₁.1 ⊓ C.chartPreimage D₂ c₂.1 ≤
          C.chartPreimage D₁ c₁.1)).op =
        (homOfLE (show C.chartPreimage D₁ c₁.1 ⊓ C.chartPreimage D₂ c₂.1 ≤ ⊤ from le_top)).op :=
      Subsingleton.elim _ _
    have hcomp₂ : (homOfLE (show C.chartPreimage D₂ c₂.1 ≤ ⊤ from le_top)).op ≫
        (homOfLE (inf_le_right : C.chartPreimage D₁ c₁.1 ⊓ C.chartPreimage D₂ c₂.1 ≤
          C.chartPreimage D₂ c₂.1)).op =
        (homOfLE (show C.chartPreimage D₁ c₁.1 ⊓ C.chartPreimage D₂ c₂.1 ≤ ⊤ from le_top)).op :=
      Subsingleton.elim _ _
    have h₁ : (cartierDivisorSheaf C.toScheme).val.map
        (homOfLE (show C.chartPreimage D₁ c₁.1 ⊓ C.chartPreimage D₂ c₂.1 ≤ ⊤ from le_top)).op
        (C.restrictCartier D₁ hD₁ hC₁) =
        cartierEquationClassHom C.toScheme (C.chartPreimage D₁ c₁.1 ⊓ C.chartPreimage D₂ c₂.1)
          (Additive.ofMul (C.restrictedEquation D₁ hD₁ c₁.1 c₁.2 hC₁)) := by
      rw [← hcomp₁, (cartierDivisorSheaf C.toScheme).val.map_comp]
      change (cartierDivisorSheaf C.toScheme).val.map
        (homOfLE (inf_le_left : C.chartPreimage D₁ c₁.1 ⊓ C.chartPreimage D₂ c₂.1 ≤
          C.chartPreimage D₁ c₁.1)).op
        ((cartierDivisorSheaf C.toScheme).val.map
          (homOfLE (show C.chartPreimage D₁ c₁.1 ≤ ⊤ from le_top)).op
          (C.restrictCartier D₁ hD₁ hC₁)) = _
      rw [C.restrictCartier_spec D₁ hD₁ hC₁ c₁, cartierEquationClassHom_restrict]
    have h₂ : (cartierDivisorSheaf C.toScheme).val.map
        (homOfLE (show C.chartPreimage D₁ c₁.1 ⊓ C.chartPreimage D₂ c₂.1 ≤ ⊤ from le_top)).op
        (C.restrictCartier D₂ hD₂ hC₂) =
        cartierEquationClassHom C.toScheme (C.chartPreimage D₁ c₁.1 ⊓ C.chartPreimage D₂ c₂.1)
          (Additive.ofMul (C.restrictedEquation D₂ hD₂ c₂.1 c₂.2 hC₂)) := by
      rw [← hcomp₂, (cartierDivisorSheaf C.toScheme).val.map_comp]
      change (cartierDivisorSheaf C.toScheme).val.map
        (homOfLE (inf_le_right : C.chartPreimage D₁ c₁.1 ⊓ C.chartPreimage D₂ c₂.1 ≤
          C.chartPreimage D₂ c₂.1)).op
        ((cartierDivisorSheaf C.toScheme).val.map
          (homOfLE (show C.chartPreimage D₂ c₂.1 ≤ ⊤ from le_top)).op
          (C.restrictCartier D₂ hD₂ hC₂)) = _
      rw [C.restrictCartier_spec D₂ hD₂ hC₂ c₂, cartierEquationClassHom_restrict]
    rw [hL, ofMul_mul, map_add, ← h₁, ← h₂]
    exact (map_add ((cartierDivisorSheaf C.toScheme).val.map
      (homOfLE (show C.chartPreimage D₁ c₁.1 ⊓ C.chartPreimage D₂ c₂.1 ≤ ⊤ from le_top)).op).hom
      (C.restrictCartier D₁ hD₁ hC₁) (C.restrictCartier D₂ hD₂ hC₂)).symm

/-- **Additivity of the intersection number**: `C·(D₁ + D₂) = C·D₁ + C·D₂` (admitted 0AYX). -/
theorem intersectionDegree_add :
    C.intersectionDegree (D₁ + D₂) hD₁₂ hC₁₂ =
      C.intersectionDegree D₁ hD₁ hC₁ + C.intersectionDegree D₂ hD₂ hC₂ := by
  have h12 := C.lineDegree_restrictCartier_eq_intersectionDegree (D₁ + D₂) hD₁₂ hC₁₂
  have h1 := C.lineDegree_restrictCartier_eq_intersectionDegree D₁ hD₁ hC₁
  have h2 := C.lineDegree_restrictCartier_eq_intersectionDegree D₂ hD₂ hC₂
  rw [C.restrictCartier_add D₁ D₂ hD₁ hD₂ hC₁ hC₂ hD₁₂ hC₁₂] at h12
  have hadd := KltDP.AdmissionProbe.CurveTensorDegreeConsumers.lineDegree_eq_add_of_tensorIso C
    (cartierDivisorInvertibleSheaf C.toScheme (C.restrictCartier D₁ hD₁ hC₁))
    (cartierDivisorInvertibleSheaf C.toScheme (C.restrictCartier D₂ hD₂ hC₂))
    (cartierDivisorInvertibleSheaf C.toScheme
      (C.restrictCartier D₁ hD₁ hC₁ + C.restrictCartier D₂ hD₂ hC₂))
    (cartierTensorIso C.toScheme (C.restrictCartier D₁ hD₁ hC₁) (C.restrictCartier D₂ hD₂ hC₂)).symm
  have hZ : (C.intersectionDegree (D₁ + D₂) hD₁₂ hC₁₂ : ℤ) =
      (C.intersectionDegree D₁ hD₁ hC₁ : ℤ) + (C.intersectionDegree D₂ hD₂ hC₂ : ℤ) := by
    rw [← h12, hadd, h1, h2]
  exact_mod_cast hZ

/-- Nonnegativity of the intersection number (it is a `k`-dimension). -/
theorem intersectionDegree_nonneg (D : CartierDivisor X.toScheme)
    (hD : HasRegularCartierEquations X.toScheme D) (hC : C.NotInSupport D hD) :
    (0 : ℤ) ≤ (C.intersectionDegree D hD hC : ℤ) :=
  Nat.cast_nonneg _

end KltDP.Geometry.NormalProjectiveSurface.PrimeCurve
