import KltDP.Geometry.ReesChartUnitRescaling

/-!
# The original chart at an explicitly unit-scaled generator

This specializes the actual unit-multiple chart equivalence to the literal
element `u*a` of the original ideal. No generator-comparison premise remains.
-/

noncomputable section

namespace KltDP.Geometry.AffineBlowup

variable {R : Type*} [CommRing R]

/-- The literal unit multiple in the original ideal. -/
def unitScaledElement (I : Ideal R) (a : I) (u : Rˣ) : I :=
  ⟨(u : R) * (a : R), I.mul_mem_left _ a.property⟩

@[simp] theorem unitScaledElement_coe (I : Ideal R) (a : I) (u : Rˣ) :
    (unitScaledElement I a u : R) = (u : R) * (a : R) := rfl

/-- The canonical original-chart equivalence for `a` and the literal `u*a`. -/
def chartUnitEquiv (I : Ideal R) (a : I) (u : Rˣ) :
    chartRing I a ≃+* chartRing I (unitScaledElement I a u) :=
  chartUnitMultipleEquiv I a (unitScaledElement I a u) u rfl

@[simp] theorem chartUnitEquiv_baseMap (I : Ideal R) (a : I) (u : Rˣ) (r : R) :
    chartUnitEquiv I a u (chartBaseMap I a r) =
      chartBaseMap I (unitScaledElement I a u) r :=
  chartUnitMultipleEquiv_baseMap I a (unitScaledElement I a u) u rfl r

theorem chartUnitEquiv_comp_baseMap (I : Ideal R) (a : I) (u : Rˣ) :
    (chartUnitEquiv I a u).toRingHom.comp (chartBaseMap I a) =
      chartBaseMap I (unitScaledElement I a u) := by
  apply RingHom.ext
  intro r
  exact chartUnitEquiv_baseMap I a u r

@[simp] theorem chartUnitEquiv_symm_baseMap (I : Ideal R) (a : I) (u : Rˣ) (r : R) :
    (chartUnitEquiv I a u).symm (chartBaseMap I (unitScaledElement I a u) r) =
      chartBaseMap I a r :=
  chartUnitMultipleEquiv_symm_baseMap I a (unitScaledElement I a u) u rfl r

theorem chartUnitEquiv_fraction (I : Ideal R) (a : I) (u : Rˣ) (b : I) :
    chartUnitEquiv I a u (chartFraction I a b) =
      chartBaseMap I (unitScaledElement I a u) (u : R) *
        chartFraction I (unitScaledElement I a u) b :=
  chartUnitMultipleEquiv_fraction I a (unitScaledElement I a u) u rfl b

theorem chartUnitEquiv_symm_fraction (I : Ideal R) (a : I) (u : Rˣ) (b : I) :
    (chartUnitEquiv I a u).symm (chartFraction I (unitScaledElement I a u) b) =
      chartBaseMap I a (↑u⁻¹ : R) * chartFraction I a b :=
  chartUnitMultipleEquiv_symm_fraction I a (unitScaledElement I a u) u rfl b

end KltDP.Geometry.AffineBlowup

#check @KltDP.Geometry.AffineBlowup.chartUnitEquiv
#check @KltDP.Geometry.AffineBlowup.chartUnitEquiv_symm_fraction
#print axioms KltDP.Geometry.AffineBlowup.chartUnitEquiv
#print axioms KltDP.Geometry.AffineBlowup.chartUnitEquiv_symm_fraction
