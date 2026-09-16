import KltDP.Examples.FrobeniusBlowupChartIteration
import KltDP.Examples.FrobeniusBlowupSmooth
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.LinearAlgebra.ExteriorPower.Pairing

/-!
# The actual differential factor on a plane point-blowup chart

The original selected Rees-chart projection has coordinate map
`u ↦ u`, `v ↦ u*v`, as proved by `coordinateBlowdown_eq`. In the actual
exterior square of the chart's Kähler differential module, differentiating
these two coordinate functions gives `u • (du ∧ dv)`.

The form `du ∧ dv` is nonzero: the two original coordinate derivations,
lifted through the universal Kähler map, pair with it to give one. Thus
the factor calculation is not an equality of zero forms. All arguments
work in every characteristic. This file does not construct a global
canonical divisor or claim a global divisor/intersection formula.

Reuse: pinned derivation Leibniz, transport through an actual algebra
equivalence, and the determinant pairing on actual exterior powers.
No new library proof port or literature axiom is required.
-/

noncomputable section

namespace KltDP.Examples.FrobeniusBlowupDifferential

open FrobeniusBlowupContact FrobeniusBlowupSmooth

universe u v

section Wedge

variable {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]

/-- The original alternating exterior product of two vectors. -/
def wedgeTwo (x y : M) : ⋀[A]^2 M := exteriorPower.ιMulti A 2 ![x, y]

theorem wedgeTwo_self (x : M) : wedgeTwo (A := A) x x = 0 :=
  (exteriorPower.ιMulti A 2).map_eq_zero_of_eq ![x, x]
    (i := (0 : Fin 2)) (j := (1 : Fin 2)) rfl (by decide)

/-- Alternation removes the repeated differential from the Leibniz rule. -/
theorem wedgeTwo_derivation_mul {k : Type*} [CommRing k] [Algebra k A]
    [Module k M] (D : Derivation k A M) (a b : A) :
    wedgeTwo (A := A) (D a) (D (a * b)) =
      a • wedgeTwo (A := A) (D a) (D b) := by
  let B := (exteriorPower.ιMulti A 2).curryLeft (D a)
  change B ![D (a * b)] = _
  rw [D.leibniz, B.map_vecCons_add, B.map_vecCons_smul, B.map_vecCons_smul]
  change a • wedgeTwo (A := A) (D a) (D b) +
    b • wedgeTwo (A := A) (D a) (D a) = _
  rw [wedgeTwo_self, smul_zero, add_zero]

end Wedge

variable {k : Type u} [Field k]

/-- The actual Kähler module of the original polynomial chart over its field. -/
abbrev PlaneDifferential (k : Type u) [Field k] :=
  KaehlerDifferential k (planeRing k)

/-- The original outer-variable polynomial derivation, restricted to k. -/
def partialV : Derivation k (planeRing k) (planeRing k) :=
  (Polynomial.derivative' : Derivation (Polynomial k) (planeRing k) (planeRing k)).restrictScalars k

@[simp] theorem partialV_u : partialV (uCoord (k := k)) = 0 := by
  change Polynomial.derivative (Polynomial.C Polynomial.X) = 0
  exact Polynomial.derivative_C

@[simp] theorem partialV_v : partialV (vCoord (k := k)) = 1 := by
  change Polynomial.derivative (Polynomial.X : planeRing k) = 1
  exact Polynomial.derivative_X

private theorem partialV_swap_kernel (x : planeRing k)
    (hx : coordinateSwap x = 0) : coordinateSwap (partialV x) = 0 := by
  have hzero : x = 0 :=
    (coordinateSwap (k := k)).injective (hx.trans (map_zero coordinateSwap).symm)
  simp only [hzero, map_zero]

/-- The inner-variable derivation is transported through the existing
actual coordinate-swap algebra equivalence. -/
def partialU : Derivation k (planeRing k) (planeRing k) :=
  Derivation.liftOfRightInverse
    (f := (coordinateSwap (k := k)).toAlgHom)
    (f_inv := (coordinateSwap (k := k)).symm)
    (coordinateSwap (k := k)).apply_symm_apply
    (d := partialV) partialV_swap_kernel

theorem partialU_swap (x : planeRing k) :
    partialU (coordinateSwap x) = coordinateSwap (partialV x) :=
  Derivation.liftOfRightInverse_apply
    (f := (coordinateSwap (k := k)).toAlgHom)
    (f_inv := (coordinateSwap (k := k)).symm)
    (coordinateSwap (k := k)).apply_symm_apply
    (d := partialV) partialV_swap_kernel x

@[simp] theorem partialU_u : partialU (uCoord (k := k)) = 1 := by
  simpa only [coordinateSwap_v, partialV_v, map_one] using
    partialU_swap (vCoord (k := k))

@[simp] theorem partialU_v : partialU (vCoord (k := k)) = 0 := by
  simpa only [coordinateSwap_u, partialV_u, map_zero] using
    partialU_swap (uCoord (k := k))

/-- The coordinate form in the actual exterior square, with the order u,v. -/
def coordinateTopForm : ⋀[planeRing k]^2 (PlaneDifferential k) :=
  wedgeTwo (A := planeRing k)
    (KaehlerDifferential.D k (planeRing k) uCoord)
    (KaehlerDifferential.D k (planeRing k) vCoord)

/-- Evaluate an actual exterior two-form against the two actual partial
derivations using the pinned exterior-power determinant pairing. -/
def coordinateTopFormEvaluator :
    (⋀[planeRing k]^2 (PlaneDifferential k)) →ₗ[planeRing k] planeRing k :=
  exteriorPower.alternatingMapToDual (planeRing k) (PlaneDifferential k) 2
    ![partialU.liftKaehlerDifferential, partialV.liftKaehlerDifferential]

theorem coordinateTopFormEvaluator_coordinateTopForm :
    coordinateTopFormEvaluator (coordinateTopForm (k := k)) = 1 := by
  simp [coordinateTopFormEvaluator, coordinateTopForm, wedgeTwo,
    exteriorPower.alternatingMapToDual_apply_ιMulti, Matrix.det_fin_two]

/-- The original coordinate two-form is nonzero, including in characteristic two. -/
theorem coordinateTopForm_ne_zero : coordinateTopForm (k := k) ≠ 0 := by
  intro h
  have he := coordinateTopFormEvaluator_coordinateTopForm (k := k)
  rw [h, map_zero] at he
  exact zero_ne_one he

/-- Differentiate the images of the two coordinates under the actual
chart blowdown ring map. No new pullback functor is defined here. -/
def pulledCoordinateTopForm : ⋀[planeRing k]^2 (PlaneDifferential k) :=
  wedgeTwo (A := planeRing k)
    (KaehlerDifferential.D k (planeRing k) (chartSubstitution uCoord))
    (KaehlerDifferential.D k (planeRing k) (chartSubstitution vCoord))

/-- The selected actual Rees-chart projection has the exceptional differential factor u. -/
theorem pulledCoordinateTopForm_eq :
    pulledCoordinateTopForm (k := k) = uCoord (k := k) • coordinateTopForm (k := k) := by
  unfold pulledCoordinateTopForm coordinateTopForm
  rw [chartSubstitution_u, chartSubstitution_v]
  exact wedgeTwo_derivation_mul (KaehlerDifferential.D k (planeRing k)) uCoord vCoord

/-- The determinant pairing reads exactly the original exceptional coordinate. -/
theorem coordinateTopFormEvaluator_pulledCoordinateTopForm :
    coordinateTopFormEvaluator (pulledCoordinateTopForm (k := k)) = uCoord := by
  rw [pulledCoordinateTopForm_eq, map_smul,
    coordinateTopFormEvaluator_coordinateTopForm, smul_eq_mul, mul_one]

theorem pulledCoordinateTopForm_ne_zero : pulledCoordinateTopForm (k := k) ≠ 0 := by
  intro h
  have he := coordinateTopFormEvaluator_pulledCoordinateTopForm (k := k)
  rw [h, map_zero] at he
  exact uCoord_ne_zero he.symm

end KltDP.Examples.FrobeniusBlowupDifferential
