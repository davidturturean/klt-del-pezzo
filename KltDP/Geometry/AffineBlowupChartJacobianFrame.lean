import KltDP.Geometry.AffineBlowupChartJacobian
import KltDP.Geometry.AffineTopDifferentialFrame

/-!
# Reading the original Rees-chart Jacobian in a native coordinate frame

The only coordinate hypothesis is an actual basis of the chart's original
Kähler module whose two vectors are the differentials of the actual exceptional
equation and the actual chart fraction. Its determinant frame reads the
original exterior differential as that exceptional equation. In particular,
the factor calculation is nonzero on any nonempty affine chart.

Constructing these two basis vectors from smooth-point étale coordinates and
gluing the intrinsic differential factorizations are separate obligations.
-/

noncomputable section

namespace KltDP.Geometry.AffineBlowupChartJacobian

open AffineBlowup AffineTopDifferentialFrame
open KltDP.Examples.FrobeniusBlowupDifferential

universe u v

variable (k : Type u) [CommRing k]
variable {R : Type v} [CommRing R] (I : Ideal R) (a b : I)
variable [groundAlgebra : Algebra k (chartRing I a)]
variable (β : Basis (Fin 2) (chartRing I a) (KaehlerDifferential k (chartRing I a)))
variable (h0 : β 0 =
  KaehlerDifferential.D k (chartRing I a) (chartBaseMap I a (a : R)))
variable (h1 : β 1 =
  KaehlerDifferential.D k (chartRing I a) (chartFraction I a b))

include h0 h1 in
/-- The displayed native coordinate wedge is the wedge of the actual basis. -/
theorem chartCoordinateTopForm_eq_basis_wedge :
    chartCoordinateTopForm k I a b = exteriorPower.ιMulti (chartRing I a) 2 β := by
  change exteriorPower.ιMulti (chartRing I a) 2 ![_, _] = _
  apply congrArg (exteriorPower.ιMulti (chartRing I a) 2)
  funext i
  fin_cases i
  · exact h0.symm
  · exact h1.symm

include h0 h1 in
/-- The actual determinant frame sends the native coordinate wedge to one. -/
theorem determinantEquiv_chartCoordinateTopForm :
    determinantEquiv β (chartCoordinateTopForm k I a b) = 1 := by
  rw [chartCoordinateTopForm_eq_basis_wedge k I a b β h0 h1,
    determinantEquiv_basis_wedge]

variable [baseAlgebra : Algebra k R]
variable [hTower : @IsScalarTower k R (chartRing I a)
  baseAlgebra.toSMul (originalChartAlgebra I a).toSMul groundAlgebra.toSMul]

include h0 h1 hTower in
/-- The coefficient of the original exterior differential is the original
exceptional equation, in the actual coordinate determinant frame. -/
theorem determinantEquiv_topDifferentialMap_coordinate :
    determinantEquiv β (topDifferentialMap k I a (sourceCoordinateTopForm k I a b)) =
      chartBaseMap I a (a : R) := by
  rw [topDifferentialMap_coordinate,
    LinearEquiv.map_smul (determinantEquiv β)
      (chartBaseMap I a (a : R)) (chartCoordinateTopForm k I a b),
    determinantEquiv_chartCoordinateTopForm k I a b β h0 h1, smul_eq_mul, mul_one]

include h0 h1 hTower in
/-- On a nontrivial chart the actual differential image is nonzero, because
the original exceptional equation is a nonzerodivisor. -/
theorem topDifferentialMap_coordinate_ne_zero [Nontrivial (chartRing I a)] :
    topDifferentialMap k I a (sourceCoordinateTopForm k I a b) ≠ 0 := by
  intro h
  have he := determinantEquiv_topDifferentialMap_coordinate k I a b β h0 h1
  rw [h, LinearEquiv.map_zero (determinantEquiv β)] at he
  exact nonZeroDivisors.ne_zero
    (chartBaseMap_equation_mem_nonZeroDivisors I a) he.symm

end KltDP.Geometry.AffineBlowupChartJacobian
