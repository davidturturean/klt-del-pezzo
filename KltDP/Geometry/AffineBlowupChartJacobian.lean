import KltDP.Geometry.AffineBlowupChartCenter
import KltDP.Examples.FrobeniusBlowupDifferential

/-!
# The native Jacobian on an original Rees chart

The chart is the original homogeneous localization `AffineBlowup.chartRing I a`.
Its algebra over the original ring is the existing `chartAlgebra I a`; the
ground-ring algebra is any compatible scalar tower, in particular the original
composite ground-ring map. No polynomial-chart isomorphism is assumed.

For actual elements `a, b` of the center ideal, the existing relation
`chartBaseMap a * chartFraction a b = chartBaseMap b` gives the native exterior
differential factor. The induced map is exactly `exteriorPower.map` of the
pinned scalar-extended Kähler differential map. The factor is the original
regular equation of the pulled-back center, even over a general commutative
base. This identity alone does not assert that the displayed wedges are frames.
-/

noncomputable section

open scoped TensorProduct

namespace KltDP.Geometry.AffineBlowupChartJacobian

open AffineBlowup KltDP.Examples.FrobeniusBlowupDifferential

universe u v w

private theorem map_wedgeTwo
    {A : Type u} [CommRing A]
    {M : Type v} [AddCommGroup M] [Module A M]
    {N : Type w} [AddCommGroup N] [Module A N]
    (f : M →ₗ[A] N) (x y : M) :
    exteriorPower.map 2 f (wedgeTwo (A := A) x y) =
      wedgeTwo (A := A) (f x) (f y) := by
  change exteriorPower.map 2 f (exteriorPower.ιMulti A 2 ![x, y]) = _
  rw [exteriorPower.map_apply_ιMulti]
  apply congrArg (exteriorPower.ιMulti A 2)
  funext i
  fin_cases i <;> rfl

private theorem map_wedgeTwo_of_eq
    {A : Type u} [CommRing A]
    {M : Type v} [AddCommGroup M] [Module A M]
    {N : Type w} [AddCommGroup N] [Module A N]
    (f : M →ₗ[A] N) (x y : M) (z t : N) (hx : f x = z) (hy : f y = t) :
    exteriorPower.map 2 f (wedgeTwo (A := A) x y) = wedgeTwo (A := A) z t := by
  rw [map_wedgeTwo, hx, hy]

private def scalarExtendedDifferential (k A B : Type*)
    [CommRing k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra A B] [Algebra k B] [IsScalarTower k A B] :
    B ⊗[A] KaehlerDifferential k A →ₗ[B] KaehlerDifferential k B :=
  KaehlerDifferential.mapBaseChange k A B

private theorem scalarExtendedDifferential_one_tmul_D (k A B : Type*)
    [CommRing k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra A B] [Algebra k B] [IsScalarTower k A B] (r : A) :
    scalarExtendedDifferential k A B (1 ⊗ₜ[A] KaehlerDifferential.D k A r) =
      KaehlerDifferential.D k B (algebraMap A B r) := by
  rw [scalarExtendedDifferential, KaehlerDifferential.mapBaseChange_tmul,
    KaehlerDifferential.map_D, one_smul]

variable (k : Type u) [CommRing k]
variable {R : Type v} [CommRing R] (I : Ideal R) (a : I)
variable [groundAlgebra : Algebra k (chartRing I a)]

/-- The native wedge identity uses the actual homogeneous chart fraction. -/
theorem native_wedge_factor (b : I) :
    wedgeTwo (A := chartRing I a)
        (KaehlerDifferential.D k (chartRing I a) (chartBaseMap I a (a : R)))
        (KaehlerDifferential.D k (chartRing I a) (chartBaseMap I a (b : R))) =
      chartBaseMap I a (a : R) •
        wedgeTwo (A := chartRing I a)
          (KaehlerDifferential.D k (chartRing I a) (chartBaseMap I a (a : R)))
          (KaehlerDifferential.D k (chartRing I a) (chartFraction I a b)) := by
  rw [← chartBaseMap_mul_chartFraction I a b]
  exact wedgeTwo_derivation_mul (KaehlerDifferential.D k (chartRing I a))
    (chartBaseMap I a (a : R)) (chartFraction I a b)

local instance originalChartAlgebra : Algebra R (chartRing I a) := chartAlgebra I a

variable [baseAlgebra : Algebra k R]
variable [hTower : @IsScalarTower k R (chartRing I a)
  baseAlgebra.toSMul (originalChartAlgebra I a).toSMul groundAlgebra.toSMul]

include hTower in
/-- Scalar extension along the original Rees-chart structure ring map. -/
def differentialMap :
    chartRing I a ⊗[R] KaehlerDifferential k R →ₗ[chartRing I a]
      KaehlerDifferential k (chartRing I a) :=
  @scalarExtendedDifferential k R (chartRing I a) _ _ _
    baseAlgebra (originalChartAlgebra I a) groundAlgebra hTower

include hTower in
theorem differentialMap_one_tmul_D (r : R) :
    differentialMap k I a (1 ⊗ₜ[R] KaehlerDifferential.D k R r) =
      KaehlerDifferential.D k (chartRing I a) (chartBaseMap I a r) :=
  @scalarExtendedDifferential_one_tmul_D k R (chartRing I a) _ _ _
    baseAlgebra (originalChartAlgebra I a) groundAlgebra hTower r

include hTower in
/-- The actual exterior square of the original differential map. -/
def topDifferentialMap :
    (⋀[chartRing I a]^2 (chartRing I a ⊗[R] KaehlerDifferential k R)) →ₗ[chartRing I a]
      (⋀[chartRing I a]^2 (KaehlerDifferential k (chartRing I a))) :=
  exteriorPower.map 2 (differentialMap k I a)

/-- The source parameter wedge after actual scalar extension. -/
def sourceCoordinateTopForm (b : I) :
    ⋀[chartRing I a]^2 (chartRing I a ⊗[R] KaehlerDifferential k R) :=
  wedgeTwo (1 ⊗ₜ[R] KaehlerDifferential.D k R (a : R))
    (1 ⊗ₜ[R] KaehlerDifferential.D k R (b : R))

/-- The ordered parameter/fraction wedge in the actual chart Kähler module. -/
def chartCoordinateTopForm (b : I) :
    ⋀[chartRing I a]^2 (KaehlerDifferential k (chartRing I a)) :=
  wedgeTwo
    (KaehlerDifferential.D k (chartRing I a) (chartBaseMap I a (a : R)))
    (KaehlerDifferential.D k (chartRing I a) (chartFraction I a b))

include hTower in
/-- The original exterior differential has the original exceptional factor. -/
theorem topDifferentialMap_coordinate (b : I) :
    topDifferentialMap k I a (sourceCoordinateTopForm k I a b) =
      chartBaseMap I a (a : R) • chartCoordinateTopForm k I a b := by
  exact (map_wedgeTwo_of_eq (differentialMap k I a)
    (1 ⊗ₜ[R] KaehlerDifferential.D k R (a : R))
    (1 ⊗ₜ[R] KaehlerDifferential.D k R (b : R)) _ _
    (differentialMap_one_tmul_D k I a (a : R))
    (differentialMap_one_tmul_D k I a (b : R))).trans
      (native_wedge_factor k I a b)

end KltDP.Geometry.AffineBlowupChartJacobian
