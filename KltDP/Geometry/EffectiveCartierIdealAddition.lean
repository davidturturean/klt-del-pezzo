import KltDP.Geometry.StrictNormalCrossingsCartierIdealData
import KltDP.Geometry.CartierDivisorPullbackAdd

/-!
# The actual ideal of the sum of effective Cartier divisors

On every original affine open the existing ideal of D + E is the product
of the two original ideals. The proof uses the original germ maps: on a
common equation neighborhood the coefficient of D + E is the product of
the two original restricted coefficients. Pinned affine ideal extensionality
then gives equality on the arbitrary original affine open.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
universe u
namespace KltDP.Geometry
attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (X : Scheme.{u}) [IsIntegral X]

/-- Addition of actual effective Cartier divisors multiplies their actual
ideals on every original affine open. The sum's regular equations are derived. -/
theorem effectiveCartierIdealDataOfRegularEquations_add_ideal
    (D E : CartierDivisor X) (hD : HasRegularCartierEquations X D)
    (hE : HasRegularCartierEquations X E) (U : X.affineOpens) :
    (effectiveCartierIdealDataOfRegularEquations X (D + E)
      (CartierDivisorPullbackAdd.hasRegularCartierEquations_add D E hD hE)).ideal U =
    (effectiveCartierIdealDataOfRegularEquations X D hD).ideal U *
      (effectiveCartierIdealDataOfRegularEquations X E hE).ideal U := by
  rw [U.2.ideal_ext_iff]
  intro x hxU
  obtain ⟨c, hxc⟩ := hD x
  obtain ⟨d, hxd⟩ := hE x
  let e := CartierDivisorPullbackAdd.regularChartMul D E c d
  have hxe : x ∈ e.chart.openSet := ⟨hxc, hxd⟩
  rw [Ideal.map_mul,
    regularCartierIdealData_map_germ_eq_span X (D + E)
      (CartierDivisorPullbackAdd.hasRegularCartierEquations_add D E hD hE) e U x hxU hxe,
    regularCartierIdealData_map_germ_eq_span X D hD c U x hxU hxc,
    regularCartierIdealData_map_germ_eq_span X E hE d U x hxU hxd,
    Ideal.span_singleton_mul_span_singleton]
  change Ideal.span ({X.presheaf.germ (c.chart.openSet ⊓ d.chart.openSet) x
    ⟨hxc, hxd⟩
    (X.presheaf.map (homOfLE inf_le_left).op c.coefficient *
      X.presheaf.map (homOfLE inf_le_right).op d.coefficient)} :
    Set (X.presheaf.stalk x)) = _
  rw [map_mul, X.presheaf.germ_res_apply, X.presheaf.germ_res_apply]

/-- The same equality as literal families of original affine ideals; no
new multiplication structure on ideal-sheaf data is introduced. -/
theorem effectiveCartierIdealDataOfRegularEquations_add_ideal_family
    (D E : CartierDivisor X) (hD : HasRegularCartierEquations X D)
    (hE : HasRegularCartierEquations X E) :
    (effectiveCartierIdealDataOfRegularEquations X (D + E)
      (CartierDivisorPullbackAdd.hasRegularCartierEquations_add D E hD hE)).ideal =
    fun U => (effectiveCartierIdealDataOfRegularEquations X D hD).ideal U *
      (effectiveCartierIdealDataOfRegularEquations X E hE).ideal U := by
  funext U
  exact effectiveCartierIdealDataOfRegularEquations_add_ideal X D E hD hE U

end KltDP.Geometry

#print axioms KltDP.Geometry.effectiveCartierIdealDataOfRegularEquations_add_ideal
