import KltDP.Geometry.EffectiveCartierZero
import KltDP.Geometry.PrimeCurveIntersectionAdditive

/-!
# Original equations for finite sums of actual effective Cartier divisors

The existing product chart gives an equation of a sum on the actual common
open. Its germ is the product of the two original germs. Finite induction
therefore constructs an actual chart of the finite sum with precisely the
finite product germ, without any equation or ideal comparison premise.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u v

namespace KltDP.Geometry

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable (X : Scheme.{u}) [IsIntegral X]

/-- The existing product equation chart has the product of the original germs. -/
theorem RegularCartierEquationChart.mul_germ
    {D E : CartierDivisor X} (c : RegularCartierEquationChart X D)
    (d : RegularCartierEquationChart X E)
    [Nonempty (c.chart.openSet ⊓ d.chart.openSet : X.Opens)]
    (x : X) (hc : x ∈ c.chart.openSet) (hd : x ∈ d.chart.openSet) :
    X.presheaf.germ (c.mul d).chart.openSet x ⟨hc, hd⟩ (c.mul d).coefficient =
      X.presheaf.germ c.chart.openSet x hc c.coefficient *
        X.presheaf.germ d.chart.openSet x hd d.coefficient := by
  change X.presheaf.germ (c.chart.openSet ⊓ d.chart.openSet) x ⟨hc, hd⟩
    (X.presheaf.map (homOfLE inf_le_left).op c.coefficient *
      X.presheaf.map (homOfLE inf_le_right).op d.coefficient) = _
  rw [map_mul, X.presheaf.germ_res_apply, X.presheaf.germ_res_apply]

/-- At each original point, the finite sum has a genuine regular equation
whose actual stalk germ is the product of the chosen original germs. -/
theorem exists_finset_sum_cartier_chart_germ
    {I : Type v} (D : I → CartierDivisor X)
    (c : ∀ i, RegularCartierEquationChart X (D i))
    (x : X) (hx : ∀ i, x ∈ (c i).chart.openSet) (s : Finset I) :
    ∃ (a : RegularCartierEquationChart X (∑ i ∈ s, D i))
      (ha : x ∈ a.chart.openSet),
      X.presheaf.germ a.chart.openSet x ha a.coefficient =
        ∏ i ∈ s, X.presheaf.germ (c i).chart.openSet x (hx i) (c i).coefficient := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty, Finset.prod_empty]
      refine ⟨zeroCartierChart X, Set.mem_univ x, ?_⟩
      change X.presheaf.germ ⊤ x trivial 1 = 1
      exact map_one _
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi]
      obtain ⟨a, ha, hg⟩ := ih
      letI : Nonempty ((c i).chart.openSet ⊓ a.chart.openSet : X.Opens) :=
        ⟨⟨x, hx i, ha⟩⟩
      refine ⟨(c i).mul a, ⟨hx i, ha⟩, ?_⟩
      rw [RegularCartierEquationChart.mul_germ, hg]

end KltDP.Geometry

#print axioms KltDP.Geometry.exists_finset_sum_cartier_chart_germ
