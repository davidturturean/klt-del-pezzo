import KltDP.Geometry.StrictNormalCrossings
import KltDP.Geometry.CartierSectionIdeal

/-!
# Strict normal crossings from one original equation at each point

Two regular charts of the same original Cartier divisor generate its
original ideal on their overlap. Their germs are therefore associated.
The existing unit-invariance of the SNC equation predicate transports a
single SNC equation through each point to every original equation chart.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
universe u
namespace KltDP.Geometry
attribute [local instance] Types.instFunLike Types.instConcreteCategory

namespace IsStrictNormalCrossingsEquation

/-- Association changes an actual local equation only by a unit. -/
theorem of_associated {R : Type u} [CommRing R] [IsLocalRing R] {f g : R}
    (hf : IsStrictNormalCrossingsEquation R f) (hfg : Associated f g) :
    IsStrictNormalCrossingsEquation R g := by
  obtain ⟨v, rfl⟩ := hfg
  simpa only [mul_comm] using hf.unit_mul v

/-- Equal principal ideals in a domain have the same SNC generators. -/
theorem of_span_eq {R : Type u} [CommRing R] [IsLocalRing R] [IsDomain R]
    {f g : R} (hf : IsStrictNormalCrossingsEquation R f)
    (hfg : Ideal.span ({f} : Set R) = Ideal.span ({g} : Set R)) :
    IsStrictNormalCrossingsEquation R g :=
  hf.of_associated (Ideal.span_singleton_eq_span_singleton.mp hfg)

end IsStrictNormalCrossingsEquation

variable (X : Scheme.{u}) [IsIntegral X]

/-- Original regular equations for the same Cartier divisor have associated
germs at every point of their actual overlap. -/
theorem RegularCartierEquationChart.associated_germ (D : CartierDivisor X)
    (c d : RegularCartierEquationChart X D) (x : X)
    (hxc : x ∈ c.chart.openSet) (hxd : x ∈ d.chart.openSet) :
    Associated (X.presheaf.germ c.chart.openSet x hxc c.coefficient)
      (X.presheaf.germ d.chart.openSet x hxd d.coefficient) := by
  let V : X.Opens := c.chart.openSet ⊓ d.chart.openSet
  have hxV : x ∈ V := ⟨hxc, hxd⟩
  letI : Nonempty V := ⟨⟨x, hxV⟩⟩
  let c' := RegularCartierEquationChart.restrict X D c V inf_le_left
  let d' := RegularCartierEquationChart.restrict X D d V inf_le_right
  have hspan : Ideal.span ({c'.coefficient} : Set Γ(X, V)) =
      Ideal.span ({d'.coefficient} : Set Γ(X, V)) :=
    (cartierSectionIdeal_eq_span X D c').symm.trans
      (cartierSectionIdeal_eq_span X D d')
  have h := Associated.map (X.presheaf.germ V x hxV).hom
    (Ideal.span_singleton_eq_span_singleton.mp hspan)
  change Associated
    (X.presheaf.germ V x hxV
      (X.presheaf.map (homOfLE (inf_le_left : V ≤ c.chart.openSet)).op c.coefficient))
    (X.presheaf.germ V x hxV
      (X.presheaf.map (homOfLE (inf_le_right : V ≤ d.chart.openSet)).op d.coefficient)) at h
  rw [X.presheaf.germ_res_apply, X.presheaf.germ_res_apply] at h
  exact h

/-- One genuine regular equation with an SNC germ at each original point
suffices for the global, all-equation-charts SNC predicate. -/
theorem isStrictNormalCrossingsCartier_of_local_equations [IsLocallyNoetherian X]
    (D : CartierDivisor X)
    (h : ∀ x : X, ∃ (c : RegularCartierEquationChart X D)
      (hx : x ∈ c.chart.openSet), IsStrictNormalCrossingsEquation (X.presheaf.stalk x)
        (X.presheaf.germ c.chart.openSet x hx c.coefficient)) :
    IsStrictNormalCrossingsCartier X D := by
  refine ⟨?_, ?_⟩
  · intro x
    obtain ⟨c, hx, _⟩ := h x
    exact ⟨c, hx⟩
  · intro c x hxc
    obtain ⟨d, hxd, hd⟩ := h x
    exact hd.of_associated (RegularCartierEquationChart.associated_germ X D d c x hxd hxc)

end KltDP.Geometry

#print axioms KltDP.Geometry.isStrictNormalCrossingsCartier_of_local_equations
